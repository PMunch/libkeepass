import streams, strutils, sequtils, base64, xmltree, xmlparser, tables
import nimcrypto / [hash, sha2, hmac, bcmode, rijndael]
import chacha20
import zip/zlib
import "libkeepass/salsa"

proc newEIO(msg: string): ref IOError =
  new(result)
  result.msg = msg

proc read[T](s: Stream, result: var T) =
  if readData(s, addr(result), sizeof(T)) != sizeof(T):
    raise newEIO("Cannot read from stream")

proc readUint8(s: Stream): uint8 =
  read(s, result)

proc readUint16(s: Stream): uint16 =
  read(s, result)

proc readUint32(s: Stream): uint32 =
  read(s, result)

proc readUint64(s: Stream): uint64 =
  read(s, result)

type DecryptionException* = object of CatchableError

template error(s: untyped): untyped =
  raise newException(DecryptionException, s)

const
  magic = 0x03_D9_A2_9A'u32
  version = 0x67_FB_4B_B5'u32
  cipherid256Aes = [0x31'u8,0xc1,0xf2,0xe6,0xbf,0x71,0x43,0x50,0xbe,0x58,0x05,0x21,0x6a,0xfc,0x5a,0xff]
  kdfAesKdbx3 = [0xc9'u8, 0xd9, 0xf3, 0x9a, 0x62, 0x8a, 0x44, 0x60, 0xbf, 0x74, 0x0d, 0x08, 0xc1, 0x8a, 0x4f, 0xea]

type
  DynamicHeaderType {.pure.} = enum
    END = (0,"END"),
    COMMENT = (1,"COMMENT"),
    CIPHERID = (2, "CIPHERID"),
    COMPRESSIONFLAGS = (3, "COMPRESSIONFLAGS"),
    MASTERSEED = (4, "MASTERSEED"),
    TRANSFORMSEED = (5, "TRANSFORMSEED"),
    TRANSFORMROUNDS = (6, "TRANSFORMROUNDS"),
    ENCRYPTIONIV = (7, "ENCRYPTIONIV"),
    PROTECTEDSTREAMKEY = (8, "PROTECTEDSTREAMKEY"),
    STREAMSTARTBYTES = (9, "STREAMSTARTBYTES"),
    INNERRANDOMSTREAMID = (10, "INNERRANDOMSTREAMID"),
    KDFPARAMETERS = (11, "KDFPARAMETERS")
  CompressionMethod {.pure.} = enum
    None = (0, "None"),
    Gzip = (1, "Gzip")
  EncryptionType {.pure.} = enum
    None = (0, "None"),
    Arc4Variant = (1, "Arc4Variant"),
    Salsa20 = (2, "Salsa20")
    ChaCha20 = (3, "ChaCha20")
  VariantValueKind {.pure.} = enum
    End = 0x00, Uint32 = 0x04, Uint64 = 0x05, Bool = 0x08, Int32 = 0x0C, Int64 = 0x0D, String = 0x18, Bytes = 0x42
  VariantValue = object
    case kind: VariantValueKind
    of VariantValueKind.End: discard
    of Uint32: u32: uint32
    of Uint64: u64: uint64
    of Bool: bo: bool
    of Int32: i32: int32
    of Int64: i64: int64
    of String: s: string
    of Bytes: bs: seq[byte]
  DynamicHeader = object
    compression: CompressionMethod
    innerEncryption: EncryptionType
    masterseed: string
    transformseed: string
    transformrounds: uint64
    encryptionIV: string
    protectedStreamKey: string
    streamStartBytes: string
    encrypted: string
    kdfParameters: Table[string, VariantValue]
  HeaderBytes = string
  SalsaStream = object
    iv: array[8, byte]
    key: array[32, byte]
    pos: uint32
  ChaChaStream = object
    nonce: array[12, byte]
    key: array[32, byte]
    pos: uint32
  CryptoStreamKind = enum Salsa, ChaCha
  CryptoStream = object
    case kind: CryptoStreamKind
    of Salsa: salsa: SalsaStream
    of ChaCha: chacha: ChaChaStream

proc readBytes(s: Stream, count: int): seq[byte] =
  result.setLen(count)
  if s.readData(result[0].addr, count) != count:
    raise newException(ValueError, "Unable to read enough bytes for value")

proc add(header: var HeaderBytes, d: uint8) =
  header.add d.chr

proc add(header: var HeaderBytes, d: uint16) =
  header.add (0xFF'u16 and d).uint8
  header.add (0xFF'u16 and (d shr 8)).uint8

proc add(header: var HeaderBytes, d: uint32) =
  header.add (0xFF'u32 and d).uint8
  header.add (0xFF'u32 and (d shr 8)).uint8
  header.add (0xFF'u32 and (d shr 16)).uint8
  header.add (0xFF'u32 and (d shr 24)).uint8

proc add(header: var HeaderBytes, d: uint64) =
  header.add (0xFF'u64 and d).uint8
  header.add (0xFF'u64 and (d shr 8)).uint8
  header.add (0xFF'u64 and (d shr 16)).uint8
  header.add (0xFF'u64 and (d shr 24)).uint8
  header.add (0xFF'u64 and (d shr 32)).uint8
  header.add (0xFF'u64 and (d shr 40)).uint8
  header.add (0xFF'u64 and (d shr 48)).uint8
  header.add (0xFF'u64 and (d shr 56)).uint8

proc add(header: var HeaderBytes, d: string) =
  for b in d:
    header.add b.uint8

proc computeHeaderHmac(master: MDigest[512], data: string): MDigest[256] =
  var key: sha512
  key.init()
  key.update(cast[array[8, byte]](uint64.high))
  key.update(master.data)
  result = sha256.hmac(key.finish.data, data)

proc computeBlockHmac(master: MDigest[512], index: uint64, data: seq[byte]): MDigest[256] =
  var key: sha512
  key.init()
  key.update(cast[array[8, byte]](index))
  key.update(master.data)
  var hmac: Hmac[sha256]
  hmac.init(key.finish.data)
  hmac.update(cast[array[8, byte]](index))
  hmac.update(cast[array[4, byte]](data.len.uint32))
  hmac.update(data)
  result = hmac.finish()

proc decrypt(cryptoStream: var CryptoStream, data: var seq[uint8]) =
  case cryptoStream.kind:
  of Salsa:
    crypt(cryptoStream.salsa.key, cryptoStream.salsa.iv, cryptoStream.salsa.pos, data)
    cryptoStream.salsa.pos += data.len.uint32
  of ChaCha:
    cryptoStream.chacha.pos += chacha20(cryptoStream.chacha.key, cryptoStream.chacha.nonce, cryptoStream.chacha.pos, data, data)

proc cryptoStream(header: DynamicHeader): CryptoStream =
  case header.innerEncryption:
  of Salsa20:
    result = CryptoStream(kind: Salsa, salsa:
      SalsaStream(key: sha256.digest(header.protectedStreamKey).data,
                  iv: [0xE8'u8,0x30,0x09,0x4B,0x97,0x20,0x5D,0x2A],
                  pos: 0))
  of ChaCha20:
    let keynonce = sha512.digest(header.protectedStreamKey).data
    result = CryptoStream(kind: ChaCha, chacha:
      ChaChaStream(pos: 0))
    copyMem(result.chacha.key.addr, keynonce[0].unsafeAddr, 32)
    copyMem(result.chacha.nonce.addr, keynonce[32].unsafeAddr, 12)
  else: error "Unable to decrypt passwords using " & $header.innerEncryption

proc parseEntry(entry: XmlNode, cryptoStream: var CryptoStream) =
  if entry.tag == "Entry":
    for field in entry:
      case field.tag:
      of "String":
        let
          keyTag = field.child("Key")
          valueTag = field.child("Value")
          key = keyTag.innerText
          value = valueTag.innerText
        case key:
          of "Password":
            let pwData = value.decode
            var pwBytes = newSeq[uint8](pwData.len)
            for i in 0..<pwBytes.len:
              pwBytes[i] = pwData[i].uint8
            cryptoStream.decrypt(pwBytes)
            var pwString = newStringOfCap(pwBytes.len)
            for i in 0..<pwBytes.len:
              pwString.add pwBytes[i].char
            if valueTag.len != 0:
              valueTag[0].text = xmltree.escape(pwString)
      of "History":
        for innerEntry in field:
          parseEntry(innerEntry, cryptoStream)

proc parseGroup(group: XmlNode, cryptoStream: var CryptoStream) =
  if group.tag == "Group":
    for entry in group:
      if entry.tag == "Entry":
        parseEntry(entry, cryptoStream)
      elif entry.tag == "Group":
        parseGroup(entry, cryptoStream)

proc parseBody(xmlstring: Stream, headerData: string, dynamicHeader: DynamicHeader, cryptoStream: var CryptoStream): seq[XmlNode] =
  let
    xml = parseXml(xmlstring)
    meta = xml.child("Meta")
    root = xml.child("Root")
  for tag in meta:
    if tag.tag == "HeaderHash":
      # Switch to a less dumb way of comparing
      if sha256.digest(headerData).data.mapIt(chr(it)).join("") != tag.innerText.decode:
        error "Header hash not matching"
  for group in root:
    parseGroup(group, cryptoStream)
  result.add(xml)

proc readDatabase*(s: Stream, password: string): seq[XmlNode] =
  result = @[]
  var
    dynamicHeader: DynamicHeader
    headerData: HeaderBytes = ""
  let
    m = s.readUint32
    v = s.readUint32
  if not m == magic:
    error "Magic number not matching!"
  if not v == version:
    error "Version number not matching!"
  let
    minor = s.readUint16
    major = s.readUint16
  if (major != 3 or minor != 1) and (major != 4 or minor notin {0, 1}):
    error "Only version 3.1, 4.0, and 4.1 databases supported"
  headerData.add m
  headerData.add v
  headerData.add minor
  headerData.add major
  var bId = s.readUint8.DynamicHeaderType
  while true:
    var
      size = if major == 3: s.readUint16.int else: s.readUint32.int
      data: seq[uint8]
      dword: uint32
      qword: uint64
      str: string
    headerData.add bId.uint8
    if major == 3:
      headerData.add size.uint16
    else:
      headerData.add size.uint32
    # Read data
    case bId:
      of CIPHERID:
        data = newSeq[uint8](size)
        for i in 0..<size:
          data[i] = s.readUint8
          headerData.add data[i]
      of COMPRESSIONFLAGS:
        dword = s.readUint32
        headerData.add dword
      of INNERRANDOMSTREAMID:
        dword = s.readUint32
        headerData.add dword
      of MASTERSEED:
        if not size == 32:
          error "MASTERSEED not 32 bytes!"
        str = s.readStr(32)
        headerData.add str
      of TRANSFORMROUNDS:
        qword = s.readUint64
        headerData.add qword
      of ENCRYPTIONIV, PROTECTEDSTREAMKEY, STREAMSTARTBYTES, TRANSFORMSEED, KDFPARAMETERS:
        str = s.readStr(size)
        headerData.add str
      else:
        # Discard unknown headers
        for i in 0..<size:
          headerData.add s.readUint8
    # Handle data
    case bId:
      of CIPHERID:
        for i in 0..<size:
          if not data[i] == cipherid256Aes[i]:
            error "Only AES256 outer encryption supported"
      of COMPRESSIONFLAGS:
        dynamicHeader.compression = dword.CompressionMethod
      of INNERRANDOMSTREAMID:
        dynamicHeader.innerEncryption = dword.EncryptionType
      of MASTERSEED:
        dynamicHeader.masterseed = str
      of TRANSFORMSEED:
        dynamicHeader.transformseed = str
      of TRANSFORMROUNDS:
        dynamicHeader.transformrounds = qword
      of ENCRYPTIONIV:
        dynamicHeader.encryptionIV = str
      of PROTECTEDSTREAMKEY:
        dynamicHeader.protectedStreamKey = str
      of STREAMSTARTBYTES:
        dynamicHeader.streamStartBytes = str
      of KDFPARAMETERS:
        var kpStream = newStringStream(str)
        if kpStream.readUint16 != 0x0100: error "Only version 1.0 of VariantDictionaries supported for KdfParameters"
        while (var kind = kpStream.readUint8.VariantValueKind; kind != VariantValueKind.End):
          let
            keyLength = kpStream.readUint32.int
            key = kpStream.readStr(keyLength)
            valLength = kpStream.readUint32.int
          var value = VariantValue(kind: kind)
          case kind:
          of VariantValueKind.End: discard
          of Uint32: value.u32 = kpStream.readUint32
          of Uint64: value.u64 = kpStream.readUint64
          of Bool: value.bo = kpStream.readBool
          of Int32: value.i32 = kpStream.readInt32
          of Int64: value.i64 = kpStream.readInt64
          of String: value.s = kpStream.readStr(valLength)
          of Bytes: value.bs = kpStream.readBytes(valLength)
          if key == "$UUID" and value.bs != kdfAesKdbx3:
            error "Only AES KDBX3 key derivation function supported"
          dynamicHeader.kdfParameters[key] = value
      else:
        discard
    if bId == DynamicHeaderType.END:
      break
    bId = s.readUint8.DynamicHeaderType
  let compKey = sha256.digest(sha256.digest(password).data)
  var aesEcb: ECB[aes256]
  if dynamicHeader.transformseed.len < aesEcb.sizeKey():
    if not dynamicHeader.kdfParameters.hasKey("S"):
      error "Could not set AES encode key"
    else:
      aesEcb.init(dynamicHeader.kdfParameters["S"].bs)
  else:
    aesEcb.init(dynamicHeader.transformseed)
  var transformedKey = compKey
  if dynamicHeader.transformrounds == 0:
    if not dynamicHeader.kdfParameters.hasKey("R"):
      error "Could not set key derivation transformation rounds"
    else:
      dynamicHeader.transformrounds = dynamicHeader.kdfParameters["R"].u64
  for i in 0..<dynamicHeader.transformrounds.int:
    aesEcb.encrypt(transformedKey.data.toOpenArray(0, 15), transformedKey.data.toOpenArray(0, 15))
    aesEcb.encrypt(transformedKey.data.toOpenArray(16, 31), transformedKey.data.toOpenArray(16, 31))
  transformedKey = sha256.digest(transformedKey.data)

  var masterKeyHash: sha256
  masterKeyHash.init()
  masterKeyHash.update(dynamicHeader.masterseed)
  masterKeyHash.update(transformedKey.data)
  var aesCbc: CBC[aes256]
  aesCbc.init(masterKeyHash.finish().data, dynamicHeader.encryptionIV.toOpenArrayByte(0, dynamicHeader.encryptionIV.high))

  if major == 4:
    if s.readBytes(sizeof(MDigest[256])) != sha256.digest(headerData).data:
      error "SHA256 hash of header doesn't match"
    let hmac = s.readBytes(sizeof(MDigest[256]))
    var hmacKey: sha512
    hmacKey.init()
    hmacKey.update(dynamicHeader.masterSeed)
    hmacKey.update(transformedKey.data)
    hmacKey.update("\x01")
    let hmacKeyDigest = hmacKey.finish
    let computedHmac = hmacKeyDigest.computeHeaderHmac(headerData)
    if hmac != computedHmac.data:
      error "HMAC-SHA256 hash of header doesn't match"
    for i in 0..int.high:
      let
        blockHash = s.readBytes(32)
        blockLen = s.readUint32()
      if blockLen == 0: break
      var blockData = s.readBytes(blockLen.int)
      if blockHash != hmacKeyDigest.computeBlockHmac(i.uint64, blockData).data:
        error "HMAC-SHA256 hash of block " & $i & " doesn't match"
      if blockData.len mod 16 != 0:
        let pad = 16-(blockData.len-`div`(blockData.len, 16)*16)
        blockData &= cast[byte](pad).repeat(pad)
      var decrypted = newSeq[byte](blockData.len)
      aesCbc.decrypt(blockData, decrypted)
      decrypted.setLen(decrypted.len - decrypted[decrypted.high].int)
      let ss = newStringStream(case dynamicHeader.compression:
        of CompressionMethod.None: cast[string](decrypted)
        of Gzip: uncompress(cast[string](decrypted), GZIP_STREAM))
      while (var itemType = ss.readChar.byte; itemType != 0x00):
        let length = ss.readUint32
        case itemType:
        of 0x01:
          dynamicHeader.innerEncryption = ss.readUint32.EncryptionType
        of 0x02:
          dynamicHeader.protectedStreamKey = cast[string](ss.readBytes(length.int))
        else:
          echo itemType
          echo ss.readBytes(length.int)
      discard ss.readUint32 # The length of the null end block
      var cryptoStream = dynamicHeader.cryptoStream
      result &= parseBody(ss, headerData, dynamicHeader, cryptoStream)
  else:
    dynamicHeader.encrypted = s.readAll
    if dynamicHeader.encrypted.len mod 16 != 0:
      let pad = 16-(dynamicHeader.encrypted.len-`div`(dynamicHeader.encrypted.len, 16)*16)
      dynamicHeader.encrypted &= cast[char](pad).repeat(pad)
    var decrypted = newString(dynamicHeader.encrypted.len)
    aesCbc.decrypt(dynamicHeader.encrypted, decrypted)
    if not decrypted.startsWith(dynamicHeader.streamStartBytes):
      error "Bad decryption"
    var ss = newStringStream(decrypted)
    ss.setPosition(dynamicHeader.streamStartBytes.len)
    var cryptoStream = dynamicHeader.cryptoStream
    while true:
      let
        blockId = ss.readUint32
        hash = ss.readBytes(32)
        blockSize = ss.readUint32
        data = $ss.readStr(blockSize.int)
      # Check for end condition
      if blockSize == 0 and hash == default(array[32, byte]):
        break
      if hash != sha256.digest(data).data:
        error "Hash not matching for block " & $blockId
      else:
        let xmlstring = newStringStream(case dynamicHeader.compression:
          of CompressionMethod.None: data
          of Gzip: uncompress(data, blockSize, GZIP_STREAM))
        result &= parseBody(xmlstring, headerData, dynamicHeader, cryptoStream)

when isMainModule:
  # Example of how to use the above module
  import os
  if commandLineParams().len < 2:
    stderr.write "Incorrect amount of arguments. Usage: keepass <kdbx file> <password>\n"
    quit 1
  let
    s = newFileStream(commandLineParams()[0], fmRead)
    db = readDatabase(s, commandLineParams()[1])
  for xml in db:
    for group in xml.child("Root"):
      proc parseGroup(group: XmlNode, path: string) =
        let name =
          if group.child("Name") == nil:
            ""
          else:
            if group.child("Name").innerText != "Root":
              group.child("Name").innerText & "  "
            else:
              ""
        if group.tag == "Group":
          for entry in group:
            proc parseEntry(entry: XmlNode) =
              if entry.tag == "Entry":
                var title, password: string
                for field in entry:
                  case field.tag:
                  of "String":
                    let
                      keyTag = field.child("Key")
                      valueTag = field.child("Value")
                      key = keyTag.innerText
                      value = valueTag.innerText
                    case key:
                      of "Title":
                        title = path & name & value
                      of "Password":
                        password = value
                echo title & ": " & password.multiReplace(
                  ("&lt;", "<"),
                  ("&gt;", ">"),
                  ("&amp;", "&"),
                  ("&quot;", "\""),
                  ("&#x27;", "'"),
                  ("&#x2F;", "/"))
            if entry.tag == "Entry":
              parseEntry(entry)
            elif entry.tag == "Group":
              parseGroup(entry, path & name)
      parseGroup(group, "")
