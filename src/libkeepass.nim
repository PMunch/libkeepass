import streams, strutils, endians, times, sequtils
import nimSHA2, nimAES
import zip/zlib
import base64
import xmltree, xmlparser
import tables
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

type DecryptionException* = object of Exception

template error(s: untyped): untyped =
  raise newException(DecryptionException, s)

const
  magic = 0x03_D9_A2_9A'u32
  version = 0x67_FB_4B_B5'u32
  cipherid = [0x31'u8,0xc1,0xf2,0xe6,0xbf,0x71,0x43,0x50,0xbe,0x58,0x05,0x21,0x6a,0xfc,0x5a,0xff]

type
  DynamicHeaderType = enum
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
    INNERRANDOMSTREAMID = (10, "INNERRANDOMSTREAMID")
  CompressionMethod {.pure.} = enum
    None = (0, "None"),
    Gzip = (1, "Gzip")
  EncryptionType {.pure.} = enum
    None = (0, "None"),
    Arc4Variant = (1, "Arc4Variant"),
    Salsa20 = (2, "Salsa20")
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
  HeaderBytes = string
  Entry = ref object
    title: string
    username: string
    password: string
    url: string
    notes: string

proc add(header: var HeaderBytes, d: uint8) =
  header.add d.chr

proc add(header: var HeaderBytes, d: uint16) =
  header.add d.uint8
  header.add((d shr 8).uint8)

proc add(header: var HeaderBytes, d: uint32) =
  header.add d.uint8
  header.add((d shr 8).uint8)
  header.add((d shr 16).uint8)
  header.add((d shr 24).uint8)

proc add(header: var HeaderBytes, d: uint64) =
  header.add d.uint8
  header.add((d shr 8).uint8)
  header.add((d shr 16).uint8)
  header.add((d shr 24).uint8)
  header.add((d shr 32).uint8)
  header.add((d shr 40).uint8)
  header.add((d shr 48).uint8)
  header.add((d shr 56).uint8)

proc add(header: var HeaderBytes, d: string) =
  for b in d:
    header.add b.uint8

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
  headerData.add m
  headerData.add v
  headerData.add minor
  headerData.add major
  var bId = s.readUint8.DynamicHeaderType
  while true:
    var
      size = s.readUint16.int
      data: seq[uint8]
      dword: uint32
      qword: uint64
      str: string
    headerData.add bId.uint8
    headerData.add size.uint16
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
      of ENCRYPTIONIV, PROTECTEDSTREAMKEY, STREAMSTARTBYTES, TRANSFORMSEED:
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
          if not data[i] == cipherid[i]:
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
      else:
        discard
    if bId == END:
      break
    bId = s.readUint8.DynamicHeaderType
  dynamicHeader.encrypted = s.readAll
  let compKey = $computeSha256($computeSha256(password))
  var aes = initAES()
  if not aes.setEncodeKey(dynamicHeader.transformseed):
    error "Could not set AES encode key"
  var transformedKey = compKey
  # This is the slow part. A faster implementation of encryptECB should speed this up
  for i in 0..<dynamicHeader.transformrounds.int:
    let oldKey = transformedKey
    transformedKey = aes.encryptECB(oldKey[0..15]) & aes.encryptECB(oldKey[16..31])
  transformedKey = $computeSha256(transformedKey)
  let masterKey = $computeSha256(dynamicHeader.masterseed & $transformedKey)
  aes = initAes()
  if not aes.setDecodeKey(masterKey):
    error "Could not set AES decode key"
  if dynamicHeader.encrypted.len mod 16 != 0:
    let pad = 16-(dynamicHeader.encrypted.len-`div`(dynamicHeader.encrypted.len, 16)*16)
    dynamicHeader.encrypted &= cast[char](pad).repeat(pad)
  let decrypted = aes.decryptCBC(dynamicHeader.encryptionIV, dynamicHeader.encrypted)
  if not decrypted.startsWith(dynamicHeader.streamStartBytes):
    error "Bad decryption"
  var ss = newStringStream(decrypted)
  ss.setPosition(dynamicHeader.streamStartBytes.len)
  let
    keyArr = cast[ptr array[32, uint8]](($computeSha256($dynamicHeader.protectedStreamKey)).cstring)
  var
    iv = [0xE8'u8,0x30,0x09,0x4B,0x97,0x20,0x5D,0x2A]
    pos = 0'u32
  while true:
    let
      blockId = ss.readUint32
      hash = ss.readStr(32)
      blockSize = ss.readUint32
      data = $ss.readStr(blockSize.int)
    # Check for end condition
    if blockSize == 0 and hash == '\0'.repeat(32):
      break
    if $hash != $computeSha256(data):
      error "Hash not matching for block " & $blockId
    else:
      let
        xmlstring = uncompress(data, blockSize, GZIP_STREAM)
        xml = parseXml(xmlstring.newStringStream)
        meta = xml.child("Meta")
        root = xml.child("Root")
      for tag in meta:
        if tag.tag == "HeaderHash":
          if $computeSha256(headerData) != tag.innerText.decode:
            error "Header hash not matching"
      for group in root:
        proc parseGroup(group: XmlNode) =
          if group.tag == "Group":
            for entry in group:
              proc parseEntry(entry: XmlNode) =
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
                          crypt(keyArr[], iv, pos, pwBytes)
                          pos += pwBytes.len.uint32
                          var pwString = newStringOfCap(pwBytes.len)
                          for i in 0..<pwBytes.len:
                            pwString.add pwBytes[i].char
                          if valueTag.len != 0:
                            valueTag[0].text = xmltree.escape(pwString)
                    of "History":
                      for innerEntry in field:
                        parseEntry(innerEntry)
              if entry.tag == "Entry":
                parseEntry(entry)
              elif entry.tag == "Group":
                parseGroup(entry)
        parseGroup(group)
      result.add(xml)

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
      var path = ""
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
