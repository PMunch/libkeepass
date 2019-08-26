proc rotl(value: uint32, shift: int): uint32 {.inline.} =
  return (value shl shift) or (value shr (32 - shift))

proc quarterRound(y0, y1, y2, y3: var uint32) =
  y1 = y1 xor rotl(y0 + y3, 7)
  y2 = y2 xor rotl(y1 + y0, 9)
  y3 = y3 xor rotl(y2 + y1, 13)
  y0 = y0 xor rotl(y3 + y2, 18)

template rowRound(y: var array[16, uint32]) =
  quarterRound(y[0], y[1], y[2], y[3])
  quarterRound(y[5], y[6], y[7], y[4])
  quarterRound(y[10], y[11], y[8], y[9])
  quarterRound(y[15], y[12], y[13], y[14])

template columnRound(x: var array[16, uint32]) =
  quarterRound(x[0], x[4], x[8], x[12])
  quarterRound(x[5], x[9], x[13], x[1])
  quarterRound(x[10], x[14], x[2], x[6])
  quarterRound(x[15], x[3], x[7], x[11])

template doubleRound(x: var array[16, uint32]) =
  columnRound(x)
  rowRound(x)

proc littleEndian[T](b: T, o: int): uint32 {.inline.} =
  return b[o+0].uint32 + b[o+1].uint32 shl 8 + b[o+2].uint32 shl 16 + b[o+3].uint32 shl 24

template revLittleEndian[T](b: var T, o: int, w: uint32) =
  b[o+0] = (w and 0xff).uint8
  b[o+1] = (w shr 8 and 0xff).uint8
  b[o+2] = (w shr 16 and 0xff).uint8
  b[o+3] = (w shr 24 and 0xff).uint8

proc hash(s: var array[64, uint8]) =
  var
    x: array[16, uint32]
    z: array[16, uint32]

  for i in 0..<16:
    x[i] = littleEndian(s, 4*i)
    z[i] = x[i]

  for i in 0..<10:
    doubleRound(z)

  for i in 0..<16:
    z[i] += x[i]
    revLittleEndian(s, 4*i, z[i])

converter charToUint8(i: char): uint8 = i.uint8

proc expand(k: array[16, uint8], n: array[16, uint8], keystream: var array[64, uint8]) =
  let t = [
    ['e', 'x', 'p', 'a'],
    ['n', 'd', ' ', '1'],
    ['6', '-', 'b', 'y'],
    ['t', 'e', ' ', 'k']
  ]

  for i in countup(0, 64, step = 20):
    for j in 0..<4:
      keystream[i + j] = t[i.`div` 20][j]

  for i in 0..<16:
    keystream[4+i] =  k[i]
    keystream[44+i] = k[i]
    keystream[24+i] = n[i]

  hash(keystream)

proc expand(k: array[32, uint8], n: array[16, uint8], keystream: var array[64, uint8]) =
  let o = [
    ['e', 'x', 'p', 'a'],
    ['n', 'd', ' ', '3'],
    ['2', '-', 'b', 'y'],
    ['t', 'e', ' ', 'k']
  ]

  for i in countup(0, 64, step = 20):
    for j in 0..<4:
      keystream[i + j] = o[i.`div` 20][j]

  for i in 0..<16:
    keystream[4+i] =  k[i]
    keystream[44+i] = k[i+16]
    keystream[24+i] = n[i]

  hash(keystream)

proc crypt*[T](key: T, nonce: array[8, uint8], si: uint32, buf: var seq[uint8]) =
  var
    keystream: array[64, uint8]
    n: array[16, uint8]

  for i in 0..<8:
    n[i] = nonce[i]

  if si mod 64 != 0:
    revLittleEndian(n, 8, si.`div` 64)
    expand(key, n, keystream)

  for i in 0..<buf.len:
    if (si + i.uint32) mod 64 == 0:
      revLittleEndian(n, 8, (si + i.uint32).`div` 64)
      expand(key, n, keystream)

    buf[i] = buf[i] xor keystream[((si + i.uint32) mod 64).int]

when isMainModule:
  import strutils

  proc `$`(buf: seq[uint8]): string =
    result = ""
    for b in buf:
      result &= b.toHex
    result &= "\n"
    for b in buf:
      result &= b.chr

  var buf = @[0x68'u8, 0x65, 0x6c, 0x6c, 0x6f, 0x20, 0x77, 0x6f, 0x72, 0x6c, 0x64]
  echo buf

  let
    key = [0x7C'u8,0x46,0x07,0x5C,0xB4,0xB3,0xDA,0xC8,0xED,0x97,0x95,0x0B,0x56,0xCA,0x4F,0xBA,0xE1,0x0A,0xB8,0x10,0xD7,0x88,0xFA,0x5D,0x8E,0xE8,0xD7,0x4D,0x5B,0xAD,0x8E,0x0E]
    nonce = [0xE8'u8,0x30,0x09,0x4B,0x97,0x20,0x5D,0x2A]

  # Encrypt
  crypt(key, nonce, 0, buf)
  echo buf
  # Decrypt
  crypt(key, nonce, 0, buf)
  echo buf
