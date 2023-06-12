#!/usr/bin/env sage
# -*- coding: utf-8 -*-

# Implement the Simplified AES algorithm as described in Stalling's
# book and the specification as given in the class materials on the
# Moodle server. You also find a walk-through of an encryption and a
# decryption operation in the class materials.
from past.builtins import xrange


def xor(a, b):
    def h(x, y):
        if (x == y):
            return (0)
        else:
            return (1)

    return (list(map(lambda x, y: h(x, y), a, b)))


def int2blist(n, length):
    b = bin(n)
    l = string2blist(b[2:])
    return ([0] * (length - len(l)) + l)


def string2blist(s):
    return (list(map(int, list(s))))


def pp(b):
    """Pretty print bit lists"""
    t = "".join(map(str, b))
    r = ""
    for i in range(0, len(t), 4):
        r += t[i:i + 4] + ' '
    return (r)


# Since the mix column operations are tricky, the following
# implementations are provided for your convenience.

def mix_col(d, inv=False):
    L.< a >= GF(2 ^ 4);
    V = VectorSpace(GF(2), 8)
    if inv:
        MixColumns_matrix = Matrix(L, [[a ^ 3 + 1, a], [a, a ^ 3 + 1]])
    else:
        MixColumns_matrix = Matrix(L, [[1, a ^ 2], [a ^ 2, 1]])
    d0 = d[0:4]
    d0.reverse()
    d1 = d[4:8]
    d1.reverse()
    d2 = d[8:12]
    d2.reverse()
    d3 = d[12:16]
    d3.reverse()
    dMatrix = Matrix(L, [[d0, d2],
                         [d1, d3]])
    matrixProduct = MixColumns_matrix * dMatrix
    r = []
    for j in range(2):
        for i in range(2):
            r += int2blist(int(matrixProduct[i][j]._int_repr()), 4)
    return (r)


def inv_mix_col(d):
    return (mix_col(d=d, inv=True))


###################### First SBOX Func For Encryption
def subBox(nibble, encrypt):
    L = GF(2 ^ 4)
    V = VectorSpace(GF(2), 4)
    m = Matrix(L, [[1, 0, 1, 1], [1, 1, 0, 1], [1, 1, 1, 0], [0, 1, 1, 1]])
    a = V([1, 0, 0, 1])
    for b0 in xrange(0, 2):
        for b1 in xrange(0, 2):
            for b2 in xrange(0, 2):
                for b3 in xrange(0, 2):
                    sbox_in = [b0, b1, b2, b3]
                    # [0,0,0,0] is a special case.
                    if sbox_in == [0, 0, 0, 0]:
                        sbox_out = [1, 0, 0, 1]
                    else:
                        b = V(int2blist((~L([b3, b2, b1, b0])).integer_representation(), 4))
                        sbox_out = list(m * (b) + a)
                    # encryption
                    if nibble == sbox_in:
                        return sbox_out

# for Decrypt for Decryption
def subBoxDecrypt(nibble, encrypt):
    L = GF(2 ^ 4)
    V = VectorSpace(GF(2), 4)
    m = Matrix(L, [[1, 0, 1, 1], [1, 1, 0, 1], [1, 1, 1, 0], [0, 1, 1, 1]])
    a = V([1, 0, 0, 1])
    for b0 in xrange(0, 2):
        for b1 in xrange(0, 2):
            for b2 in xrange(0, 2):
                for b3 in xrange(0, 2):
                    sbox_in = [b0, b1, b2, b3]
                    # [0,0,0,0] is a special case.
                    if sbox_in == [0, 0, 0, 0]:
                        sbox_out = [1, 0, 0, 1]
                    else:
                        b = V(int2blist((~L([b3, b2, b1, b0])).integer_representation(), 4))
                        sbox_out = list(m * (b) + a)
                    # decryption
                    if nibble == sbox_out:
                        return sbox_in
##############################################################

# same for both enc dyc
# used to generate sub keys
def keyGeneration(keyList):
    keys = [None] * 3
    w0 = keyList[0:8]
    w1 = [keyList[8], keyList[9], keyList[10], keyList[11], keyList[12], keyList[13], keyList[14], keyList[15]]
    # w2 = w0 XOR 10000000 XOR SubNib(RotNib(w1))
    w2 = xor(xor(w0, string2blist("10000000")), subNibbles(rotateNibble(w1), True))
    w3 = xor(w2, w1)
    # w4 = w2 XOR 00110000 XOR SubNib(RotNib(w3))
    w4 = xor(xor(w2, string2blist("00110000")), subNibbles(rotateNibble(w3), True))
    w5 = xor(w4, w3)

    # creation of subkeys
    keys[0] = w0 + w1
    keys[1] = w2 + w3
    keys[2] = w4 + w5
    return keys

# for encry
def subNibbles(byte, encrypt):
    boxLeft = [byte[0], byte[1], byte[2], byte[3]]
    boxRigt = [byte[4], byte[5], byte[6], byte[7]]

    substitutedLeft = subBox(boxLeft, encrypt)
    substitutedRigt = subBox(boxRigt, encrypt)
    return substitutedLeft + substitutedRigt

# for dcrypt
def subNibblesFrDecrypt(byte, encrypt):
    boxLeft = [byte[0], byte[1], byte[2], byte[3]]
    boxRigt = [byte[4], byte[5], byte[6], byte[7]]

    substitutedLeft = subBoxDecrypt(boxLeft, encrypt)
    substitutedRigt = subBoxDecrypt(boxRigt, encrypt)
    return substitutedLeft + substitutedRigt

# for dcrypt
def substituteNibblesFrDecrypt(addedKey, encrypt):
    substitutedleftByte = subNibblesFrDecrypt(
        [addedKey[0], addedKey[1], addedKey[2], addedKey[3], addedKey[4], addedKey[5], addedKey[6], addedKey[7]],
        encrypt)
    substitutedRghtByte = subNibblesFrDecrypt(
        [addedKey[8], addedKey[9], addedKey[10], addedKey[11], addedKey[12], addedKey[13], addedKey[14], addedKey[15]],
        encrypt)
    afterSubstition = substitutedleftByte + substitutedRghtByte
    return afterSubstition


def rotateNibble(inByte):
    return [inByte[4], inByte[5], inByte[6], inByte[7], inByte[0], inByte[1], inByte[2], inByte[3]]


# 2 Points
def saes_decrypt(ciphertext, key):
    subKeys = keyGeneration(key)
    addedKey = addRoundKey(ciphertext, subKeys[2])
    afterShifting = shifting(addedKey)

    afterSubstition = substituteNibblesFrDecrypt(afterShifting, False)

    addedKey = addRoundKey(afterSubstition, subKeys[1])
    afterInv = inv_mix_col(addedKey)
    afterShifting = shifting(afterInv)
    afterSubstition = substituteNibblesFrDecrypt(afterShifting, False)
    addedKey = addRoundKey(afterSubstition, subKeys[0])

    return addedKey


# Encryption
def saes_encrypt(plaintext, key):
    # first Round of encryption
    # adding both plainText and Key
    addedKey = addRoundKey(plaintext, key)
    # substitution of nibbles
    afterSubstition = substituteNibbles(addedKey, True)

    # after shifting
    afterShifting = shifting(afterSubstition)
    afterShifting = string2blist(afterShifting)

    # After mixing columns
    afterMixing = mix_col(afterShifting)

    # after add Round key
    subkeys = keyGeneration(key)

    afterAddingRoundKey = xor(afterMixing, subkeys[1])

    # second Round
    afterSubstitionRound2 = substituteNibbles(afterAddingRoundKey, True)
    afterShifting2 = shifting(afterSubstitionRound2)
    afterAddingRoundKeyRound2 = addRoundKey(afterShifting2, subkeys[2])

    # Done with encryption
    return afterAddingRoundKeyRound2


# initializing the functions for the Encryption
# adding key to plainText
def addRoundKey(plaintext, key):
    return xor(plaintext, key)

# for encrypt
def substituteNibbles(addedKey, encrypt):
    substitutedleftByte = subNibbles(
        [addedKey[0], addedKey[1], addedKey[2], addedKey[3], addedKey[4], addedKey[5], addedKey[6], addedKey[7]],
        encrypt)
    substitutedRghtByte = subNibbles(
        [addedKey[8], addedKey[9], addedKey[10], addedKey[11], addedKey[12], addedKey[13], addedKey[14], addedKey[15]],
        encrypt)
    afterSubstition = substitutedleftByte + substitutedRghtByte
    return afterSubstition


# shifting 2nd nibble and 4th nibble
def shifting(list):
    list2 = [list[0], list[1], list[2], list[3], list[12], list[13], list[14], list[15], list[8], list[9], list[10],
             list[11], list[4], list[5], list[6], list[7]]
    return list2



def test():
    for (plaintext, key, ciphertext) in [
         (# Stallings, Exercise 5.10 / 5.12 / 5.14
          '0110111101101011',
          '1010011100111011',
          '0000011100111000')
        ,(# Gordon
          '1101011100101000',
          '0100101011110101',
          '0010010011101100')
        ,(# Holden
          '0110111101101011',
          '1010011100111011',
          '0000011100111000')
        ]:
        plaintext = string2blist(plaintext)
        ciphertext = string2blist(ciphertext)
        key = string2blist(key)
        assert(saes_encrypt(plaintext=plaintext, key=key)
               == ciphertext)
        assert(saes_decrypt(ciphertext=ciphertext, key=key)
               == plaintext)

if __name__ == '__main__':
    test()

mix_col([0, 0, 1, 0, 1, 1, 1, 0, 1, 1, 1, 0, 1, 1, 1, 0])
