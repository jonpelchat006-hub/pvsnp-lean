"""
Part 11: SHA-256 round by round.

The SHA-256 compression function, vectorized over many messages with numpy,
returning the 256-bit working state (a..h) after every round. With all 64
rounds and the final feed-forward it is checked against hashlib.

Round constants can be swapped:
  "sha256" - the standard ones (cube roots of the first 64 primes)
  "zero"   - all zero
  "golden" - K_t = floor(frac(t * phi) * 2^32), a golden-ratio sequence
             (t = 1 gives 0x9E3779B9, the constant TEA and RC5 use)
"""

import hashlib
import struct

import numpy as np

M32 = np.uint32(0xFFFFFFFF)

K_SHA = np.array([
    0x428a2f98, 0x71374491, 0xb5c0fbcf, 0xe9b5dba5, 0x3956c25b, 0x59f111f1, 0x923f82a4, 0xab1c5ed5,
    0xd807aa98, 0x12835b01, 0x243185be, 0x550c7dc3, 0x72be5d74, 0x80deb1fe, 0x9bdc06a7, 0xc19bf174,
    0xe49b69c1, 0xefbe4786, 0x0fc19dc6, 0x240ca1cc, 0x2de92c6f, 0x4a7484aa, 0x5cb0a9dc, 0x76f988da,
    0x983e5152, 0xa831c66d, 0xb00327c8, 0xbf597fc7, 0xc6e00bf3, 0xd5a79147, 0x06ca6351, 0x14292967,
    0x27b70a85, 0x2e1b2138, 0x4d2c6dfc, 0x53380d13, 0x650a7354, 0x766a0abb, 0x81c2c92e, 0x92722c85,
    0xa2bfe8a1, 0xa81a664b, 0xc24b8b70, 0xc76c51a3, 0xd192e819, 0xd6990624, 0xf40e3585, 0x106aa070,
    0x19a4c116, 0x1e376c08, 0x2748774c, 0x34b0bcb5, 0x391c0cb3, 0x4ed8aa4a, 0x5b9cca4f, 0x682e6ff3,
    0x748f82ee, 0x78a5636f, 0x84c87814, 0x8cc70208, 0x90befffa, 0xa4506ceb, 0xbef9a3f7, 0xc67178f2,
], dtype=np.uint32)

IV = np.array([0x6a09e667, 0xbb67ae85, 0x3c6ef372, 0xa54ff53a,
               0x510e527f, 0x9b05688c, 0x1f83d9ab, 0x5be0cd19], dtype=np.uint32)


def golden_constants():
    from math import isqrt
    root5 = isqrt(5 * 4 ** 80)                         # floor(sqrt(5) * 2^80)
    out = []
    for t in range(1, 65):
        x = (t * ((1 << 80) + root5)) >> 1             # t * phi * 2^80 (exact integer part)
        out.append((x >> 48) & 0xFFFFFFFF)             # frac(t phi) * 2^32
    return np.array(out, dtype=np.uint32)


CONSTANTS = {"sha256": K_SHA, "zero": np.zeros(64, dtype=np.uint32), "golden": golden_constants()}


def rotr(x, n):
    return (x >> np.uint32(n)) | (x << np.uint32(32 - n))


def schedule(W16, rounds):
    W = [W16[:, t] for t in range(16)]
    for t in range(16, rounds):
        s0 = rotr(W[t - 15], 7) ^ rotr(W[t - 15], 18) ^ (W[t - 15] >> np.uint32(3))
        s1 = rotr(W[t - 2], 17) ^ rotr(W[t - 2], 19) ^ (W[t - 2] >> np.uint32(10))
        W.append(W[t - 16] + s0 + W[t - 7] + s1)
    return W


def rounds_states(W16, rounds=64, K=K_SHA, state=None):
    """States after rounds 1..rounds: array (rounds, N, 8) of uint32."""
    N = W16.shape[0]
    if state is None:
        state = np.broadcast_to(IV, (N, 8))
    a, b, c, d, e, f, g, h = (state[:, i].copy() for i in range(8))
    W = schedule(W16, rounds)
    out = np.empty((rounds, N, 8), dtype=np.uint32)
    with np.errstate(over="ignore"):
        for t in range(rounds):
            S1 = rotr(e, 6) ^ rotr(e, 11) ^ rotr(e, 25)
            ch = (e & f) ^ (~e & g)
            T1 = h + S1 + ch + K[t] + W[t]
            S0 = rotr(a, 2) ^ rotr(a, 13) ^ rotr(a, 22)
            mj = (a & b) ^ (a & c) ^ (b & c)
            T2 = S0 + mj
            h, g, f = g, f, e
            e = d + T1
            d, c, b = c, b, a
            a = T1 + T2
            out[t] = np.stack([a, b, c, d, e, f, g, h], axis=1)
    return out


def digest_one_block(msg: bytes):
    """Full SHA-256 of a message shorter than 56 bytes, via rounds_states."""
    assert len(msg) < 56
    block = msg + b"\x80" + b"\x00" * (55 - len(msg)) + struct.pack(">Q", 8 * len(msg))
    W16 = np.array(struct.unpack(">16I", block), dtype=np.uint32)[None, :]
    with np.errstate(over="ignore"):
        final = rounds_states(W16)[-1][0] + IV
    return b"".join(struct.pack(">I", int(v)) for v in final)


def check_against_hashlib(trials=200, seed=1):
    rng = np.random.default_rng(seed)
    for _ in range(trials):
        msg = bytes(rng.integers(0, 256, size=int(rng.integers(0, 56)), dtype=np.uint8))
        if digest_one_block(msg) != hashlib.sha256(msg).digest():
            return False
    return True


def bits(states):
    """(..., 8) uint32 -> (..., 256) of 0/1, word-major, bit 31 first."""
    s = states[..., None] >> np.arange(31, -1, -1, dtype=np.uint32)
    return (s & np.uint32(1)).reshape(*states.shape[:-1], 256).astype(np.uint8)


def xor_sums(W16, rounds=64, K=K_SHA, state=None):
    """XOR of the working state over all N messages, after each round:
    array (rounds, 8). Memory stays at one round of states."""
    N = W16.shape[0]
    if state is None:
        state = np.broadcast_to(IV, (N, 8))
    a, b, c, d, e, f, g, h = (state[:, i].copy() for i in range(8))
    W = schedule(W16, rounds)
    out = np.empty((rounds, 8), dtype=np.uint32)
    with np.errstate(over="ignore"):
        for t in range(rounds):
            S1 = rotr(e, 6) ^ rotr(e, 11) ^ rotr(e, 25)
            ch = (e & f) ^ (~e & g)
            T1 = h + S1 + ch + K[t] + W[t]
            S0 = rotr(a, 2) ^ rotr(a, 13) ^ rotr(a, 22)
            mj = (a & b) ^ (a & c) ^ (b & c)
            T2 = S0 + mj
            h, g, f = g, f, e
            e = d + T1
            d, c, b = c, b, a
            a = T1 + T2
            out[t] = [np.bitwise_xor.reduce(v) for v in (a, b, c, d, e, f, g, h)]
    return out
