# Code-Golfed ECDSA Signature Verification in x86 Assembly (64-bit)

This is an implementation of the ECDSA signature verification, when
working over the NIST elliptic curve P-256. This implementation was
optimized for having a minimal binary code size. Aiming for a very
reduced code size can be useful in some niche situations (e.g. for
the boot ROM of a device that wants to verify a signature on its
firmware in Flash memory before executing it), though this specific
implementation is stupidly slow and thus should probably not be
used at all. This is more an artistic statement.

**Achieved size: 766 bytes**

**Speed:** about 257 million clock cycles on an Intel i5-8259U (a
"Coffee Lake" core, very similar to Skylake). This is about a thousand
times slower than what you'd normally expect from a usual
implementation.

API is defined in [*ecdsa-p256-verify.h*](ecdsa-p256-verify.h).
Namely, there is a single function, to which is provided the signature
to verify, the public key, and the hashed message:

  - The signature uses the "IEEE p1363 format" in which the *r* and *s*
    integers are encoded over 32 bytes each (unsigned big-endian
    convention) and concatenated in that order. This is *not* the
    ASN.1/DER format which is often encountered in, for instance,
    X.509 certificates. Conversion between the two formats is not
    especially hard, but no function to do that is provided.

  - The public key is in ANSI X9.62 uncompressed format: the public key
    contains both x and y coordinates of the public key point, and is
    encoded over exactly 65 bytes (the first byte has value 0x04).

  - The caller is expected to provide the hash value computed over the
    signed message. The hash function is not provided. Usually, SHA-256
    is used with ECDSA over the P-256 curve, but the algorithm can work
    with other hash functions. The only restriction enforced by the API
    is that the hash value has size between 32 and 64 bytes (inclusive).

The function returns 1 if the signature is valid, 0 otherwise.

The implementation itself is in
[*ecdsa-p256-verify_stupid.S*](ecdsa-p256-verify_stupid.S). It compiles
into a stand-alone object file with no external dependency. It is meant
for x86 systems in 64-bit mode, and complies with the SysV EABI as
used in, for instance, Linux systems. It is written using the "AT&T"
syntax. The file name ends with an uppercase `.S`, meaning that it expects
to be preprocessed with the C preprocessor; this is used to enable
some unit test framework (if compiled with `-DTV_ECDSA_P256_TEST`.

To compile type `make`; this generates a test program that exercises 492
test vectors from the [Wycheproof
project](https://github.com/c2SP/wycheproof). Running the program with
the `-s` command-line argument runs a speed benchmark; this entails
accessing performance counters and will probably crash on your machine.
It is also meaningless if you do not disable CPU frequency scaling, aka
"TurboBoost". See
[cycle-counter](https://github.com/pornin/cycle-counter) for details.
