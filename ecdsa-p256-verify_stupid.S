# ========================================================================
# Code-golfed ECDSA signature verification in x86 assembly (64-bit mode).
#
# This code is very small (766 bytes) but also very slow (about 275 million
# cycles on an Intel Skylake-class CPU) and should probably not be used in
# practice.
# ========================================================================

	.arch	generic64
	.file	"ecdsa-p256-verify_stupid.S"
	.text

# ========================================================================
# PLATFORM COMPATIBILITY
#
# This code was meant for systems using the SysV EABI, e.g. Linux.
# Functions expect pointer/integer arguments to be provided in registers
# RDI, RSI, RDX, RCX, R8 and R9, in that order. To use this code on
# Windows, which uses a different convention, the externally callable
# functions must be adjusted (namely all functions whose name starts
# with 'tv_': the main API function tv_ecdsa_p256_verify(), and the
# test-only functions).
#
# Only standard 64-bit x86 instructions are used (no reliance on extensions
# such as BMI2). SSE instructions are not used at all. The code is
# self-contained and does not reference external functions; it is also
# position-independent.
#
# The code does NOT rely on the "red zone" which is part of the SysV EABI
# (the 128 bytes _below_ the stack pointer are guaranteed to remain
# unmodified, even by asynchronous code such as interruptions or signal
# delivery). This makes it compatible with more situations, e.g. as part
# a custom boot ROM.
# ========================================================================

# ========================================================================
# INTEGER FORMAT
#
# We use a simple little-endian encoding of integers over 32 bytes. These
# can be processed as 8 limbs of 32 bits, or 4 limbs of 64 bits; both
# work. Integers are all unsigned. When an addition overflows, the current
# modulus is subtracted, possibly twice, to ensure the value is brought
# back to a 256-bit range; similarly, on subtraction overflow, the current
# modulus is added, possibly twice.
# ========================================================================

# ========================================================================
# void decode_int(gf *d, const uint8_t *src)
# Decode value from the source (32 bytes, unsigned, big-endian) into
# the destination (32 bytes, unsigned, little-endian).
# SPECIAL ABI:
# Input:
#    bits 8..63 of rcx MUST be zero
# Output:
#    rdi = (uint8_t *)d + 32
#    rsi = src + 32
# Clobbers: rax, rcx
# ========================================================================

# WARNING: decode_int() has size 15 bytes and is immediately followed by
# curve_constants. This is used in the INTERPRETER_BEGIN macro (later on)
# and in particular the function size is hardcoded there (to get a more
# size-efficient opcode encoding).
# IF THIS FUNCTION IS MODIFIED, INTERPRETER_BEGIN MUST BE ADJUSTED.
	.type	decode_int, %function
decode_int:
	# WARNING: callers rely on r8-r10 not being modified

	# Split source words into limbs, pushed onto the stack.
	# Least significant limb is pushed last.
	# We can use 'loop' even though we only set cl because the caller
	# ensured that rcx[8..63] = 0.
	movb	$8, %cl
Ldecode_int__loop1:
	lodsl
	bswapl	%eax        # source is big-endian
	pushq	%rax
	loop	Ldecode_int__loop1

	# Pop back words and write into destination. The move through
	# the stack ensures that the values are in the right order.
	movb	$8, %cl
Ldecode_int__loop2:
	popq	%rax
	stosl
	loop	Ldecode_int__loop2

	ret
	.size	decode_int, . - decode_int

# Curve constants, in that order:
#   Gx           curve generator point, X coordinate
#   Gy           curve generator point, Y coordinate
#   b            curve parameter b
#   mod_scalar   modulus n (scalar field)
#   mod_coord    modulus p (coordinate field)
# All values use unsigned LITTLE-ENDIAN encoding (32 bytes per value).
# WARNING: values MUST NOT be separated or reordered.
# WARNING: the bytecode must follow immediately after the curve constants.
curve_constants:
	# Gx
	.quad	0xF4A13945D898C296, 0x77037D812DEB33A0
	.quad	0xF8BCE6E563A440F2, 0x6B17D1F2E12C4247
	# Gy
	.quad	0xCBB6406837BF51F5, 0x2BCE33576B315ECE
	.quad	0x8EE7EB4A7C0F9E16, 0x4FE342E2FE1A7F9B
	# b
	.quad	0x3BCE3C3E27D2604B, 0x651D06B0CC53B0F6
	.quad	0xB3EBBD55769886BC, 0x5AC635D8AA3A93E7
mod_N:
	.quad	0xF3B9CAC2FC632551, 0xBCE6FAADA7179E84
	.quad	0xFFFFFFFFFFFFFFFF, 0xFFFFFFFF00000000
mod_P:
	.quad	0xFFFFFFFFFFFFFFFF, 0x00000000FFFFFFFF
	.quad	0x0000000000000000, 0xFFFFFFFF00000001

# -------------------------------------------------------------------------
# BEGIN BYTECODE
# -------------------------------------------------------------------------

# ========================================================================
# Custom virtual machine.
#
# We use an interpreter for a virtual machine with a few instructions.
# The instructions are specialized for the problem at hand. Each
# instruction fits on one byte (except CALL, which uses two bytes).
# The VM works with 32 values (numbered 0 to 31); each value holds an
# integer in 5-limb format:
#  - Value 0 is the accumulator; it is used as source and/or destination
#    operand by many of the instructions.
#  - Value 1 contains the current modulus (which can be set to either
#    mod_N or mod_P with the SMOD instruction); it can be read, but not
#    written to.
#  - Values 2 to 31 are other values. A few are preloaded with constants,
#    which in general should not be modified by code:
#       27   ZERO (the integer value 0)
#       28   ONE (the integer value 1)
#       29   Gx (x coordinate of generator point, affine)
#       30   Gy (y coordinate of generator point, affine)
#       31   B (b curve parameter)
#    All other values are initialized at zero. Value 27 is conventionally
#    considered to be "the" constant ZERO.
# Symbolic names are defined for modifiable values; from the VM point of
# view, these values are nothing special (except F1), but the bytecode uses
# them to organize its ECDSA subroutines:
#        2       F1         reserved for implementation of MUL
#        3       Kr         r (first signature half)
#        4       Ks         s (second signature half)
#        5       Ke         e (reduced hash value)
#        6       Qx         x coordinate of public key
#        7       Qy         y coordinate of public key
#        8       Wx         X coordinate of work point W (projective)
#        9       Wy         Y coordinate of work point W (projective)
#       10       Wz         Z coordinate of work point W (projective)
#       11       Hx         X coordinate of work point H (projective)
#       12       Hy         Y coordinate of work point H (projective)
#       13       Hz         Z coordinate of work point H (projective)
#       16..25   T0 to T9   temporaries
#       26       F0         reserved for implementation of MUL
# The tv_ecdsa_p256_verify() function, when setting up the interpreter,
# loads Kr, Ks, Ke, Qx and Qy with the relevant values, freshly decoded
# from the parameters (signature, hash value and public key). The values
# are decoded into 32-byte little-endian format but not otherwise checked;
# the bytecode is responsible for verifying that:
#    0 < r < n
#    0 < s < n
#    0 <= Qx < p
#    0 <= Qy < p
#    (Qx, Qy) is a point on the curve
#
# Instructions are the following:
#
#    encoding   mnemonic     operation
#    --------   --------     ---------
#    xxxxx000   LD x         acc <- x
#    xxxxx001   ST x         x <- acc
#    xxxxx010   ADD x        acc <- acc + x
#    xxxxx011   SUB x        acc <- acc - x
#    xxxxx100   SMOD y       set modulus to mod_N (y = 30) or mod_P (y = 31)
#    xxxxx101   MUL x        acc <- acc*x mod m
#    xxxxx110   SKIPBITZ x   skip next if current bit in x is zero
#    00000111   SKIPCS       skip next if carry is set
#    00001111   SKIPCC       skip next is carry is clear
#    00010111   RET          return from subroutine
#    00011111   FOR          initialize bit iterator
#    00100111   NEXT         loop back iterator
#    00101111   OK           exit with a success
#    00110111   FAIL         exit with a failure
#    00111111   CALL label   call subroutine (+immediate offset)
#
# "LD x" copies value x (0 <= x <= 31) into the accumulator. "ST x" copies
# the accumulator into value x. "ADD x" (resp. "SUB x") adds x to (resp.
# subtracts x from) the accumulator. "MUL x" multiplies the accumulator with
# value x (it is actually a pseudo-instruction which is implemented with
# a hidden subroutine). ADD, SUB and MUL use the current modulus, which is
# set with "SMOD y" (parameter y must be 30 or 31, for n and p,
# respectively); the current modulus can also be read from value 1.
#
# A carry flag is set when the last addition or subtraction overflowed; it
# is cleared when it did not. Either way, the current modulus is automatically
# added or subtracted as necessary to counteract the overflow. "SKIPCC" and
# "SKIPCS" make the VM skip the next instruction if the carry is currently
# cleared or set, respectively.
#
# A loop facility is provided; two loops may nest: the code cannot run
# an internal loop within an outer loop (internally, one level of
# nesting is supported, but the inner level is used for the
# implementation of MUL). "FOR" starts the loop, and "NEXT" triggers the
# next iteration. The loop runs for exactly 256 iterations. There can be
# several "NEXT" opcodes matching a single "FOR". While the iteration runs,
# the "SKIPBITZ x" opcode uses the current iteration counter (255 to 0)
# as a bit index within value x, and tests whether the corresponding bit
# is set or cleared; if cleared, then the next instruction is skipped.
# This facility is meant to support square-and-multiply exponentiation
# as well as double-and-add point multiplication.
#
# Subroutines are supported: "CALL label" jumps to the subroutine located
# at the provided assembly label; "RET" returns from the current subroutine
# to the caller. Nested calls are supported. In the encoding, the subroutine
# offset is encoded as an 8-bit unsigned value that immediately follows the
# "CALL": this implies that the target of the CALL can only be located
# _after_ the call site in the bytecode (and it must not be farther than
# 255 bytes away). The "skip" instructions correctly skip the two bytes of
# a "CALL" function.
#
# The "OK" and "FAIL" instructions terminate the interpreter with an exit
# status of 1 or 0, respectively. They can be used within called subroutines,
# not just at the toplevel.
# ========================================================================

# VALUE ALLOCATION
# WARNING: code relies on Kr, Ks, Ke, Qx and Qy to be consecutive.

	# Symbolic identifiers for various slots.
	.equ	_M,     1    # current modulus
	.equ	_F1,    2    # reserved for MUL
	.equ	_ZERO, 27    # constant zero
	.equ	_ONE,  28    # constant one
	.equ	_Gx,   29    # constant Gx (x coordinate of generator)
	.equ	_Gy,   30    # constant Gy (y coordinate of generator)
	.equ	_B,    31    # constant b (curve parameter)
	.equ	_T0,   16    # temporary 0
	.equ	_T1,   17    # temporary 1
	.equ	_T2,   18    # temporary 2
	.equ	_T3,   19    # temporary 3
	.equ	_T4,   20    # temporary 4
	.equ	_T5,   21    # temporary 5
	.equ	_T6,   22    # temporary 6
	.equ	_T7,   23    # temporary 7
	.equ	_T8,   24    # temporary 8
	.equ	_T9,   25    # temporary 9
	.equ	_F0,   26    # reserved for MUL

	.equ	_Kr,    3    # r (first signature half)
	.equ	_Ks,    4    # s (second signature half)
	.equ	_Ke,    5    # e (reduced hash value)
	.equ	_Qx,    6    # Qx (x coordinate of public key)
	.equ	_Qy,    7    # Qy (y coordinate of public key)
	.equ	_Wx,    8    # Wx (X coordinate of work point W)
	.equ	_Wy,    9    # Wy (Y coordinate of work point W)
	.equ	_Wz,   10    # Wz (Z coordinate of work point W)
	.equ	_Hx,   11    # Hx (X coordinate of second point operand)
	.equ	_Hy,   12    # Hy (Y coordinate of second point operand)
	.equ	_Hz,   13    # Hz (Z coordinate of second point operand)

	# Opcode base values.
	.equ	OP_LD,        0x00
	.equ	OP_ST,        0x01
	.equ	OP_ADD,       0x02
	.equ	OP_SUB,       0x03
	.equ	OP_SMOD,      0x04
	.equ	OP_MUL,       0x05
	.equ	OP_SKIPBITZ,  0x06
	.equ	OP_SKIPCS,    0x07
	.equ	OP_SKIPCC,    0x0F
	.equ	OP_RET,       0x17
	.equ	OP_FOR,       0x1F
	.equ	OP_NEXT,      0x27
	.equ	OP_OK,        0x2F
	.equ	OP_FAIL,      0x37
	.equ	OP_CALL,      0x3F

# Macros to help write bytecode.
.macro	_LD x
	.byte	(\x) * 8 + OP_LD
.endm
.macro	_ST x
	.byte	(\x) * 8 + OP_ST
.endm
.macro	_ADD x
	.byte	(\x) * 8 + OP_ADD
.endm
.macro	_SUB x
	.byte	(\x) * 8 + OP_SUB
.endm
.macro	_SMOD y
	.byte	(\y) * 8 + OP_SMOD
.endm
.macro	_MUL x
	.byte	(\x) * 8 + OP_MUL
.endm
.macro	_SKIPBITZ x
	.byte	(\x) * 8 + OP_SKIPBITZ
.endm
.macro	_SKIPCS
	.byte	OP_SKIPCS
.endm
.macro	_SKIPCC
	.byte	OP_SKIPCC
.endm
.macro	_RET
	.byte	OP_RET
.endm
.macro	_FOR
	.byte	OP_FOR
.endm
.macro	_NEXT
	.byte	OP_NEXT
.endm
.macro	_OK
	.byte	OP_OK
.endm
.macro	_FAIL
	.byte	OP_FAIL
.endm
.macro	_CALL  label
	.byte	OP_CALL
	.byte	\label - 1f
1:
.endm

# _MODN is an alias for _SMOD 30, i.e. switching modulus to mod_N.
.macro	_MODN
	_SMOD 30
.endm

# _MODP is an alias for _SMOD 31, i.e. switching modulus to mod_P.
.macro	_MODP
	_SMOD 31
.endm

# BYTECODE ENTRY POINT
# WARNING: the code locates the entry point relatively to the
# constants: it must immediately follow the modulus p in the curve constants
# block.

	# Check that r and s are both non-zero and below n
	_LD _Kr ; _CALL check_scalar
	_LD _Ks ; _CALL check_scalar
	# Invert s.
	_CALL invert_mod ; _ST _Ks
	# Compute u = e/s (into Ke).
	_MUL _Ke ; _ST _Ke
	# Compute v = r/s (into Ks).
	_LD _Ks ; _MUL _Kr ; _ST _Ks

	# We have u and v; we now switch to modulus p for curve computations.
	_MODP

	# Check that the point in (Qx,Qy) is a valid curve point.
	_CALL check_point

	# Compute W = u*G + v*Q
	# Set work point W to the neutral (0:1:0). Values Wx and Wz were
	# initialized at zero by the interpreter initialization, so we only
	# need to set Wy to 1.
	_LD _ONE ; _ST _Wy
	# We loop over bits in u and v (high to low).
	_FOR
	# Double W.
	_LD _Wx ; _ST _Hx ; _LD _Wy ; _ST _Hy ; _LD _Wz ; _ST _Hz
	_CALL point_add_to_W
	# Add G if bit i of u is set; u is in Ke
	_LD _Gx ; _ST _Hx ; _LD _Gy ; _ST _Hy ; _LD _ONE ; _ST _Hz
	_SKIPBITZ _Ke ; _CALL point_add_to_W
	# Add Q if bit i of v is set; v is in Ks; Hz still contains 1
	_LD _Qx ; _ST _Hx ; _LD _Qy ; _ST _Hy
	_SKIPBITZ _Ks ; _CALL point_add_to_W
	# Loop until all bits have been processed.
	_NEXT

	# Get x coordinate of point W. For now we suppose that W is not
	# the point-at-infinity.
	_LD _Wz ; _CALL invert_mod ; _MUL _Wx
	# We need x in canonical format ([0,p-1]). Subtracting the modulus
	# does the trick: either the value was not lower that p, in which
	# case the subtraction was needed, or it was lower than p, and the
	# subtraction overflowed, and the modulus was added back.
	_SUB _M

	# Signature is valid if and only if we get back the same value
	# as r, when reduced modulo n. We switch back to computations
	# modulo n, then compute r - x(W) mod n; signature is valid if
	# and only if that yields a zero.
	_MODN ; _SUB _Kr ; _SUB _M
	_SUB _ONE ; _SKIPCS ; _FAIL ; _OK

	# If W was the point-at-infinity, then inversion of Wz yielded zero,
	# and the rebuilt x(W) was zero. Since r != 0 (we checked it
	# explicitly), this case implies a signature rejection, which is
	# the correct result.

# BYTECODE: Check that a value (just decoded) is non-zero and less than
# the modulus. This is meant for scalars; it uses the current modulus.
# Input:
#    acc   value to check
# Output:
#    acc   x
check_scalar:
	# Check that x < m: subtracting the modulus should overflow.
	_SUB _M ; _SKIPCS ; _FAIL
	# Check that x != 0; subtracting 1 should not overflow.
	_SUB _ONE ; _SKIPCC ; _FAIL ; _ADD _ONE ; _RET

# BYTECODE: Modular inversion. The current modulus is used.
# Input:
#    acc   value to invert
# Output:
#    acc   computed inverse (zero if input is zero)
# Clobbers: T0, T1
invert_mod:
	# Copy source value into T0.
	_ST _T0
	# Set T1 to exponent, which is m-2 (canonical) for modulus m.
	# Subtraction is limb-wise but for the two involved moduli (p and n)
	# this does not overflow any limb, so m-2 is still canonical.
	_LD _M ; _SUB _ONE ; _SUB _ONE ; _ST _T1
	# Set accumulator to 1.
	_LD _ONE
	# Start iterator
	_FOR
	# Square current value
	_MUL 0
	# If current bit is 1, multiply accumulator by operand
	_SKIPBITZ _T1 ; _MUL _T0
	# Loop until finished, then exit
	_NEXT ; _RET

# BYTECODE: Check decoded point. This function verifies that the two
# coordinates are in [0,p-1] and that they fulfill the curve equation.
# Input:
#    current modulus MUST be mod_P
#    Qx   candidate x coordinate (affine)
#    Qy   candidate y coordinate (affine)
# No output. A failure is triggered if the point is incorrect.
# Clobbers: T0
check_point:
	# Check that Qx is lower than p. It was just decoded, and thus
	# we can simply subtract the modulus and check the carry.
	_LD _Qx ; _SUB _M ; _SKIPCS ; _FAIL
	# While it's loaded in the accumulator, compute X^3 and store
	# it into _T0.
	_MUL _Qx ; _MUL _Qx ; _ST _T0
	# Check that Qy is lower than p (same treatment as Qx).
	_LD _Qy ; _SUB _M ; _SKIPCS ; _FAIL
	# We must check the curve equation:
	#    y^2 = x^3 - 3*x + b
	# The accumulator still contains y.
	_MUL _Qy ; _SUB _T0
	_ADD _Qx ; _ADD _Qx ; _ADD _Qx ; _SUB _B
	# Compare with 0.
	_SUB _M ; _SUB _ONE ; _SKIPCS ; _FAIL
	_RET

# BYTECODE: Add a curve point to point W. Point W is in projective
# coordinates in (Wx:Wy:Wz); the other operand is read from (Hx:Hy:Hz).
# Inputs:
#    Wx   first operand X coordinate
#    Wy   first operand Y coordinate
#    Wz   first operand Z coordinate
#    Hx   second operand X coordinate
#    Hy   second operand Y coordinate
#    Hz   second operand Z coordinate
# Output is written back into (Wx:Wy:Wz).
# Clobbers: T0 to T8
point_add_to_W:
	# t0 <- X1 * X2
	_LD _Wx ; _MUL _Hx ; _ST _T0
	# t1 <- Y1 * Y2
	_LD _Wy ; _MUL _Hy ; _ST _T1
	# t2 <- Z1 * Z2
	# t7 <- bb * t2
	_LD _Wz ; _MUL _Hz ; _ST _T2 ; _MUL _B ; _ST _T7

	# t3 <- (X1 + Y1)*(X2 + Y2) - t0 - t1
	_LD _Wx ; _ADD _Wy ; _ST _T3
	_LD _Hx ; _ADD _Hy ; _MUL _T3 ; _SUB _T0 ; _SUB _T1 ; _ST _T3

	# t6 <- (X1 + Z1)*(X2 + Z2) - t0 - t2
	_LD _Wx ; _ADD _Wz ; _ST _T6
	_LD _Hx ; _ADD _Hz ; _MUL _T6 ; _SUB _T0 ; _SUB _T2 ; _ST _T6
	# t6 is still in acc
	# t5 <- t1 + 3*(t6 - t7)
	# t7 <- t1 - 3*(t6 - t7)
	_SUB _T7 ; _ST _T5 ; _ADD 0 ; _ADD _T5   # acc <- 3*(t6 - t7)
	_ST _T7 ; _ADD _T1 ; _ST _T5
	_LD _T1 ; _SUB _T7 ; _ST _T7

	# t8 <- 3*t2
	_LD _T2 ; _ADD 0 ; _ADD _T2 ; _ST _T8

	# t6 <- 3*(b*t6 - t0 - t8)
	_LD _T6 ; _MUL _B ; _SUB _T0 ; _SUB _T8 ; _ST _T6
	_ADD 0 ; _ADD _T6 ; _ST _T6

	# t4 <- (Y1 + Z1)*(Y2 + Z2) - t1 - t2
	_LD _Wy ; _ADD _Wz ; _ST _T4
	_LD _Hy ; _ADD _Hz ; _MUL _T4 ; _SUB _T1 ; _SUB _T2 ; _ST _T4
	# t4 is still in acc
	# X1 <- t3*t5 - t4*t6
	_MUL _T6 ; _ST _Wx
	_LD _T3 ; _MUL _T5 ; _SUB _Wx ; _ST _Wx

	# t0 <- 3*t0 - t8
	_LD _T0 ; _ADD 0 ; _ADD _T0 ; _SUB _T8 ; _ST _T0
	# t0 is still in acc
	# Y1 <- t0*t6 + t5*t7
	_MUL _T6 ; _ST _Wy ; _LD _T5 ; _MUL _T7 ; _ADD _Wy ; _ST _Wy

	# Z1 <- t4*t7 + t3*t0
	_LD _T4 ; _MUL _T7 ; _ST _Wz
	_LD _T3 ; _MUL _T0 ; _ADD _Wz ; _ST _Wz

	_RET

# -------------------------------------------------------------------------
# END BYTECODE
# -------------------------------------------------------------------------

# ========================================================================
# VM INTERPRETER
#
# The interpreter maintains a context structure on the stack, of size
# 1088 bytes. The rbp register points to that context.
# Value x (for 0 <= x <= 31) is at address rbp+32*x; moduli n and p are
# located at rbp+1024 and rbp+1056, respectively. Value 1 is special, in
# that instructions that read that value obtain the current modulus; the
# storage space of value 1 is reused for some values collectively called
# "the flags":
#
#    rbp+32    current modulus pointer (8 bytes)
#    rbp+40    saved original stack pointer (8 bytes)
#    rbp+48    exit flag (1 = exit reached, 0 = not done yet) (1 byte)
#    rbp+49    status flag (0 = err, 1 = success) (1 byte)
#
# The emulated carry flag is in r8b and loop state are stored in registers
# r8..r12.
#
# Instruction decoding uses first the translation_table (below), which
# points to the offset of the native routine for the instruction. The
# index consists of the three low bits of the instruction, and the
# offset is over one byte. This handles instructions LD, ST, ADD, SUB,
# SMOD, MUL, and SKIPBITZ (all instructions with a 5-bit parameter);
# other instructions are handled with op_extended, which does a secondary
# decoding with another table.
translation_table:
	.byte	op_ld - translation_table
	.byte	op_st - translation_table
	.byte	op_add - translation_table
	.byte	op_sub - translation_table
	.byte	op_smod - translation_table
	.byte	op_mul - translation_table
	.byte	op_skipbitz - translation_table
	.byte	op_extended - translation_table

# BYTECODE INTERNAL: routine for multiplication. Second operand has been
# copied into F1.
# WARNING: this routine MUST immediately follow the translation_table.
# WARNING: if this routine is modified, check offsets in op_add.
microcode_mul:
	# First operand is in the accumulator: move to F0, then clear acc.
	_ST _F0 ; _LD _ZERO
	# Double-and-add algorithm.
	_FOR                      # for i = 255 to 0:
	_ADD 0                    #    acc <- 2*acc
	_SKIPBITZ _F1 ; _ADD _F0  #    if F1[i] != 0: acc <- acc + F0
	_NEXT ; _RET

# WARNING: this routine MUST immediately follow microcode_mul
# WARNING: if this routine is modified, check offsets in op_add.
# z256_add:
# [rbp] <- [rbp] + [rsi] (32 bytes), CF out
# Clobbers: rax, rcx, rdx, rsi
	.type	z256_add, %function
	# Function size is 16 bytes
z256_add:
	xorl	%edx, %edx    # also clears CF
	movb	$8, %cl
Lz256_add__loop:
	lodsl
	adcl	%eax, (%rbp,%rdx,4)
	incb	%dl
	# We could use 'loop' here (and in z256_sub below); this would save
	# four bytes in total, but runtime cost would significantly jump up
	# (270Mcyc -> 432Mcyc) because 'loop' is inefficient in modern x86,
	# so we'll abstain.
	decb	%cl
	jnz	Lz256_add__loop
	ret
	.size	z256_add, . - z256_add

# WARNING: this routine MUST immediately follow microcode_mul
# z256_sub:
# [rbp] <- [rbp] - [rsi] (32 bytes), CF out
# Clobbers: rax, rcx, rdx, rsi
	.type	z256_sub, %function
z256_sub:
	xorl	%edx, %edx    # also clears CF
	movb	$8, %cl
Lz256_sub__loop:
	lodsl
	sbbl	%eax, (%rbp,%rdx,4)
	incb	%dl
	# See comment about 'loop' in z256_add.
	decb	%cl
	jnz	Lz256_sub__loop
	ret
	.size	z256_sub, . - z256_sub

# Instruction routine conventions:
#  - each routine is invoked with 'call' and ends with a ret opcode
#  - rax contains the routine's own address
#  - rbx and rbp must be preserved
#  - cl contains the top five bits of the current opcode and the rest of
#    rcx is zero (this is the 5-bit parameter value)
#  - rdx points to the explicit operand value (i.e. rbp+32*x, or the
#    current modulus if x = 1)
#  - rsi contains the instruction pointer (pointing to the byte that
#    follows the instruction)
#  - rsp+8 contains the saved instruction pointer (copy of rsi); this is
#    the value that the interpreter will use to reach the next instruction
#    when this one is finished
#  - r8b contains the carry from the last addition or subtraction
#    (1 = carry set, 0 = carry clear); it must be preserved by all other
#    opcodes
#  - r9d contains the current loop counter, and r10 the loop start address
#  - r11d and r12 contain the saved loop counter and start address
#    (for nested loops)
#  - CPU carry flag (CF) is cleared
# The stack is used for subroutine calls: appart from the native return
# address pushed when calling the instruction routine, the stack contains
# nested instruction pointers for the calls.

# LD x    copy value x into accumulator
op_ld:
	pushq	%rdx
	popq	%rsi
	pushq	%rbp
	popq	%rdi
# docopy is a shareable routine that copies 40 bytes from rsi to rdi
# (assumption: bits 8..63 of rcx are zero).
docopy:
	movb	$32, %cl
	rep movsb
	ret

# ST x    copy accumulator into value x
op_st:
	pushq	%rdx
	popq	%rdi
	pushq	%rbp
	popq	%rsi
	jmp	docopy

# SUB x   subtract value x from accumulator
op_sub:
	stc
	# FALL THROUGH
# ADD x   add value x to accumulator
op_add:
	# The primary function is the one that performs the operation on
	# the values (z256_add() for ADD, z256_sub() for SUB) while the
	# secondary function is the one that applies the corrective action
	# with the modulus (z256_sub() for ADD, z256_add() for SUB). The
	# CPU carry flag (CF) is cleared when this routine is called for
	# ADD, but it is set when we are executing a SUB. We use CF to
	# set pointers to the primary and secondary functions.
	# Moreover, these two functions are located relatively from the
	# translation table, with small offsets.
	leaq	16(%rbx), %rdi   # z256_add (primary)
	leaq	32(%rbx), %rax   # z256_sub (secondary)
	jnc	Lop_add__cont1
	# For SUB, CF is set, so we exchange z256_add and z256_sub
	xchgq	%rdi, %rax
Lop_add__cont1:
	pushq	%rax       # save pointer to secondary function
	# Move pointer to second operand into rsi
	pushq	%rdx
	popq	%rsi
	callq	*%rdi      # call primary function
	setc	%r8b       # update emulated carry (copy of CF)
	popq	%rdi       # recover pointer to secondary function
	# If no carry out, we're done.
	jnc	Lop_add__cont2
	# Subtract modulus until a borrow is obtained (to counteract the carry).
Lop_add__loop:
	movq	32(%rbp), %rsi   # modulus
	callq	*%rdi      # call secondary function
	jnc	Lop_add__loop
Lop_add__cont2:
	ret

# SMOD y    switch current modulus (y = 30 for mod_N, y = 31 for mod_P)
op_smod:
	# &mod_N == rbp+1024
	# &mod_P == rbp+1056 == &mod_N + 32
	addq	$64, %rdx
	movq	%rdx, 32(%rbp)
	ret

# MUL x   multiply accumulator with x
op_mul:
	# The MUL routine expects the second operand to be in F1.
	pushq	%rsi    # save current instruction pointer
	pushq	%rdx
	popq	%rsi
	leaq	(_F1*32)(%rbp), %rdi  # F1 is value 2 -> offset 32*_F1 is small
	movb	$32, %cl
	rep movsb
	popq	%rsi    # restore current instruction pointer
	# Pretend that this is CALL to microcode_mul.
	# microcode_mul is located immediately after the translation_table,
	# which has size 8.
	leaq	8(%rbx), %rax
	jmp	docall

# SKIPBITZ x   skip next instruction if current bit is set in x
# The "current bit" relates to the iterator; this instruction makes sense
# only when an iteration is ongoing.
op_skipbitz:
	btl	%r9d, (%rdx)      # test bit value
	jc	Lret1
	# FALL THROUGH
# Common sequence for skipping the next instruction. This assumes that
# rsi contains the current instruction pointer; the saved instruction
# pointer (on the stack) is adjusted.
# WARNING: doskip requires rsi to still contain the instruction pointer.
doskip:
	# Increment the instruction pointer to skip the next instruction;
	# take care that CALL instruction has size 2 bytes.
	lodsb
	cmpb	$(OP_CALL), %al
	jne	Ldoskip__cont
	lodsb
Ldoskip__cont:
	popq	%rax
	popq	%rcx
	pushq	%rsi
	pushq	%rax
Lret1:
	ret

# The extended translation table is used for opcodes that do not have
# a value operand. This table contains routine offsets relative to
# op_extended.
extended_translation_table:
	# WARNING: if table size is changed, the movb instruction
	# in op_extended MUST be altered accordingly.
	.byte	op_skipcs - op_extended
	.byte	op_skipcc - op_extended
	.byte	op_ret - op_extended
	.byte	op_for - op_extended
	.byte	op_next - op_extended
	.byte	op_ok - op_extended
	.byte	op_fail - op_extended
	.byte	op_call - op_extended

# Pseudo-instruction invoked for extended opcodes.
op_extended:
	# %cl contains the opcode.
	# Use the secondary translation table. rax currently contains
	# the address of op_extended, and the table size is 8 bytes.
	# WARNING: if the table size is modified, the offset in the
	# movb instruction below MUST be modified. The offset is
	# hardcoded so that it uses only one byte in the generated
	# instruction (if using a symbol related expression, the assembler
	# generates a 32-bit offset).
	movb	-8(%rax,%rcx), %cl
	addq	%rcx, %rax
	jmpq	*%rax

# In extended opcodes, cl no longer contains relevant data (but
# bits 8..63 of rcx are still 0).

# SKIPCS   skip next instruction if emulated carry is set
op_skipcs:
	testb	%r8b, %r8b
	jnz	doskip
	ret

# SKIPCC   skip next instruction if emulated carry is cleared
op_skipcc:
	testb	%r8b, %r8b
	jz	doskip
	ret

# RET     return from subroutine
op_ret:
	popq	%rax    # return address for the opcode routine
	popq	%rsi    # saved instruction pointer
	pushq	%rax
	ret

# CALL   call subroutine
# The target subroutine address is provided as one inline byte
# immediately following the instruction; the byte is the offset
# (unsigned) to add to the current instruction pointer to obtain the
# address of the called subroutine. Since the offset is unsigned,
# this can only call subroutines located after the call site.
op_call:
	# rax <- subroutine address (callee)
	xorl	%eax, %eax
	lodsb
	addq	%rsi, %rax
	# FALL THROUGH
# docall performs a CALL operation. Inputs: current instruction pointer
# in rsi, target subroutine address in rax.
docall:
	# We must manipulate the stack so that the interpreter begins
	# fetching the instructions from the subroutine.
	# Current stack:
	#   rsp+8    saved instruction pointer (caller)
	#   rsp+0    opcode routine return address
	# New stack:
	#   rsp+16   saved instruction pointer (caller)
	#   rsp+8    saved instruction pointer (subroutine)
	#   rsp+0    opcode routine return address
	popq	%rdx    # remove native return address
	popq	%rcx    # remove old saved instruction pointer
	pushq	%rsi    # push caller address (right after the CALL opcode)
	pushq	%rax    # push callee address
	pushq	%rdx    # put back native return address
	ret

# FOR    start the iterator
# This sets the iterator counter to 255. Each NEXT instruction will
# decrement the iterator and loop back to immediately after the FOR,
# unless the counter reaches -1 (which terminates the loop).
op_for:
	# Nested loop support: move current counter and start address
	# to the save registers.
	movb	%r9b, %r11b
	movq	%r10, %r12
	# Set counter.
	movb	$255, %r9b
	# Save address of next instruction; this is where execution will
	# loop back upon NEXT.
	movq	%rsi, %r10
Lret2:
	ret

# NEXT   decrement iterator counter and loop
# If the counter is at zero, then the loop exits. Otherwise, the counter
# is decremented, and execution jumps to right after the FOR instruction
# that started the iterator.
op_next:
	# If bit offset is 0, loop is finished.
	cmpb	$0, %r9b
	jne	Lop_next__cont1
	# Loop is finished (iterator is 0), remove it.
	movb	%r11b, %r9b
	movq	%r12, %r10
	ret
Lop_next__cont1:
	# Decrement counter.
	decb	%r9b
	# Reset saved instruction pointer.
	popq	%rdx
	popq	%rsi
	pushq	%r10
	pushq	%rdx
Lop_next__cont2:
	ret

# OK     exit the interpreter with a success status
op_ok:
	# Set the success flag
	movb	$1, 49(%rbp)
	# FALL THROUGH
# FAIL   exit the interpreter with a failed status
op_fail:
	# Set the exit flag
	# Status is 0 by default, only OK sets it to 1.
	movb	$1, 48(%rbp)
	ret

# Interpreter is built as three macros, so that the test code may use
# some interpreters to exercise subroutines.

# Interpreter initialization: allocate and setup the stack context.
# Current values of rbx, r12 and rbp are saved; they will be restored when
# INTERPRETER_END is called.
# Outputs:
#    rbx   pointer to the decode_int() function
#    rbp   points to the allocated stack context
#    rsi   points to the bytecode entry point
# Clobbers: rax, rcx, rdx, rdi
# 1104 bytes are stored on the stack, and rbp is made equal to rsp. Previous
# top-of-stack can be accessed at 1104(%rbp).
.macro	INTERPRETER_BEGIN
	pushq	%rbx
	pushq	%r12
	leaq	decode_int(%rip), %rbx

	# WARNING: value "15" is the size of the decode_int() function. This
	# is hardcoded here because uing a proper offset expression
	# 'curve_constants - decode_int' would lead the assembler to use
	# a 4-byte offset in the opcode, instead of a 1-byte offset.
	# THIS VALUE MUST BE ADJUSTED IF decode_int() IS MODIFIED.
	leaq	15(%rbx), %rsi

	# Allocate the interpreter context.
	# Context consists of 32 slots of 32 bytes each, for the 32 values
	# (slot 1 is "virtual" and contains the flag), and an extra 64 byts
	# for mod_N and mod_P (each of size 32 bytes).

	# Reserve space for Gx, Gy, Bm, mod_N and mod_P.
	# The 'enter' opcode here is equivalent to:
	#   pushq  %rbp
	#   movq   %rsp, %rbp
	#   subq   $160, %rsp
	enter	$160, $0

	# Copy constants to stack slots (Gx, Gy, b) followed by
	# mod_N and mod_P.
	movq	%rsp, %rdi
	xorl	%ecx, %ecx
	movb	$160, %cl
	rep movsb

	# Now rsi points to the bytecode entry point (it immediately
	# follows the constants block).
	# Clear space for values 28 to 2, and the flags, except the slots
	# for the saved stack pointer and the current modulus.
	xorl	%eax, %eax
	movb	$110, %cl    # 111 = 28*4 - 2
1:
	pushq	%rax
	loop	1b
	# Push saved stack pointer.
	pushq	%rbp
	# Push pointer to current modulus (initially mod_N).
	subq	$64, %rbp
	pushq	%rbp
	# Value 28 is ONE.
	movb	$1, -128(%rbp)
	# Allocate space for the accumulator (uninitialized).
	subq	$32, %rsp
	movq	%rsp, %rbp
.endm

# Main interpreter loop.
# Inputs:
#    rbp   points to the allocated stack context
#    rsi   instruction pointer
# Outputs:
#    rbp is unchanged
#    stack MAY have grown (use rbp to access stack elements)
# Clobbers:
#    rax, rbx, rcx, rdx, rsi, rdi, r8
.macro	INTERPRETER_MAIN
	# Set rbx to point to the translation table.
	leaq	translation_table(%rip), %rbx
	xorl	%r9d, %r9d
1:
	# Load next instruction.
	xorl	%eax, %eax
	lodsb
	# Let al = 8*x + t  (x = high 5 bits, t = low 3 bits).
	# We want to:
	#  - translate instruction t into a pointer (in rax)
	#  - set rcx to x
	#  - set rdx to rbp + 32*x
	movl	%eax, %ecx    # this also clears all high bits of rcx
	andb	$0x07, %al    # al <- t
	xorb	%al, %cl      # cl <- 8*x
	xlatb
	leaq	(%rbp,%rcx,4), %rdx   # rdx <- rbp + 32*x
	shrl	$3, %ecx      # cl <- x
	# If x = 1, target value is the modulus (pointer to the current
	# modulus is at the start of the flag area, which is pointed to
	# by rdx in that case).
	cmp	$1, %cl
	jne	2f
	movq	(%rdx), %rdx
2:
	addq	%rbx, %rax    # rax <- translated address (also clears CF)

	# Call the opcode routine
	pushq	%rsi
	callq	*%rax
	popq	%rsi
	# Execute next instruction until the exit flag is set
	cmpb	$0, 48(%rbp)
	je	1b
.endm

# Wind down the interpreter. The stack, rbx and rbp are restored to the
# state when INTERPRETER_BEGIN was invoked. rax is set to the code exit
# status.
# Output: rax
# Clobbers: rbp
.macro	INTERPRETER_END
	# Retrieve exit status.
	xorl	%eax, %eax
	movb	49(%rbp), %al

	# Restore stack and saved registers.
	movq	40(%rbp), %rsp
	popq	%rbp
	popq	%r12
	popq	%rbx
.endm

# ========================================================================
# int tv_ecdsa_p256_verify(const void *sig, size_t sig_len,
#         const void *pub, size_t pub_len,
#         const void *hv, size_t hv_len)
# ========================================================================

# Small helper chunk located here so that some jumps are close.
Ltv_ecdsa_p256_verify__err:
	xorl	%eax, %eax
	ret

	.global	tv_ecdsa_p256_verify
	.type	tv_ecdsa_p256_verify, %function
tv_ecdsa_p256_verify:
	# Check input sizes.
	subq	$64, %rsi
	jnz	Ltv_ecdsa_p256_verify__err
	subq	$65, %rcx
	jnz	Ltv_ecdsa_p256_verify__err
	subq	$32, %r9
	cmpq	$32, %r9
	ja	Ltv_ecdsa_p256_verify__err

	# Check that the public key leading byte is 0x04.
	pushq	%rdx
	popq	%rsi
	lodsb
	cmpb	$0x04, %al
	jne	Ltv_ecdsa_p256_verify__err

	# We need to allocate the interpreter context; this will not
	# clobber r8, r9 or r10.
	movq	%rdi, %r9
	movq	%rsi, %r10
	# r8   hv
	# r9   sig
	# r10  pub+1

	INTERPRETER_BEGIN

	# rsi points to the bytecode; we save it for now.
	pushq	%rsi

	# Decode r, s, e, Qx and Qy into the appropriate slots.
	# This uses the fact that the slots are consecutive.
	# rbx contains the address of decode_int() (set by INTERPRETER_BEGIN).
	leaq	(32*_Kr)(%rbp), %rdi
	movq	%r9, %rsi
	callq	*%rbx        # r
	callq	*%rbx        # s
	movq	%r8, %rsi
	callq	*%rbx        # e
	movq	%r10, %rsi
	callq	*%rbx        # Qx
	callq	*%rbx        # Qy

	# We previously saved the bytecode address.
	popq	%rsi
	INTERPRETER_MAIN

	INTERPRETER_END
	# %eax was set according to the bytecode exit status
	ret
	.size	tv_ecdsa_p256_verify, . - tv_ecdsa_p256_verify

#ifdef TV_ECDSA_P256_TEST

# ========================================================================
# ========================================================================
# ========================================================================
# ###########################<<< TEST CODE >>>############################
#
# Everything below this line is test code which is used by external unit
# tests on individual functionalities such as modular multiplication; this
# is not meant to be compiled in released builds. When the
# TV_ECDSA_P256_TEST macro is not defined, this code is omitted.
# ========================================================================
# ========================================================================
# ========================================================================

# This code has no notion of "unreduced formats", so we return 0.
	.global	tv_gf_has_unreduced
	.type	tv_gf_has_unreduced, %function
tv_gf_has_unreduced:
	xorl	%eax, %eax
	ret
	.size	tv_gf_has_unreduced, . - tv_gf_has_unreduced

# Simple decode (implicit reduction).
	.global	tv_gf_decode
	.type	tv_gf_decode, %function
tv_gf_decode:
	xorl	%ecx, %ecx
	call	decode_int
	xorl	%eax, %eax
	movb	$1, %al
	ret
	.size	tv_gf_decode, . - tv_gf_decode

# This is not actually used since we do not really support an "unreduced"
# format.
	.global	tv_gf_check
	.type	tv_gf_check, %function
tv_gf_check:
	xorl	%eax, %eax
	movb	$1, %al
	ret
	.size	tv_gf_check, . - tv_gf_check

# For additions, subtractions, multiplications and inversion, we fire up
# an interpreter and use the relevant bytecode.

bytecode_add:
	_ADD _T0 ; _RET
bytecode_sub:
	_SUB _T0 ; _RET
bytecode_mul:
	_MUL _T0 ; _RET
bytecode_ok:
	_OK

# gf_op(gf *d, const gf *a, const gf *b, int scalar, const uint8_t *code)
	.type	gf_op, %function
gf_op:
	pushq	%r15
	movq	%rsp, %r15
	pushq	%rdi
	pushq	%rsi
	pushq	%rdx
	pushq	%rcx
	pushq	%r8

	INTERPRETER_BEGIN

	# Copy operands:
	#  - If a != NULL then this is an add, sub or mul; the two source
	#    operands go to the accumulator and value T0, respectively.
	#  - If a == NULL then this is an inversion or an encoding, *d is
	#    copied into the accumulator.
	xorl	%ecx, %ecx
	movq	%rbp, %rdi
	movq	-16(%r15), %rsi
	testq	%rsi, %rsi
	jz	Lgf_op__cont1
	# Copy a to accumulator
	movb	$32, %cl
	rep movsb
	# Copy b to T0
	leaq	(32*_T0)(%rbp), %rdi
	movq	-24(%r15), %rsi
	movb	$32, %cl
	rep movsb
	jmp	Lgf_op__cont2
Lgf_op__cont1:
	# Copy d to accumulator
	movq	-8(%r15), %rsi
	movb	$32, %cl
	rep movsb
Lgf_op__cont2:
	# Set modulus according to the 'scalar' argument.
	movl	-32(%r15), %eax
	leaq	mod_P(%rip), %rcx
	leaq	mod_N(%rip), %rdx
	testl	%eax, %eax
	cmovnz	%rdx, %rcx
	movq	%rcx, 32(%rbp)

	# Simulate a call, with a return pointer leading to bytecode_ok,
	# then use the provided code pointer.
	leaq	bytecode_ok(%rip), %rax
	pushq	%rax
	movq	-40(%r15), %rsi
	INTERPRETER_MAIN

	# Copy result into destination.
	movq	-8(%r15), %rdi
	movq	%rbp, %rsi
	xorl	%ecx, %ecx
	movb	$32, %cl
	rep movsb

	INTERPRETER_END

	movq	%r15, %rsp
	popq	%r15
	ret
	.size	gf_op, . - gf_op

# tv_gf_add() uses gf_op()
	.global	tv_gf_add
	.type	tv_gf_add, %function
tv_gf_add:
	leaq	bytecode_add(%rip), %r8
	jmp	gf_op
	.size	tv_gf_add, . - tv_gf_add

# tv_gf_sub() uses gf_op()
	.global	tv_gf_sub
	.type	tv_gf_sub, %function
tv_gf_sub:
	leaq	bytecode_sub(%rip), %r8
	jmp	gf_op
	.size	tv_gf_sub, . - tv_gf_sub

# tv_gf_mul() uses gf_op()
	.global	tv_gf_mul
	.type	tv_gf_mul, %function
tv_gf_mul:
	leaq	bytecode_mul(%rip), %r8
	jmp	gf_op
	.size	tv_gf_mul, . - tv_gf_mul

# tv_gf_invert() uses gf_op()
	.global	tv_gf_invert
	.type	tv_gf_invert, %function
tv_gf_invert:
	movq	%rsi, %rcx
	xorq	%rsi, %rsi
	xorq	%rdx, %rdx
	leaq	invert_mod(%rip), %r8
	jmp	gf_op
	.size	tv_gf_invert, . - tv_gf_invert

# tv_gf_encode()
	.global	tv_gf_encode
	.type	tv_gf_encode, %function
tv_gf_encode:
	pushq	%rbx
	pushq	%rdi
	pushq	%rsi
	subq	$32, %rsp

	# Set relevant modulus into rdx
	testl	%edx, %edx
	leaq	mod_N(%rip), %rax
	leaq	mod_P(%rip), %rdx
	cmovnz	%rax, %rdx

	# Copy value into rsp+0
	movq	%rsp, %rdi
	movq	32(%rsp), %rsi
	xorl	%ecx, %ecx
	movb	$32, %cl
	rep movsb

	# Subtract modulus until that triggers a borrow
Ltv_gf_encode__loop1:
	xorl	%ebx, %ebx
	movb	$8, %cl
Ltv_gf_encode__loop2:
	movl	(%rdx,%rbx,4), %eax
	sbbl	%eax, (%rsp,%rbx,4)
	incb	%bl
	decb	%cl
	jnz	Ltv_gf_encode__loop2
	jnc	Ltv_gf_encode__loop1

	# Add back the modulus since we got to a negative value
	xorl	%ebx, %ebx
	movb	$8, %cl
Ltv_gf_encode__loop3:
	movl	(%rdx,%rbx,4), %eax
	adcl	%eax, (%rsp,%rbx,4)
	incb	%bl
	decb	%cl
	jnz	Ltv_gf_encode__loop3

	# Copy value to destination, with byteswap (output is big-endian).
	popq	%rax
	popq	%rbx
	popq	%rcx
	popq	%rdx
	bswapq	%rax
	bswapq	%rbx
	bswapq	%rcx
	bswapq	%rdx
	popq	%rsi
	popq	%rdi
	movq	%rdx, (%rdi)
	movq	%rcx, 8(%rdi)
	movq	%rbx, 16(%rdi)
	movq	%rax, 24(%rdi)

	xorl	%eax, %eax
	movb	$1, %al
	popq	%rbx
	ret
	.size	tv_gf_encode, . - tv_gf_encode

# tv_point_decode()
	.global	tv_point_decode
	.type	tv_point_decode, %function
tv_point_decode:
	# Skip leading byte.
	incq	%rsi
	pushq	%r14
	pushq	%r15
	movq	%rsi, %r14
	movq	%rdi, %r15
	INTERPRETER_BEGIN

	# Decode coordinates as integers into slots Qx and Qy
	movq	%r14, %rsi
	leaq	(32*_Qx)(%rbp), %rdi
	callq	*%rbx      # rbx points to decode_int()
	callq	*%rbx

	# Set modulus to mod_P
	leaq	mod_P(%rip), %rax
	movq	%rax, 32(%rbp)

	# We mimick a _CALL to the check_point routine, and set back
	# the return address to a _OK.
	leaq	bytecode_ok(%rip), %rax
	pushq	%rax
	leaq	check_point(%rip), %rsi
	INTERPRETER_MAIN

	# Copy decoded x and y to destination P.X and P.Y; set P.Z to 1.
	movq	%r15, %rdi
	leaq	(32*_Qx)(%rbp), %rsi
	xorl	%ecx, %ecx
	movb	$64, %cl
	rep movsb
	xorl	%eax, %eax
	incb	%al
	stosq
	xorl	%eax, %eax
	stosq
	stosq
	stosq

	INTERPRETER_END
	popq	%r15
	popq	%r14
	ret
	.size	tv_point_decode, . - tv_point_decode

# tv_point_encode()
	.global	tv_point_encode
	.type	tv_point_encode, %function
tv_point_encode:
	pushq	%rdi
	pushq	%rsi
	subq	$64, %rsp

	# Copy Z coordinate to rsp+0
	movq	%rsp, %rdi
	leaq	64(%rsi), %rsi
	xorl	%ecx, %ecx
	movb	$32, %cl
	rep movsb
	# Invert Z
	movq	%rsp, %rdi
	xorl	%esi, %esi
	call	tv_gf_invert
	# Multiply 1/Z with Y, into rsp+32
	leaq	32(%rsp), %rdi
	movq	%rsp, %rsi
	movq	64(%rsp), %rdx
	addq	$32, %rdx
	xorl	%ecx, %ecx
	call	tv_gf_mul
	# Multiply 1/Z with X, into rsp
	movq	%rsp, %rdi
	movq	%rsp, %rsi
	movq	64(%rsp), %rdx
	xorl	%ecx, %ecx
	call	tv_gf_mul
	# Encode x and y into rsp+0 and rsp+32, respectively.
	movq	%rsp, %rdi
	movq	%rsp, %rsi
	xorl	%edx, %edx
	call	tv_gf_encode
	leaq	32(%rsp), %rdi
	leaq	32(%rsp), %rsi
	xorl	%edx, %edx
	call	tv_gf_encode
	# y is never zero for a curve point, since the curve has odd order.
	# If we still get a zero, then this must be because Z was zero
	# (which tv_gf_invert() "inverted" into zero), i.e. this was the
	# point-at-infinity.
	leaq	32(%rsp), %rdi
	xorl	%ecx, %ecx
	movb	$32, %cl
	xorl	%eax, %eax
	repe scasb
	jnz	Ltv_point_encode__cont
	addq	$72, %rsp
	popq	%rdi
	stosb
	movb	$1, %al
	ret
Ltv_point_encode__cont:
	# Non-infinity point.
	movq	72(%rsp), %rdi
	movb	$0x04, %al
	stosb
	movq	%rsp, %rsi
	movb	$64, %cl
	rep movsb
	addq	$80, %rsp
	movb	$65, %al
	ret
	.size	tv_point_encode, . - tv_point_encode

# tv_point_set_neutral()
	.global	tv_point_set_neutral
	.type	tv_point_set_neutral, %function
tv_point_set_neutral:
	# Clear all 120 useful bytes of the structure, then set Y to a
	# non-zero value.
	xorl	%eax, %eax
	xorl	%ecx, %ecx
	movb	$96, %cl
	rep stosb
	movb	$1, -64(%rdi)
	ret
	.size	tv_point_set_neutral, . - tv_point_set_neutral

# point_double(point *p1)                p1 <- 2*p1
# point_addto(point *p1, point *p2)      p1 <- p1 + p2
	.type	point_double, %function
point_double:
	pushq	%rdi
	popq	%rsi
point_addto:
	pushq	%r14
	pushq	%r15
	movq	%rsi, %r14
	movq	%rdi, %r15
	INTERPRETER_BEGIN

	# Copy source coordinates to _W* and _H*
	leaq	(32*_Wx)(%rbp), %rdi
	xorl	%ecx, %ecx
	movq	%r15, %rsi
	movb	$96, %cl
	rep movsb
	movq	%r14, %rsi
	movb	$96, %cl
	rep movsb

	# Set modulus to mod_P.
	leaq	mod_P(%rip), %rax
	movq	%rax, 32(%rbp)

	# We mimick a _CALL to the point_add_to_W routine, and set back
	# the return address to a _OK.
	leaq	bytecode_ok(%rip), %rax
	pushq	%rax
	leaq	point_add_to_W(%rip), %rsi
	INTERPRETER_MAIN

	# Copy resulting point to output.
	movq	%r15, %rdi
	leaq	(32*_Wx)(%rbp), %rsi
	xorl	%ecx, %ecx
	movb	$96, %cl
	rep movsb

	INTERPRETER_END
	popq	%r15
	popq	%r14
	ret
	.size	point_double, . - point_double

# tv_point_add()
	.global	tv_point_add
	.type	tv_point_add, %function
tv_point_add:
	subq	$96, %rsp
	pushq	%rdi
	pushq	%rsi
	# Copy p2 into stack buffer.
	movq	%rdx, %rsi
	leaq	16(%rsp), %rdi
	xorl	%ecx, %ecx
	movb	$96, %cl
	rep movsb
	# Add p1 to stack buffer.
	popq	%rsi
	leaq	8(%rsp), %rdi
	call	point_addto
	# Copy result to p3.
	popq	%rdi
	movq	%rsp, %rsi
	xorl	%ecx, %ecx
	movb	$96, %cl
	rep movsb
	addq	$96, %rsp
	ret
	.size	tv_point_add, . - tv_point_add

# tv_point_sub()
	.global	tv_point_sub
	.type	tv_point_sub, %function
tv_point_sub:
	subq	$96, %rsp
	pushq	%rdi
	pushq	%rsi
	# Copy p2 into stack buffer.
	movq	%rdx, %rsi
	leaq	16(%rsp), %rdi
	xorl	%ecx, %ecx
	movb	$96, %cl
	rep movsb
	# Negate Y coordinate of stack point.
	leaq	48(%rsp), %rdi
	leaq	gf_ZERO(%rip), %rsi
	movq	%rdi, %rdx
	xorl	%ecx, %ecx
	call	tv_gf_sub
	# Add p1 to stack buffer.
	popq	%rsi
	leaq	8(%rsp), %rdi
	call	point_addto
	# Copy result to p3.
	popq	%rdi
	movq	%rsp, %rsi
	xorl	%ecx, %ecx
	movb	$96, %cl
	rep movsb
	addq	$96, %rsp
	ret
	.size	tv_point_sub, . - tv_point_sub

	.align	8
gf_ZERO:
	.quad	0, 0, 0, 0

# ========================================================================
#endif

	# Special section to indicate that the stack is non-executable
	.section	".note.GNU-stack","",@progbits
