#if defined __linux || defined __linux__
#define _GNU_SOURCE
#endif
#include <stddef.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

#if defined __linux || defined __linux__
#include <sys/types.h>
#include <unistd.h>
#include <sched.h>
#endif

#include "ecdsa-p256-verify.h"

/* ====================================================================== */
/*
 * We embed a perfunctory SHA-256 implementation, both for reproducible
 * pseudorandom generation of test values, and to support use of test
 * vectors for ECDSA that use SHA-256 as hash function.
 */

static void
dec32be_x(uint32_t *d, size_t num, const void *src)
{
	const uint8_t *buf = src;
	for (size_t i = 0; i < num; i ++) {
		d[i] = ((uint32_t)buf[0] << 24)
			| ((uint32_t)buf[1] << 16)
			| ((uint32_t)buf[2] << 8)
			| (uint32_t)buf[3];
		buf += 4;
	}
}

static void
enc32be_x(void *dst, const uint32_t *val, size_t num)
{
	uint8_t *buf = dst;
	for (size_t i = 0; i < num; i ++) {
		uint32_t x = val[i];
		buf[0] = (uint8_t)(x >> 24);
		buf[1] = (uint8_t)(x >> 16);
		buf[2] = (uint8_t)(x >> 8);
		buf[3] = (uint8_t)x;
		buf += 4;
	}
}

typedef struct {
	unsigned char buf[64];
	uint64_t count;
	uint32_t val[8];
} sha256_context;

#define CH(X, Y, Z)    ((((Y) ^ (Z)) & (X)) ^ (Z))
#define MAJ(X, Y, Z)   (((Y) & (Z)) | (((Y) | (Z)) & (X)))

#define ROTR(x, n)    (((uint32_t)(x) << (32 - (n))) | ((uint32_t)(x) >> (n)))

#define BSG2_0(x)      (ROTR(x, 2) ^ ROTR(x, 13) ^ ROTR(x, 22))
#define BSG2_1(x)      (ROTR(x, 6) ^ ROTR(x, 11) ^ ROTR(x, 25))
#define SSG2_0(x)      (ROTR(x, 7) ^ ROTR(x, 18) ^ (uint32_t)((x) >> 3))
#define SSG2_1(x)      (ROTR(x, 17) ^ ROTR(x, 19) ^ (uint32_t)((x) >> 10))

static const uint32_t sha256_IV[8] = {
	0x6A09E667, 0xBB67AE85, 0x3C6EF372, 0xA54FF53A,
	0x510E527F, 0x9B05688C, 0x1F83D9AB, 0x5BE0CD19
};

static const uint32_t sha256_K[64] = {
	0x428A2F98, 0x71374491, 0xB5C0FBCF, 0xE9B5DBA5,
	0x3956C25B, 0x59F111F1, 0x923F82A4, 0xAB1C5ED5,
	0xD807AA98, 0x12835B01, 0x243185BE, 0x550C7DC3,
	0x72BE5D74, 0x80DEB1FE, 0x9BDC06A7, 0xC19BF174,
	0xE49B69C1, 0xEFBE4786, 0x0FC19DC6, 0x240CA1CC,
	0x2DE92C6F, 0x4A7484AA, 0x5CB0A9DC, 0x76F988DA,
	0x983E5152, 0xA831C66D, 0xB00327C8, 0xBF597FC7,
	0xC6E00BF3, 0xD5A79147, 0x06CA6351, 0x14292967,
	0x27B70A85, 0x2E1B2138, 0x4D2C6DFC, 0x53380D13,
	0x650A7354, 0x766A0ABB, 0x81C2C92E, 0x92722C85,
	0xA2BFE8A1, 0xA81A664B, 0xC24B8B70, 0xC76C51A3,
	0xD192E819, 0xD6990624, 0xF40E3585, 0x106AA070,
	0x19A4C116, 0x1E376C08, 0x2748774C, 0x34B0BCB5,
	0x391C0CB3, 0x4ED8AA4A, 0x5B9CCA4F, 0x682E6FF3,
	0x748F82EE, 0x78A5636F, 0x84C87814, 0x8CC70208,
	0x90BEFFFA, 0xA4506CEB, 0xBEF9A3F7, 0xC67178F2
};

static void
sha256_round(const unsigned char *buf, uint32_t *val)
{

#define SHA2_STEP(A, B, C, D, E, F, G, H, j)   do { \
		uint32_t T1, T2; \
		T1 = H + BSG2_1(E) + CH(E, F, G) + sha256_K[j] + w[j]; \
		T2 = BSG2_0(A) + MAJ(A, B, C); \
		D += T1; \
		H = T1 + T2; \
	} while (0)

	int i;
	uint32_t a, b, c, d, e, f, g, h;
	uint32_t w[64];

	dec32be_x(w, 16, buf);
	for (i = 16; i < 64; i ++) {
		w[i] = SSG2_1(w[i - 2]) + w[i - 7]
			+ SSG2_0(w[i - 15]) + w[i - 16];
	}
	a = val[0];
	b = val[1];
	c = val[2];
	d = val[3];
	e = val[4];
	f = val[5];
	g = val[6];
	h = val[7];
	for (i = 0; i < 64; i += 8) {
		SHA2_STEP(a, b, c, d, e, f, g, h, i + 0);
		SHA2_STEP(h, a, b, c, d, e, f, g, i + 1);
		SHA2_STEP(g, h, a, b, c, d, e, f, i + 2);
		SHA2_STEP(f, g, h, a, b, c, d, e, i + 3);
		SHA2_STEP(e, f, g, h, a, b, c, d, i + 4);
		SHA2_STEP(d, e, f, g, h, a, b, c, i + 5);
		SHA2_STEP(c, d, e, f, g, h, a, b, i + 6);
		SHA2_STEP(b, c, d, e, f, g, h, a, i + 7);
	}
	val[0] += a;
	val[1] += b;
	val[2] += c;
	val[3] += d;
	val[4] += e;
	val[5] += f;
	val[6] += g;
	val[7] += h;
}

static void
sha256_init(sha256_context *sc)
{
	memcpy(sc->val, sha256_IV, sizeof sha256_IV);
	sc->count = 0;
}

static void
sha256_update(sha256_context *sc, const void *data, size_t len)
{
	const unsigned char *buf;
	size_t ptr;

	buf = data;
	ptr = (size_t)sc->count & 63;
	sc->count += (uint64_t)len;
	while (len > 0) {
		size_t clen;

		clen = 64 - ptr;
		if (clen > len) {
			clen = len;
		}
		memcpy(sc->buf + ptr, buf, clen);
		ptr += clen;
		buf += clen;
		len -= clen;
		if (ptr == 64) {
			sha256_round(sc->buf, sc->val);
			ptr = 0;
		}
	}
}

static void
sha256_out(sha256_context *sc, void *dst)
{
	unsigned char buf[64];
	uint32_t val[8], tc[2];
	size_t ptr;

	ptr = (size_t)sc->count & 63;
	memcpy(buf, sc->buf, ptr);
	memcpy(val, sc->val, sizeof val);
	buf[ptr ++] = 0x80;
	if (ptr > 56) {
		memset(buf + ptr, 0, 64 - ptr);
		sha256_round(buf, val);
		memset(buf, 0, 56);
	} else {
		memset(buf + ptr, 0, 56 - ptr);
	}
	tc[0] = (uint32_t)(sc->count >> 29);
	tc[1] = (uint32_t)sc->count << 3;
	enc32be_x(buf + 56, tc, 2);
	sha256_round(buf, val);
	enc32be_x(dst, val, 8);
}

static size_t
hextobin(void *dst, size_t dst_len, const char *src)
{
	uint8_t *buf = (uint8_t *)dst;
	size_t j = 0;
	int acc = -1;
	while (*src != 0) {
		int c = *src ++;
		if (c == ' ' || c == ':') {
			continue;
		}
		if (c >= '0' && c <= '9') {
			c -= '0';
		} else if (c >= 'A' && c <= 'F') {
			c -= 'A' - 10;
		} else if (c >= 'a' && c <= 'f') {
			c -= 'a' - 10;
		} else {
			fprintf(stderr, "ERR: not hex character: $%08X\n", c);
			exit(EXIT_FAILURE);
		}
		if (acc < 0) {
			acc = c;
		} else {
			c += acc << 4;
			acc = -1;
			if (buf == NULL) {
				j ++;
			} else {
				if (j >= dst_len) {
					fprintf(stderr,
						"ERR: hextobin overflow\n");
					exit(EXIT_FAILURE);
				}
				buf[j ++] = (uint8_t)c;
			}
		}
	}
	if (acc >= 0) {
		fprintf(stderr, "ERR: odd number of hex digits\n");
		exit(EXIT_FAILURE);
	}
	return j;
}

#define HEXTOBIN(dst, src)   do { \
		if (hextobin(dst, sizeof(dst), src) != sizeof(dst)) { \
			fprintf(stderr, "ERR: hex output size mismatch\n"); \
			exit(EXIT_FAILURE); \
		} \
	} while (0)

static void
check_equals(const void *s1, const void *s2, size_t len, const char *banner)
{
	if (memcmp(s1, s2, len) == 0) {
		return;
	}
	fprintf(stderr, "ERR: %s\n", banner);
	for (size_t i = 0; i < len; i ++) {
		fprintf(stderr, "%02x", ((const uint8_t *)s1)[i]);
	}
	fprintf(stderr, "\n");
	for (size_t i = 0; i < len; i ++) {
		fprintf(stderr, "%02x", ((const uint8_t *)s2)[i]);
	}
	fprintf(stderr, "\n");
	exit(EXIT_FAILURE);
}

static void
test_sha256(void)
{
	printf("Test SHA-256: ");
	fflush(stdout);

	sha256_context sc;
	uint8_t tmp[1000];
	uint8_t ref[32], out[32];

	HEXTOBIN(ref, "ba7816bf8f01cfea414140de5dae2223b00361a396177a9cb410ff61f20015ad");
	sha256_init(&sc);
	sha256_update(&sc, "abc", 3);
	sha256_out(&sc, out);
	check_equals(ref, out, 32, "KAT 1");

	printf(".");
	fflush(stdout);

	HEXTOBIN(ref, "248d6a61d20638b8e5c026930c3e6039a33ce45964ff2167f6ecedd419db06c1");
	sha256_init(&sc);
	sha256_update(&sc, "abcdbcdecdefdefgefghfghighijhijkijkljklmklmnlmnomnopnopq", 56);
	sha256_out(&sc, out);
	check_equals(ref, out, 32, "KAT 2");

	printf(".");
	fflush(stdout);

	HEXTOBIN(ref, "cdc76e5c9914fb9281a1c7e284d73e67f1809a48a497200e046d39ccc7112cd0");
	sha256_init(&sc);
	memset(tmp, 'a', 1000);
	for (int i = 0; i < 1000; i ++) {
		sha256_update(&sc, tmp, 1000);
	}
	sha256_out(&sc, out);
	check_equals(ref, out, 32, "KAT 3");

	printf(".");
	fflush(stdout);

	printf(" done.\n");
	fflush(stdout);
}

#if defined TV_ECDSA_P256_TEST

/* ====================================================================== */
/*
 * UNIT TEST API
 *
 * This code exercises some internal functionalities such as computing
 * modular multiplication. In order to use this code, the tested code must
 * implement an extra API, documented here.
 */

/* An individual element from a field (coordinate or scalar) must fit in
   a 48-byte structure with 8-byte alignment (it can be smaller). */
typedef struct {
	uint64_t w[6];
} gf;

/* Return 1 if the implementation supports some internal "unreduced"
   format. If that function returns 1, then random field element generation
   will repeatedly add and subtract values until tv_gf_check() returns 0,
   thus exercising large range values. If tv_gf_has_unreduced() returns 0,
   then random element generation will only use a single call to
   tv_gf_decode(). */
int tv_gf_has_unreduced(void);

/* Check whether a value is "acceptable"; 1 is returned for acceptable values,
   0 otherwise. Field is the scalar field if 'scalar' is non-zero, the
   coordinate field otherwise. If the implementation does not support
   "unreduced" formats (tv_gf_has_unreduced() returns 0) then this function
   is not actually invoked at all (it must still be present so that the
   test binary can link).
   The notion of "acceptable" used here is that a call to one of the add,
   sub, mul or invert function on acceptable values should work properly. */
int tv_gf_check(const gf *x, int scalar);
 
/* Decode 32 bytes (src) into a field element. Input is unsigned and uses
   a big-endian encoding. The scalar field is used if 'scalar' is non-zero;
   otherwise, the coordinate field is used. The function may return 0 to
   indicate an unacceptable source, in case the decoding enforces strict
   range checking (the function may also use implicit reduction and accept
   any 32-byte input). */
int tv_gf_decode(gf *restrict d, const void *restrict src, int scalar);

/* Compute d <- a + b
   Field is the scalar field if 'scalar' is non-zero, the coordinate field
   otherwise.
   Source and destination operands need not be disjoint. */
void tv_gf_add(gf *d, const gf *a, const gf *b, int scalar);

/* Compute d <- a - b
   Field is the scalar field if 'scalar' is non-zero, the coordinate field
   otherwise.
   Source and destination operands need not be disjoint. */
void tv_gf_sub(gf *d, const gf *a, const gf *b, int scalar);

/* Compute d <- a*b
   Field is the scalar field if 'scalar' is non-zero, the coordinate field
   otherwise.
   Source and destination operands need not be disjoint. */
void tv_gf_mul(gf *d, const gf *a, const gf *b, int scalar);

/* Compute d <- 1/d
   Field is the scalar field if 'scalar' is non-zero, the coordinate field
   otherwise. */
void tv_gf_invert(gf *d, int scalar);

/* Encode the value into 32 bytes (unsigned big-endian convention).
   Field is the scalar field if 'scalar' is non-zero, the coordinate field
   otherwise. The function returns a non-zero value on success, or 0 on
   error; an error may be reported if the tv_gf_encode() detects an internal
   error with the value. */
int tv_gf_encode(void *dst, const gf *x, int scalar);

/* A curve point may use up to 192 bytes, with 8-byte alignment. */
typedef struct {
	uint64_t w[24];
} point;

/* Decode a curve point from the source. Returned value is 1 on success,
   0 on error. Source is in IEEE p1363 uncompressed format, and the
   caller guarantees that:
    - the first byte is 0x04
    - the point is not the point-at-infinity
    - the source total length is 65 bytes
   Decoding MUST enforce that the coordinates are canonical (both
   in [0,p-1]) and also check that the point is on the curve. */
int tv_point_decode(point *p, const void *src);

/* Encode a curve point into bytes, using IEEE p1363 uncompressed format
   (one byte for the point-at-infinity, 65 bytes for other points).
   The produced encoding size (in bytes) is returned. */
size_t tv_point_encode(void *dst, const point *p);

/* Point addition: P3 <- P1 + P2
   Source and destination operands need not be disjoint. */
void tv_point_add(point *p3, const point *p1, const point *p2);

/* Point addition: P3 <- P1 - P2
   Source and destination operands need not be disjoint. */
void tv_point_sub(point *p3, const point *p1, const point *p2);

/* Set point P to the neutral element (point-at-infinity). */
void tv_point_set_neutral(point *p);

/* ====================================================================== */

/*
 * For verifying operations, we implement some basic support of modular
 * arithmetics (in an inefficient but straightforward way).
 */

typedef struct {
	uint8_t w[32];
} z256;

/* d <- a + b, output carry is returned (1 on overflow, 0 otherwise). */
static int
z256_add(z256 *d, const z256 *a, const z256 *b)
{
	unsigned cc = 0;
	for (size_t i = 0; i < 32; i ++) {
		unsigned t = a->w[i] + b->w[i] + cc;
		d->w[i] = (uint8_t)t;
		cc = t >> 8;
	}
	return (int)cc;
}

/* d <- a + b, output borrow is returned (1 on overflow, 0 otherwise). */
static int
z256_sub(z256 *d, const z256 *a, const z256 *b)
{
	int cc = 0;
	for (size_t i = 0; i < 32; i ++) {
		int t = a->w[i] - b->w[i] + cc;
		d->w[i] = (uint8_t)t;
		cc = t >> 8;
	}
	return cc & 1;
}

/* d <- a + b mod m
   If inputs are in [0,m-1] then output is in [0,m-1]. */
static void
m256_add(z256 *d, const z256 *a, const z256 *b, const z256 *m)
{
	z256 t;
	int cc1 = z256_add(d, a, b);
	int cc2 = z256_sub(&t, d, m);
	if (cc1 == cc2) {
		*d = t;
	}
}

/* d <- a - b mod m
   If inputs are in [0,m-1] then output is in [0,m-1]. */
static void
m256_sub(z256 *d, const z256 *a, const z256 *b, const z256 *m)
{
	if (z256_sub(d, a, b)) {
		z256_add(d, d, m);
	}
}

/* d <- a * b mod m
   If inputs are in [0,m-1] then output is in [0,m-1]. */
static void
m256_mul(z256 *d, const z256 *a, const z256 *b, const z256 *m)
{
	z256 t;
	memset(t.w, 0, sizeof t.w);
	for (int i = 255; i >= 0; i --) {
		m256_add(&t, &t, &t, m);
		if (((b->w[i >> 3] >> (i & 7)) & 1) != 0) {
			m256_add(&t, &t, a, m);
		}
	}
	*d = t;
}

/* Encode a 256-bit integer into 32 bytes (unsigned, big-endian). */
static void
z256_encode(void *dst, const z256 *x)
{
	uint8_t *buf = dst;
	for (int i = 0; i < 32; i ++) {
		buf[i] = x->w[31 - i];
	}
}

static const z256 mod_p = {
	{ 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF,
	  0xFF, 0xFF, 0xFF, 0xFF, 0x00, 0x00, 0x00, 0x00,
	  0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
	  0x01, 0x00, 0x00, 0x00, 0xFF, 0xFF, 0xFF, 0xFF, }
};

static const z256 mod_n = {
	{ 0x51, 0x25, 0x63, 0xFC, 0xC2, 0xCA, 0xB9, 0xF3,
	  0x84, 0x9E, 0x17, 0xA7, 0xAD, 0xFA, 0xE6, 0xBC,
	  0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF,
	  0x00, 0x00, 0x00, 0x00, 0xFF, 0xFF, 0xFF, 0xFF, }
};

/* Make a (pseudo)random field element from the provided seed. The
   generated element is stored both in *x and *z. */
static void
rand_gf(gf *x, z256 *z, uint32_t seed, int scalar)
{
	const z256 *m = scalar ? &mod_n : &mod_p;
	for (uint32_t k = 0;; k ++) {
		gf y;
		z256 v;
		/* Make a random value by decoding 32 random bytes.
		   We try again if the implementation says that the value
		   is not acceptable (this is expected to be a quite rare
		   occurrence since the moduli are close to 2^256). */
		for (uint32_t c = 0;; c ++) {
			sha256_context sc;
			uint8_t tmp[32];
			enc32be_x(tmp, &seed, 1);
			enc32be_x(tmp + 4, &k, 1);
			enc32be_x(tmp + 8, &c, 1);
			sha256_init(&sc);
			sha256_update(&sc, tmp, 12);
			sha256_out(&sc, tmp);
			if (!tv_gf_decode(&y, tmp, scalar)) {
				continue;
			}
			for (int i = 0; i < 32; i ++) {
				v.w[i] = tmp[31 - i];
			}
			break;
		}

		/* If the code does not use an "unreduced" format then
		   one pseudorandom value is enough; otherwise, we keep
		   adding and subtracting values until the tv_gf_check()
		   function tells us to stop. */
		if (k == 0) {
			*x = y;
			*z = v;
			if (!tv_gf_has_unreduced()) {
				return;
			}
		} else {
			if ((k & 1) == 0) {
				tv_gf_add(&y, &y, x, scalar);
				m256_add(&v, &v, z, m);
			} else {
				tv_gf_sub(&y, &y, x, scalar);
				m256_sub(&v, &v, z, m);
			}
			if (!tv_gf_check(&y, scalar)) {
				return;
			}
			*x = y;
			*z = v;
		}
	}
}

static void
inner_test_gf(int scalar)
{
	printf("Test field (%s): ", scalar ? "scalars" : "coordinates");
	fflush(stdout);

	const z256 *m = scalar ? &mod_n : &mod_p;
	for (unsigned i = 0; i < 300; i ++) {
		gf xa, xb, xc;
		z256 za, zb, zc;
		uint8_t tmp1[32], tmp2[32];

		/* Generate a random value (xa, za) */
		rand_gf(&xa, &za, (i << 2) + 0, scalar);

		/* Verify that we can re-encode it properly. */
		tv_gf_encode(tmp1, &xa, scalar);
		z256_encode(tmp2, &za);
		check_equals(tmp1, tmp2, 32, "rand(a)");

		/* Generate a random value (xb, zb) */
		rand_gf(&xb, &zb, (i << 2) + 1, scalar);

		/* Verify that we can re-encode it properly. */
		tv_gf_encode(tmp1, &xb, scalar);
		z256_encode(tmp2, &zb);
		check_equals(tmp1, tmp2, 32, "rand(b)");

		/* Check addition. */
		tv_gf_add(&xc, &xa, &xb, scalar);
		if (!tv_gf_encode(tmp1, &xc, scalar)) {
			fprintf(stderr, "internal error encode (1)\n");
			exit(EXIT_FAILURE);
		}
		m256_add(&zc, &za, &zb, m);
		z256_encode(tmp2, &zc);
		check_equals(tmp1, tmp2, 32, "add");

		/* Check subtraction. */
		tv_gf_sub(&xc, &xa, &xb, scalar);
		if (!tv_gf_encode(tmp1, &xc, scalar)) {
			fprintf(stderr, "internal error encode (2)\n");
			exit(EXIT_FAILURE);
		}
		m256_sub(&zc, &za, &zb, m);
		z256_encode(tmp2, &zc);
		check_equals(tmp1, tmp2, 32, "sub");

		/* Check multiplication. */
		tv_gf_mul(&xc, &xa, &xb, scalar);
		if (!tv_gf_encode(tmp1, &xc, scalar)) {
			fprintf(stderr, "internal error encode (3)\n");
			exit(EXIT_FAILURE);
		}
		m256_mul(&zc, &za, &zb, m);
		z256_encode(tmp2, &zc);
		check_equals(tmp1, tmp2, 32, "mul");

		/* Check inversion. */
		xc = xa;
		tv_gf_invert(&xa, scalar);
		tv_gf_mul(&xc, &xc, &xa, scalar);
		if (!tv_gf_encode(tmp1, &xc, scalar)) {
			fprintf(stderr, "internal error encode (3)\n");
			exit(EXIT_FAILURE);
		}
		memset(tmp2, 0, 31);
		tmp2[31] = 1;
		check_equals(tmp1, tmp2, 32, "inv");

		printf(".");
		fflush(stdout);
	}

	printf(" done.\n");
	fflush(stdout);
}

static void
test_gf_coordinates(void)
{
	inner_test_gf(0);
}

static void
test_gf_scalars(void)
{
	inner_test_gf(1);
}

static int
point_equals(const point *p1, const point *p2)
{
	/* We could also compute p3 = p1 - p2, and encode only that
	   point, but this function is designed to test that the
	   point addition is properly implemented, so we should
	   avoid using point addition here. */
	uint8_t buf1[65], buf2[65];
	size_t len1 = tv_point_encode(buf1, p1);
	size_t len2 = tv_point_encode(buf2, p2);
	return len1 == len2 && memcmp(buf1, buf2, len1) == 0;
}

static void
check_point_equals(const point *p1, const point *p2, const char *banner)
{
	uint8_t buf1[65], buf2[65];
	size_t len1 = tv_point_encode(buf1, p1);
	size_t len2 = tv_point_encode(buf2, p2);
	if (len1 == len2 && memcmp(buf1, buf2, len1) == 0) {
		return;
	}
	fprintf(stderr, "ERR %s\n", banner);
	for (size_t i = 0; i < len1; i ++) {
		fprintf(stderr, "%02x", buf1[i]);
	}
	fprintf(stderr, "\n");
	for (size_t i = 0; i < len2; i ++) {
		fprintf(stderr, "%02x", buf2[i]);
	}
	fprintf(stderr, "\n");
	exit(EXIT_FAILURE);
}

static void
check_point_encode_equals(const point *p, const uint8_t *ref,
	const char *banner)
{
	uint8_t tmp[65];
	size_t len = tv_point_encode(tmp, p);
	size_t rlen = (ref[0] == 0) ? 1 : 65;
	if (len == rlen && memcmp(ref, tmp, len) == 0) {
		return;
	}
	fprintf(stderr, "ERR %s\n", banner);
	for (size_t i = 0; i < len; i ++) {
		fprintf(stderr, "%02x", tmp[i]);
	}
	fprintf(stderr, "\n");
	for (size_t i = 0; i < rlen; i ++) {
		fprintf(stderr, "%02x", ref[i]);
	}
	fprintf(stderr, "\n");
	exit(EXIT_FAILURE);
}

static void
test_p256_basic(void)
{
	printf("Test P-256 (basic): ");
	fflush(stdout);

	/* For a randomly generated point P, these are points i*P for
	   i = 0 to 6. */
	static const char *const KAT_PP[] = {
		"00",
		"04dc6080c0afd210c8f1ddb7a4e76b65b7fd4c24b256dc61d4c29c0e7900ab1b541e9f9b0cb8ffc6a0675c8d6b7dfec6dbb03ff3b1fecfb28bef6f899e99c6697e",
		"0432ebe142fee6af09801816dd514e2b9cc865676f3a7ce76b4a208b3a761a39abc5fd25d9ed7231e6355b0609c2d55da6465e52c289932b6745fb4d75689d8246",
		"048c8008ff09755e57a90c6b7f8c98a12b2e6d5040dd1ce875cb6b0ea171cc0fb7189b5d5a32bdc5a0267833e920cd90a06cd1ff6924abe2ada7864185de60f2f4",
		"04d00b82bf74e907b05a73732db74bb119428762feb3f2b7d07622f715a5a4efa70e0f87720f7e281ca0afe208b051e1bccb2bd99cdf3a545a0402e5c73120e768",
		"047b1e62d9dc3565ed73080b6bdb0a82254a13be8a3295fd89d110fb55fee9b714a21f1167987110c2267f923872de0b9baca01fc0d9353178d2a889b4f89b841a",
		"04c6a7100a44b0833de9f9b8b623abd2238e31af478e6cb1bbf8604b368e2618ab31d1748b30e825f8de354376f422b769fa9c5522d91ae5f557bca2b74dd5a4f0",
		NULL
	};

	point pp[7];
	for (int i = 0; i <= 6; i ++) {
		uint8_t tmp[65];
		size_t len = hextobin(tmp, sizeof tmp, KAT_PP[i]);
		if (len == 1) {
			tv_point_set_neutral(&pp[i]);
		} else {
			if (!tv_point_decode(&pp[i], tmp)) {
				fprintf(stderr, "ERR decode point %d\n", i);
				exit(EXIT_FAILURE);
			}
		}
		check_point_encode_equals(&pp[i], tmp, "dec/enc");
		if (i > 0) {
			if (point_equals(&pp[i], &pp[i - 1])) {
				fprintf(stderr, "ERR equals(1) %d\n", i);
				exit(EXIT_FAILURE);
			}
		}
		printf(".");
		fflush(stdout);
	}

	printf(" ");
	fflush(stdout);

	point qq[7];
	tv_point_sub(&qq[0], &pp[4], &pp[4]);
	check_point_equals(&qq[0], &pp[0], "sub0");
	tv_point_add(&qq[1], &qq[0], &pp[1]);
	check_point_equals(&qq[1], &pp[1], "add1");
	for (int i = 2; i <= 6; i ++) {
		char banner[10];
		sprintf(banner, "add%d", i);
		tv_point_add(&qq[i], &qq[i - 1], &qq[1]);
		check_point_equals(&qq[i], &pp[i], banner);
		printf(".");
		fflush(stdout);
	}

	printf(" ");
	fflush(stdout);

	for (int k = 0; k <= 6; k ++) {
		for (int i = 0; i <= k; i ++) {
			int j = k - i;
			char banner[15];
			sprintf(banner, "add(%d,%d)", i, j);
			point r;
			tv_point_add(&r, &qq[i], &qq[j]);
			check_point_equals(&r, &pp[k], banner);
		}
		printf(".");
		fflush(stdout);
	}

	printf(" done.\n");
	fflush(stdout);
}

#endif   /* End of unit tests of inner functions. */

/* Each group of five values is:
     test identifer (symbolic string)
     public key (up to 65 bytes) (correct size is 65)
     message (up to 20 bytes)
     signature (up to 82 bytes) (correct size is 64)
     validity (G for "good", F for "failed")
   All tests use SHA-256 as hash function.
   There are 492 test vectors in total. */
static const char *const KAT_ECDSA_P256_SHA256_VERIFY[] = {
	/* From Wycheproof: https://github.com/C2SP/wycheproof/
	   Vectors are:
	    - testvectors_v1/ecdsa_secp256r1_sha256_p1363_test.json, as of
	      commit e0df04e0c033f2d25c5051dd06230336c7822358 (2025-10-07).
	    - testvectors_v1/ecdsa_secp256r1_sha256_test.json, as of
	      commit 0fd0ec1cf2114f456f5c3e7c61ba807fb1311b45 (2026-01-19).
	   In the latter file, about half of the tests are about ASN.1/DER
	   encoding of the signature. Since this implementation uses the
	   "p1363" encoding (r and s in unsigned big-endian, 32 bytes each,
	   concatenated), all signatures have been reencoded in the p1363
	   format, and tests that exercise specific DER misencodings have
	   been removed. */

	/* ecdsa_secp256r1_sha256_p1363_test.json - 1 */
	"ecdsa_secp256r1_sha256_p1363_test.json - 1",
	"042927b10512bae3eddcfe467828128bad2903269919f7086069c8c4df6c732838c7787964eaac00e5921fb1498a60f4606766b3d9685001558d1a974e7341513e",
	"313233343030",
	"2ba3a8be6b94d5ec80a6d9d1190a436effe50d85a1eee859b8cc6af9bd5c2e184cd60b855d442f5b3c7b11eb6c4e0ae7525fe710fab9aa7c77a67f79e6fadd76",
	"G",

	/* ecdsa_secp256r1_sha256_p1363_test.json - 2 */
	"ecdsa_secp256r1_sha256_p1363_test.json - 2",
	"042927b10512bae3eddcfe467828128bad2903269919f7086069c8c4df6c732838c7787964eaac00e5921fb1498a60f4606766b3d9685001558d1a974e7341513e",
	"313233343030",
	"012ba3a8bd6b94d5ed80a6d9d1190a436ebccc0833490686deac8635bcb9bf536900b329f479a2bbd0a5c384ee1493b1f5186a87139cac5df4087c134b49156847db",
	"F",

	/* ecdsa_secp256r1_sha256_p1363_test.json - 3 */
	"ecdsa_secp256r1_sha256_p1363_test.json - 3",
	"042927b10512bae3eddcfe467828128bad2903269919f7086069c8c4df6c732838c7787964eaac00e5921fb1498a60f4606766b3d9685001558d1a974e7341513e",
	"313233343030",
	"01002ba3a7be6b94d6ec80a6d9d1190a432be6dfbb2cb98d6d4d72972df620817f180000b329f479a2bbd0a5c384ee1493b1f5186a87139cac5df4087c134b49156847db",
	"F",

	/* ecdsa_secp256r1_sha256_p1363_test.json - 4 */
	"ecdsa_secp256r1_sha256_p1363_test.json - 4",
	"042927b10512bae3eddcfe467828128bad2903269919f7086069c8c4df6c732838c7787964eaac00e5921fb1498a60f4606766b3d9685001558d1a974e7341513e",
	"313233343030",
	"d45c5740946b2a147f59262ee6f5bc90bd01ed280528b62b3aed5fc93f06f739b329f479a2bbd0a5c384ee1493b1f5186a87139cac5df4087c134b49156847db",
	"F",

	/* ecdsa_secp256r1_sha256_p1363_test.json - 5 */
	"ecdsa_secp256r1_sha256_p1363_test.json - 5",
	"042927b10512bae3eddcfe467828128bad2903269919f7086069c8c4df6c732838c7787964eaac00e5921fb1498a60f4606766b3d9685001558d1a974e7341513e",
	"313233343030",
	"012ba3a8be6b94d5ec80a6d9d1190a436effe50d85a1eee859b8cc6af9bd5c2e1800b329f479a2bbd0a5c384ee1493b1f5186a87139cac5df4087c134b49156847db",
	"F",

	/* ecdsa_secp256r1_sha256_p1363_test.json - 6 */
	"ecdsa_secp256r1_sha256_p1363_test.json - 6",
	"042927b10512bae3eddcfe467828128bad2903269919f7086069c8c4df6c732838c7787964eaac00e5921fb1498a60f4606766b3d9685001558d1a974e7341513e",
	"313233343030",
	"0100000000000000002ba3a8be6b94d5ec80a6d9d1190a436effe50d85a1eee859b8cc6af9bd5c2e18000000000000000000b329f479a2bbd0a5c384ee1493b1f5186a87139cac5df4087c134b49156847db",
	"F",

	/* ecdsa_secp256r1_sha256_p1363_test.json - 7 */
	"ecdsa_secp256r1_sha256_p1363_test.json - 7",
	"042927b10512bae3eddcfe467828128bad2903269919f7086069c8c4df6c732838c7787964eaac00e5921fb1498a60f4606766b3d9685001558d1a974e7341513e",
	"313233343030",
	"01b329f478a2bbd0a6c384ee1493b1f518276e0e4a5375928d6fcd160c11cb6d2c00b329f479a2bbd0a5c384ee1493b1f5186a87139cac5df4087c134b49156847db",
	"F",

	/* ecdsa_secp256r1_sha256_p1363_test.json - 8 */
	"ecdsa_secp256r1_sha256_p1363_test.json - 8",
	"042927b10512bae3eddcfe467828128bad2903269919f7086069c8c4df6c732838c7787964eaac00e5921fb1498a60f4606766b3d9685001558d1a974e7341513e",
	"313233343030",
	"0100b329f379a2bbd1a5c384ee1493b1f4d55181c143c3fc78fc35de0e45788d98db0000b329f479a2bbd0a5c384ee1493b1f5186a87139cac5df4087c134b49156847db",
	"F",

	/* ecdsa_secp256r1_sha256_p1363_test.json - 9 */
	"ecdsa_secp256r1_sha256_p1363_test.json - 9",
	"042927b10512bae3eddcfe467828128bad2903269919f7086069c8c4df6c732838c7787964eaac00e5921fb1498a60f4606766b3d9685001558d1a974e7341513e",
	"313233343030",
	"01b329f479a2bbd0a5c384ee1493b1f5186a87139cac5df4087c134b49156847db00b329f479a2bbd0a5c384ee1493b1f5186a87139cac5df4087c134b49156847db",
	"F",

	/* ecdsa_secp256r1_sha256_p1363_test.json - 10 */
	"ecdsa_secp256r1_sha256_p1363_test.json - 10",
	"042927b10512bae3eddcfe467828128bad2903269919f7086069c8c4df6c732838c7787964eaac00e5921fb1498a60f4606766b3d9685001558d1a974e7341513e",
	"313233343030",
	"010000000000000000b329f479a2bbd0a5c384ee1493b1f5186a87139cac5df4087c134b49156847db000000000000000000b329f479a2bbd0a5c384ee1493b1f5186a87139cac5df4087c134b49156847db",
	"F",

	/* ecdsa_secp256r1_sha256_p1363_test.json - 11 */
	"ecdsa_secp256r1_sha256_p1363_test.json - 11",
	"042927b10512bae3eddcfe467828128bad2903269919f7086069c8c4df6c732838c7787964eaac00e5921fb1498a60f4606766b3d9685001558d1a974e7341513e",
	"313233343030",
	"00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000",
	"F",

	/* ecdsa_secp256r1_sha256_p1363_test.json - 12 */
	"ecdsa_secp256r1_sha256_p1363_test.json - 12",
	"042927b10512bae3eddcfe467828128bad2903269919f7086069c8c4df6c732838c7787964eaac00e5921fb1498a60f4606766b3d9685001558d1a974e7341513e",
	"313233343030",
	"00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000001",
	"F",

	/* ecdsa_secp256r1_sha256_p1363_test.json - 13 */
	"ecdsa_secp256r1_sha256_p1363_test.json - 13",
	"042927b10512bae3eddcfe467828128bad2903269919f7086069c8c4df6c732838c7787964eaac00e5921fb1498a60f4606766b3d9685001558d1a974e7341513e",
	"313233343030",
	"0000000000000000000000000000000000000000000000000000000000000000ffffffff00000000ffffffffffffffffbce6faada7179e84f3b9cac2fc632551",
	"F",

	/* ecdsa_secp256r1_sha256_p1363_test.json - 14 */
	"ecdsa_secp256r1_sha256_p1363_test.json - 14",
	"042927b10512bae3eddcfe467828128bad2903269919f7086069c8c4df6c732838c7787964eaac00e5921fb1498a60f4606766b3d9685001558d1a974e7341513e",
	"313233343030",
	"0000000000000000000000000000000000000000000000000000000000000000ffffffff00000000ffffffffffffffffbce6faada7179e84f3b9cac2fc632550",
	"F",

	/* ecdsa_secp256r1_sha256_p1363_test.json - 15 */
	"ecdsa_secp256r1_sha256_p1363_test.json - 15",
	"042927b10512bae3eddcfe467828128bad2903269919f7086069c8c4df6c732838c7787964eaac00e5921fb1498a60f4606766b3d9685001558d1a974e7341513e",
	"313233343030",
	"0000000000000000000000000000000000000000000000000000000000000000ffffffff00000000ffffffffffffffffbce6faada7179e84f3b9cac2fc632552",
	"F",

	/* ecdsa_secp256r1_sha256_p1363_test.json - 16 */
	"ecdsa_secp256r1_sha256_p1363_test.json - 16",
	"042927b10512bae3eddcfe467828128bad2903269919f7086069c8c4df6c732838c7787964eaac00e5921fb1498a60f4606766b3d9685001558d1a974e7341513e",
	"313233343030",
	"0000000000000000000000000000000000000000000000000000000000000000ffffffff00000001000000000000000000000000ffffffffffffffffffffffff",
	"F",

	/* ecdsa_secp256r1_sha256_p1363_test.json - 17 */
	"ecdsa_secp256r1_sha256_p1363_test.json - 17",
	"042927b10512bae3eddcfe467828128bad2903269919f7086069c8c4df6c732838c7787964eaac00e5921fb1498a60f4606766b3d9685001558d1a974e7341513e",
	"313233343030",
	"0000000000000000000000000000000000000000000000000000000000000000ffffffff00000001000000000000000000000001000000000000000000000000",
	"F",

	/* ecdsa_secp256r1_sha256_p1363_test.json - 18 */
	"ecdsa_secp256r1_sha256_p1363_test.json - 18",
	"042927b10512bae3eddcfe467828128bad2903269919f7086069c8c4df6c732838c7787964eaac00e5921fb1498a60f4606766b3d9685001558d1a974e7341513e",
	"313233343030",
	"00000000000000000000000000000000000000000000000000000000000000010000000000000000000000000000000000000000000000000000000000000000",
	"F",

	/* ecdsa_secp256r1_sha256_p1363_test.json - 19 */
	"ecdsa_secp256r1_sha256_p1363_test.json - 19",
	"042927b10512bae3eddcfe467828128bad2903269919f7086069c8c4df6c732838c7787964eaac00e5921fb1498a60f4606766b3d9685001558d1a974e7341513e",
	"313233343030",
	"00000000000000000000000000000000000000000000000000000000000000010000000000000000000000000000000000000000000000000000000000000001",
	"F",

	/* ecdsa_secp256r1_sha256_p1363_test.json - 20 */
	"ecdsa_secp256r1_sha256_p1363_test.json - 20",
	"042927b10512bae3eddcfe467828128bad2903269919f7086069c8c4df6c732838c7787964eaac00e5921fb1498a60f4606766b3d9685001558d1a974e7341513e",
	"313233343030",
	"0000000000000000000000000000000000000000000000000000000000000001ffffffff00000000ffffffffffffffffbce6faada7179e84f3b9cac2fc632551",
	"F",

	/* ecdsa_secp256r1_sha256_p1363_test.json - 21 */
	"ecdsa_secp256r1_sha256_p1363_test.json - 21",
	"042927b10512bae3eddcfe467828128bad2903269919f7086069c8c4df6c732838c7787964eaac00e5921fb1498a60f4606766b3d9685001558d1a974e7341513e",
	"313233343030",
	"0000000000000000000000000000000000000000000000000000000000000001ffffffff00000000ffffffffffffffffbce6faada7179e84f3b9cac2fc632550",
	"F",

	/* ecdsa_secp256r1_sha256_p1363_test.json - 22 */
	"ecdsa_secp256r1_sha256_p1363_test.json - 22",
	"042927b10512bae3eddcfe467828128bad2903269919f7086069c8c4df6c732838c7787964eaac00e5921fb1498a60f4606766b3d9685001558d1a974e7341513e",
	"313233343030",
	"0000000000000000000000000000000000000000000000000000000000000001ffffffff00000000ffffffffffffffffbce6faada7179e84f3b9cac2fc632552",
	"F",

	/* ecdsa_secp256r1_sha256_p1363_test.json - 23 */
	"ecdsa_secp256r1_sha256_p1363_test.json - 23",
	"042927b10512bae3eddcfe467828128bad2903269919f7086069c8c4df6c732838c7787964eaac00e5921fb1498a60f4606766b3d9685001558d1a974e7341513e",
	"313233343030",
	"0000000000000000000000000000000000000000000000000000000000000001ffffffff00000001000000000000000000000000ffffffffffffffffffffffff",
	"F",

	/* ecdsa_secp256r1_sha256_p1363_test.json - 24 */
	"ecdsa_secp256r1_sha256_p1363_test.json - 24",
	"042927b10512bae3eddcfe467828128bad2903269919f7086069c8c4df6c732838c7787964eaac00e5921fb1498a60f4606766b3d9685001558d1a974e7341513e",
	"313233343030",
	"0000000000000000000000000000000000000000000000000000000000000001ffffffff00000001000000000000000000000001000000000000000000000000",
	"F",

	/* ecdsa_secp256r1_sha256_p1363_test.json - 25 */
	"ecdsa_secp256r1_sha256_p1363_test.json - 25",
	"042927b10512bae3eddcfe467828128bad2903269919f7086069c8c4df6c732838c7787964eaac00e5921fb1498a60f4606766b3d9685001558d1a974e7341513e",
	"313233343030",
	"ffffffff00000000ffffffffffffffffbce6faada7179e84f3b9cac2fc6325510000000000000000000000000000000000000000000000000000000000000000",
	"F",

	/* ecdsa_secp256r1_sha256_p1363_test.json - 26 */
	"ecdsa_secp256r1_sha256_p1363_test.json - 26",
	"042927b10512bae3eddcfe467828128bad2903269919f7086069c8c4df6c732838c7787964eaac00e5921fb1498a60f4606766b3d9685001558d1a974e7341513e",
	"313233343030",
	"ffffffff00000000ffffffffffffffffbce6faada7179e84f3b9cac2fc6325510000000000000000000000000000000000000000000000000000000000000001",
	"F",

	/* ecdsa_secp256r1_sha256_p1363_test.json - 27 */
	"ecdsa_secp256r1_sha256_p1363_test.json - 27",
	"042927b10512bae3eddcfe467828128bad2903269919f7086069c8c4df6c732838c7787964eaac00e5921fb1498a60f4606766b3d9685001558d1a974e7341513e",
	"313233343030",
	"ffffffff00000000ffffffffffffffffbce6faada7179e84f3b9cac2fc632551ffffffff00000000ffffffffffffffffbce6faada7179e84f3b9cac2fc632551",
	"F",

	/* ecdsa_secp256r1_sha256_p1363_test.json - 28 */
	"ecdsa_secp256r1_sha256_p1363_test.json - 28",
	"042927b10512bae3eddcfe467828128bad2903269919f7086069c8c4df6c732838c7787964eaac00e5921fb1498a60f4606766b3d9685001558d1a974e7341513e",
	"313233343030",
	"ffffffff00000000ffffffffffffffffbce6faada7179e84f3b9cac2fc632551ffffffff00000000ffffffffffffffffbce6faada7179e84f3b9cac2fc632550",
	"F",

	/* ecdsa_secp256r1_sha256_p1363_test.json - 29 */
	"ecdsa_secp256r1_sha256_p1363_test.json - 29",
	"042927b10512bae3eddcfe467828128bad2903269919f7086069c8c4df6c732838c7787964eaac00e5921fb1498a60f4606766b3d9685001558d1a974e7341513e",
	"313233343030",
	"ffffffff00000000ffffffffffffffffbce6faada7179e84f3b9cac2fc632551ffffffff00000000ffffffffffffffffbce6faada7179e84f3b9cac2fc632552",
	"F",

	/* ecdsa_secp256r1_sha256_p1363_test.json - 30 */
	"ecdsa_secp256r1_sha256_p1363_test.json - 30",
	"042927b10512bae3eddcfe467828128bad2903269919f7086069c8c4df6c732838c7787964eaac00e5921fb1498a60f4606766b3d9685001558d1a974e7341513e",
	"313233343030",
	"ffffffff00000000ffffffffffffffffbce6faada7179e84f3b9cac2fc632551ffffffff00000001000000000000000000000000ffffffffffffffffffffffff",
	"F",

	/* ecdsa_secp256r1_sha256_p1363_test.json - 31 */
	"ecdsa_secp256r1_sha256_p1363_test.json - 31",
	"042927b10512bae3eddcfe467828128bad2903269919f7086069c8c4df6c732838c7787964eaac00e5921fb1498a60f4606766b3d9685001558d1a974e7341513e",
	"313233343030",
	"ffffffff00000000ffffffffffffffffbce6faada7179e84f3b9cac2fc632551ffffffff00000001000000000000000000000001000000000000000000000000",
	"F",

	/* ecdsa_secp256r1_sha256_p1363_test.json - 32 */
	"ecdsa_secp256r1_sha256_p1363_test.json - 32",
	"042927b10512bae3eddcfe467828128bad2903269919f7086069c8c4df6c732838c7787964eaac00e5921fb1498a60f4606766b3d9685001558d1a974e7341513e",
	"313233343030",
	"ffffffff00000000ffffffffffffffffbce6faada7179e84f3b9cac2fc6325500000000000000000000000000000000000000000000000000000000000000000",
	"F",

	/* ecdsa_secp256r1_sha256_p1363_test.json - 33 */
	"ecdsa_secp256r1_sha256_p1363_test.json - 33",
	"042927b10512bae3eddcfe467828128bad2903269919f7086069c8c4df6c732838c7787964eaac00e5921fb1498a60f4606766b3d9685001558d1a974e7341513e",
	"313233343030",
	"ffffffff00000000ffffffffffffffffbce6faada7179e84f3b9cac2fc6325500000000000000000000000000000000000000000000000000000000000000001",
	"F",

	/* ecdsa_secp256r1_sha256_p1363_test.json - 34 */
	"ecdsa_secp256r1_sha256_p1363_test.json - 34",
	"042927b10512bae3eddcfe467828128bad2903269919f7086069c8c4df6c732838c7787964eaac00e5921fb1498a60f4606766b3d9685001558d1a974e7341513e",
	"313233343030",
	"ffffffff00000000ffffffffffffffffbce6faada7179e84f3b9cac2fc632550ffffffff00000000ffffffffffffffffbce6faada7179e84f3b9cac2fc632551",
	"F",

	/* ecdsa_secp256r1_sha256_p1363_test.json - 35 */
	"ecdsa_secp256r1_sha256_p1363_test.json - 35",
	"042927b10512bae3eddcfe467828128bad2903269919f7086069c8c4df6c732838c7787964eaac00e5921fb1498a60f4606766b3d9685001558d1a974e7341513e",
	"313233343030",
	"ffffffff00000000ffffffffffffffffbce6faada7179e84f3b9cac2fc632550ffffffff00000000ffffffffffffffffbce6faada7179e84f3b9cac2fc632550",
	"F",

	/* ecdsa_secp256r1_sha256_p1363_test.json - 36 */
	"ecdsa_secp256r1_sha256_p1363_test.json - 36",
	"042927b10512bae3eddcfe467828128bad2903269919f7086069c8c4df6c732838c7787964eaac00e5921fb1498a60f4606766b3d9685001558d1a974e7341513e",
	"313233343030",
	"ffffffff00000000ffffffffffffffffbce6faada7179e84f3b9cac2fc632550ffffffff00000000ffffffffffffffffbce6faada7179e84f3b9cac2fc632552",
	"F",

	/* ecdsa_secp256r1_sha256_p1363_test.json - 37 */
	"ecdsa_secp256r1_sha256_p1363_test.json - 37",
	"042927b10512bae3eddcfe467828128bad2903269919f7086069c8c4df6c732838c7787964eaac00e5921fb1498a60f4606766b3d9685001558d1a974e7341513e",
	"313233343030",
	"ffffffff00000000ffffffffffffffffbce6faada7179e84f3b9cac2fc632550ffffffff00000001000000000000000000000000ffffffffffffffffffffffff",
	"F",

	/* ecdsa_secp256r1_sha256_p1363_test.json - 38 */
	"ecdsa_secp256r1_sha256_p1363_test.json - 38",
	"042927b10512bae3eddcfe467828128bad2903269919f7086069c8c4df6c732838c7787964eaac00e5921fb1498a60f4606766b3d9685001558d1a974e7341513e",
	"313233343030",
	"ffffffff00000000ffffffffffffffffbce6faada7179e84f3b9cac2fc632550ffffffff00000001000000000000000000000001000000000000000000000000",
	"F",

	/* ecdsa_secp256r1_sha256_p1363_test.json - 39 */
	"ecdsa_secp256r1_sha256_p1363_test.json - 39",
	"042927b10512bae3eddcfe467828128bad2903269919f7086069c8c4df6c732838c7787964eaac00e5921fb1498a60f4606766b3d9685001558d1a974e7341513e",
	"313233343030",
	"ffffffff00000000ffffffffffffffffbce6faada7179e84f3b9cac2fc6325520000000000000000000000000000000000000000000000000000000000000000",
	"F",

	/* ecdsa_secp256r1_sha256_p1363_test.json - 40 */
	"ecdsa_secp256r1_sha256_p1363_test.json - 40",
	"042927b10512bae3eddcfe467828128bad2903269919f7086069c8c4df6c732838c7787964eaac00e5921fb1498a60f4606766b3d9685001558d1a974e7341513e",
	"313233343030",
	"ffffffff00000000ffffffffffffffffbce6faada7179e84f3b9cac2fc6325520000000000000000000000000000000000000000000000000000000000000001",
	"F",

	/* ecdsa_secp256r1_sha256_p1363_test.json - 41 */
	"ecdsa_secp256r1_sha256_p1363_test.json - 41",
	"042927b10512bae3eddcfe467828128bad2903269919f7086069c8c4df6c732838c7787964eaac00e5921fb1498a60f4606766b3d9685001558d1a974e7341513e",
	"313233343030",
	"ffffffff00000000ffffffffffffffffbce6faada7179e84f3b9cac2fc632552ffffffff00000000ffffffffffffffffbce6faada7179e84f3b9cac2fc632551",
	"F",

	/* ecdsa_secp256r1_sha256_p1363_test.json - 42 */
	"ecdsa_secp256r1_sha256_p1363_test.json - 42",
	"042927b10512bae3eddcfe467828128bad2903269919f7086069c8c4df6c732838c7787964eaac00e5921fb1498a60f4606766b3d9685001558d1a974e7341513e",
	"313233343030",
	"ffffffff00000000ffffffffffffffffbce6faada7179e84f3b9cac2fc632552ffffffff00000000ffffffffffffffffbce6faada7179e84f3b9cac2fc632550",
	"F",

	/* ecdsa_secp256r1_sha256_p1363_test.json - 43 */
	"ecdsa_secp256r1_sha256_p1363_test.json - 43",
	"042927b10512bae3eddcfe467828128bad2903269919f7086069c8c4df6c732838c7787964eaac00e5921fb1498a60f4606766b3d9685001558d1a974e7341513e",
	"313233343030",
	"ffffffff00000000ffffffffffffffffbce6faada7179e84f3b9cac2fc632552ffffffff00000000ffffffffffffffffbce6faada7179e84f3b9cac2fc632552",
	"F",

	/* ecdsa_secp256r1_sha256_p1363_test.json - 44 */
	"ecdsa_secp256r1_sha256_p1363_test.json - 44",
	"042927b10512bae3eddcfe467828128bad2903269919f7086069c8c4df6c732838c7787964eaac00e5921fb1498a60f4606766b3d9685001558d1a974e7341513e",
	"313233343030",
	"ffffffff00000000ffffffffffffffffbce6faada7179e84f3b9cac2fc632552ffffffff00000001000000000000000000000000ffffffffffffffffffffffff",
	"F",

	/* ecdsa_secp256r1_sha256_p1363_test.json - 45 */
	"ecdsa_secp256r1_sha256_p1363_test.json - 45",
	"042927b10512bae3eddcfe467828128bad2903269919f7086069c8c4df6c732838c7787964eaac00e5921fb1498a60f4606766b3d9685001558d1a974e7341513e",
	"313233343030",
	"ffffffff00000000ffffffffffffffffbce6faada7179e84f3b9cac2fc632552ffffffff00000001000000000000000000000001000000000000000000000000",
	"F",

	/* ecdsa_secp256r1_sha256_p1363_test.json - 46 */
	"ecdsa_secp256r1_sha256_p1363_test.json - 46",
	"042927b10512bae3eddcfe467828128bad2903269919f7086069c8c4df6c732838c7787964eaac00e5921fb1498a60f4606766b3d9685001558d1a974e7341513e",
	"313233343030",
	"ffffffff00000001000000000000000000000000ffffffffffffffffffffffff0000000000000000000000000000000000000000000000000000000000000000",
	"F",

	/* ecdsa_secp256r1_sha256_p1363_test.json - 47 */
	"ecdsa_secp256r1_sha256_p1363_test.json - 47",
	"042927b10512bae3eddcfe467828128bad2903269919f7086069c8c4df6c732838c7787964eaac00e5921fb1498a60f4606766b3d9685001558d1a974e7341513e",
	"313233343030",
	"ffffffff00000001000000000000000000000000ffffffffffffffffffffffff0000000000000000000000000000000000000000000000000000000000000001",
	"F",

	/* ecdsa_secp256r1_sha256_p1363_test.json - 48 */
	"ecdsa_secp256r1_sha256_p1363_test.json - 48",
	"042927b10512bae3eddcfe467828128bad2903269919f7086069c8c4df6c732838c7787964eaac00e5921fb1498a60f4606766b3d9685001558d1a974e7341513e",
	"313233343030",
	"ffffffff00000001000000000000000000000000ffffffffffffffffffffffffffffffff00000000ffffffffffffffffbce6faada7179e84f3b9cac2fc632551",
	"F",

	/* ecdsa_secp256r1_sha256_p1363_test.json - 49 */
	"ecdsa_secp256r1_sha256_p1363_test.json - 49",
	"042927b10512bae3eddcfe467828128bad2903269919f7086069c8c4df6c732838c7787964eaac00e5921fb1498a60f4606766b3d9685001558d1a974e7341513e",
	"313233343030",
	"ffffffff00000001000000000000000000000000ffffffffffffffffffffffffffffffff00000000ffffffffffffffffbce6faada7179e84f3b9cac2fc632550",
	"F",

	/* ecdsa_secp256r1_sha256_p1363_test.json - 50 */
	"ecdsa_secp256r1_sha256_p1363_test.json - 50",
	"042927b10512bae3eddcfe467828128bad2903269919f7086069c8c4df6c732838c7787964eaac00e5921fb1498a60f4606766b3d9685001558d1a974e7341513e",
	"313233343030",
	"ffffffff00000001000000000000000000000000ffffffffffffffffffffffffffffffff00000000ffffffffffffffffbce6faada7179e84f3b9cac2fc632552",
	"F",

	/* ecdsa_secp256r1_sha256_p1363_test.json - 51 */
	"ecdsa_secp256r1_sha256_p1363_test.json - 51",
	"042927b10512bae3eddcfe467828128bad2903269919f7086069c8c4df6c732838c7787964eaac00e5921fb1498a60f4606766b3d9685001558d1a974e7341513e",
	"313233343030",
	"ffffffff00000001000000000000000000000000ffffffffffffffffffffffffffffffff00000001000000000000000000000000ffffffffffffffffffffffff",
	"F",

	/* ecdsa_secp256r1_sha256_p1363_test.json - 52 */
	"ecdsa_secp256r1_sha256_p1363_test.json - 52",
	"042927b10512bae3eddcfe467828128bad2903269919f7086069c8c4df6c732838c7787964eaac00e5921fb1498a60f4606766b3d9685001558d1a974e7341513e",
	"313233343030",
	"ffffffff00000001000000000000000000000000ffffffffffffffffffffffffffffffff00000001000000000000000000000001000000000000000000000000",
	"F",

	/* ecdsa_secp256r1_sha256_p1363_test.json - 53 */
	"ecdsa_secp256r1_sha256_p1363_test.json - 53",
	"042927b10512bae3eddcfe467828128bad2903269919f7086069c8c4df6c732838c7787964eaac00e5921fb1498a60f4606766b3d9685001558d1a974e7341513e",
	"313233343030",
	"ffffffff000000010000000000000000000000010000000000000000000000000000000000000000000000000000000000000000000000000000000000000000",
	"F",

	/* ecdsa_secp256r1_sha256_p1363_test.json - 54 */
	"ecdsa_secp256r1_sha256_p1363_test.json - 54",
	"042927b10512bae3eddcfe467828128bad2903269919f7086069c8c4df6c732838c7787964eaac00e5921fb1498a60f4606766b3d9685001558d1a974e7341513e",
	"313233343030",
	"ffffffff000000010000000000000000000000010000000000000000000000000000000000000000000000000000000000000000000000000000000000000001",
	"F",

	/* ecdsa_secp256r1_sha256_p1363_test.json - 55 */
	"ecdsa_secp256r1_sha256_p1363_test.json - 55",
	"042927b10512bae3eddcfe467828128bad2903269919f7086069c8c4df6c732838c7787964eaac00e5921fb1498a60f4606766b3d9685001558d1a974e7341513e",
	"313233343030",
	"ffffffff00000001000000000000000000000001000000000000000000000000ffffffff00000000ffffffffffffffffbce6faada7179e84f3b9cac2fc632551",
	"F",

	/* ecdsa_secp256r1_sha256_p1363_test.json - 56 */
	"ecdsa_secp256r1_sha256_p1363_test.json - 56",
	"042927b10512bae3eddcfe467828128bad2903269919f7086069c8c4df6c732838c7787964eaac00e5921fb1498a60f4606766b3d9685001558d1a974e7341513e",
	"313233343030",
	"ffffffff00000001000000000000000000000001000000000000000000000000ffffffff00000000ffffffffffffffffbce6faada7179e84f3b9cac2fc632550",
	"F",

	/* ecdsa_secp256r1_sha256_p1363_test.json - 57 */
	"ecdsa_secp256r1_sha256_p1363_test.json - 57",
	"042927b10512bae3eddcfe467828128bad2903269919f7086069c8c4df6c732838c7787964eaac00e5921fb1498a60f4606766b3d9685001558d1a974e7341513e",
	"313233343030",
	"ffffffff00000001000000000000000000000001000000000000000000000000ffffffff00000000ffffffffffffffffbce6faada7179e84f3b9cac2fc632552",
	"F",

	/* ecdsa_secp256r1_sha256_p1363_test.json - 58 */
	"ecdsa_secp256r1_sha256_p1363_test.json - 58",
	"042927b10512bae3eddcfe467828128bad2903269919f7086069c8c4df6c732838c7787964eaac00e5921fb1498a60f4606766b3d9685001558d1a974e7341513e",
	"313233343030",
	"ffffffff00000001000000000000000000000001000000000000000000000000ffffffff00000001000000000000000000000000ffffffffffffffffffffffff",
	"F",

	/* ecdsa_secp256r1_sha256_p1363_test.json - 59 */
	"ecdsa_secp256r1_sha256_p1363_test.json - 59",
	"042927b10512bae3eddcfe467828128bad2903269919f7086069c8c4df6c732838c7787964eaac00e5921fb1498a60f4606766b3d9685001558d1a974e7341513e",
	"313233343030",
	"ffffffff00000001000000000000000000000001000000000000000000000000ffffffff00000001000000000000000000000001000000000000000000000000",
	"F",

	/* ecdsa_secp256r1_sha256_p1363_test.json - 60 */
	"ecdsa_secp256r1_sha256_p1363_test.json - 60",
	"042927b10512bae3eddcfe467828128bad2903269919f7086069c8c4df6c732838c7787964eaac00e5921fb1498a60f4606766b3d9685001558d1a974e7341513e",
	"3639383139",
	"64a1aab5000d0e804f3e2fc02bdee9be8ff312334e2ba16d11547c97711c898e6af015971cc30be6d1a206d4e013e0997772a2f91d73286ffd683b9bb2cf4f1b",
	"G",

	/* ecdsa_secp256r1_sha256_p1363_test.json - 61 */
	"ecdsa_secp256r1_sha256_p1363_test.json - 61",
	"042927b10512bae3eddcfe467828128bad2903269919f7086069c8c4df6c732838c7787964eaac00e5921fb1498a60f4606766b3d9685001558d1a974e7341513e",
	"343236343739373234",
	"16aea964a2f6506d6f78c81c91fc7e8bded7d397738448de1e19a0ec580bf266252cd762130c6667cfe8b7bc47d27d78391e8e80c578d1cd38c3ff033be928e9",
	"G",

	/* ecdsa_secp256r1_sha256_p1363_test.json - 62 */
	"ecdsa_secp256r1_sha256_p1363_test.json - 62",
	"042927b10512bae3eddcfe467828128bad2903269919f7086069c8c4df6c732838c7787964eaac00e5921fb1498a60f4606766b3d9685001558d1a974e7341513e",
	"37313338363834383931",
	"9cc98be2347d469bf476dfc26b9b733df2d26d6ef524af917c665baccb23c882093496459effe2d8d70727b82462f61d0ec1b7847929d10ea631dacb16b56c32",
	"G",

	/* ecdsa_secp256r1_sha256_p1363_test.json - 63 */
	"ecdsa_secp256r1_sha256_p1363_test.json - 63",
	"042927b10512bae3eddcfe467828128bad2903269919f7086069c8c4df6c732838c7787964eaac00e5921fb1498a60f4606766b3d9685001558d1a974e7341513e",
	"3130333539333331363638",
	"73b3c90ecd390028058164524dde892703dce3dea0d53fa8093999f07ab8aa432f67b0b8e20636695bb7d8bf0a651c802ed25a395387b5f4188c0c4075c88634",
	"G",

	/* ecdsa_secp256r1_sha256_p1363_test.json - 64 */
	"ecdsa_secp256r1_sha256_p1363_test.json - 64",
	"042927b10512bae3eddcfe467828128bad2903269919f7086069c8c4df6c732838c7787964eaac00e5921fb1498a60f4606766b3d9685001558d1a974e7341513e",
	"33393439343031323135",
	"bfab3098252847b328fadf2f89b95c851a7f0eb390763378f37e90119d5ba3ddbdd64e234e832b1067c2d058ccb44d978195ccebb65c2aaf1e2da9b8b4987e3b",
	"G",

	/* ecdsa_secp256r1_sha256_p1363_test.json - 65 */
	"ecdsa_secp256r1_sha256_p1363_test.json - 65",
	"042927b10512bae3eddcfe467828128bad2903269919f7086069c8c4df6c732838c7787964eaac00e5921fb1498a60f4606766b3d9685001558d1a974e7341513e",
	"31333434323933303739",
	"204a9784074b246d8bf8bf04a4ceb1c1f1c9aaab168b1596d17093c5cd21d2cd51cce41670636783dc06a759c8847868a406c2506fe17975582fe648d1d88b52",
	"G",

	/* ecdsa_secp256r1_sha256_p1363_test.json - 66 */
	"ecdsa_secp256r1_sha256_p1363_test.json - 66",
	"042927b10512bae3eddcfe467828128bad2903269919f7086069c8c4df6c732838c7787964eaac00e5921fb1498a60f4606766b3d9685001558d1a974e7341513e",
	"33373036323131373132",
	"ed66dc34f551ac82f63d4aa4f81fe2cb0031a91d1314f835027bca0f1ceeaa0399ca123aa09b13cd194a422e18d5fda167623c3f6e5d4d6abb8953d67c0c48c7",
	"G",

	/* ecdsa_secp256r1_sha256_p1363_test.json - 67 */
	"ecdsa_secp256r1_sha256_p1363_test.json - 67",
	"042927b10512bae3eddcfe467828128bad2903269919f7086069c8c4df6c732838c7787964eaac00e5921fb1498a60f4606766b3d9685001558d1a974e7341513e",
	"333433363838373132",
	"060b700bef665c68899d44f2356a578d126b062023ccc3c056bf0f60a237012b8d186c027832965f4fcc78a3366ca95dedbb410cbef3f26d6be5d581c11d3610",
	"G",

	/* ecdsa_secp256r1_sha256_p1363_test.json - 68 */
	"ecdsa_secp256r1_sha256_p1363_test.json - 68",
	"042927b10512bae3eddcfe467828128bad2903269919f7086069c8c4df6c732838c7787964eaac00e5921fb1498a60f4606766b3d9685001558d1a974e7341513e",
	"31333531353330333730",
	"9f6adfe8d5eb5b2c24d7aa7934b6cf29c93ea76cd313c9132bb0c8e38c96831db26a9c9e40e55ee0890c944cf271756c906a33e66b5bd15e051593883b5e9902",
	"G",

	/* ecdsa_secp256r1_sha256_p1363_test.json - 69 */
	"ecdsa_secp256r1_sha256_p1363_test.json - 69",
	"042927b10512bae3eddcfe467828128bad2903269919f7086069c8c4df6c732838c7787964eaac00e5921fb1498a60f4606766b3d9685001558d1a974e7341513e",
	"36353533323033313236",
	"a1af03ca91677b673ad2f33615e56174a1abf6da168cebfa8868f4ba273f16b720aa73ffe48afa6435cd258b173d0c2377d69022e7d098d75caf24c8c5e06b1c",
	"G",

	/* ecdsa_secp256r1_sha256_p1363_test.json - 70 */
	"ecdsa_secp256r1_sha256_p1363_test.json - 70",
	"042927b10512bae3eddcfe467828128bad2903269919f7086069c8c4df6c732838c7787964eaac00e5921fb1498a60f4606766b3d9685001558d1a974e7341513e",
	"31353634333436363033",
	"fdc70602766f8eed11a6c99a71c973d5659355507b843da6e327a28c11893db93df5349688a085b137b1eacf456a9e9e0f6d15ec0078ca60a7f83f2b10d21350",
	"G",

	/* ecdsa_secp256r1_sha256_p1363_test.json - 71 */
	"ecdsa_secp256r1_sha256_p1363_test.json - 71",
	"042927b10512bae3eddcfe467828128bad2903269919f7086069c8c4df6c732838c7787964eaac00e5921fb1498a60f4606766b3d9685001558d1a974e7341513e",
	"34343239353339313137",
	"b516a314f2fce530d6537f6a6c49966c23456f63c643cf8e0dc738f7b876e675d39ffd033c92b6d717dd536fbc5efdf1967c4bd80954479ba66b0120cd16fff2",
	"G",

	/* ecdsa_secp256r1_sha256_p1363_test.json - 72 */
	"ecdsa_secp256r1_sha256_p1363_test.json - 72",
	"042927b10512bae3eddcfe467828128bad2903269919f7086069c8c4df6c732838c7787964eaac00e5921fb1498a60f4606766b3d9685001558d1a974e7341513e",
	"3130393533323631333531",
	"3b2cbf046eac45842ecb7984d475831582717bebb6492fd0a485c101e29ff0a84c9b7b47a98b0f82de512bc9313aaf51701099cac5f76e68c8595fc1c1d99258",
	"G",

	/* ecdsa_secp256r1_sha256_p1363_test.json - 73 */
	"ecdsa_secp256r1_sha256_p1363_test.json - 73",
	"042927b10512bae3eddcfe467828128bad2903269919f7086069c8c4df6c732838c7787964eaac00e5921fb1498a60f4606766b3d9685001558d1a974e7341513e",
	"35393837333530303431",
	"30c87d35e636f540841f14af54e2f9edd79d0312cfa1ab656c3fb15bfde48dcf47c15a5a82d24b75c85a692bd6ecafeb71409ede23efd08e0db9abf6340677ed",
	"G",

	/* ecdsa_secp256r1_sha256_p1363_test.json - 74 */
	"ecdsa_secp256r1_sha256_p1363_test.json - 74",
	"042927b10512bae3eddcfe467828128bad2903269919f7086069c8c4df6c732838c7787964eaac00e5921fb1498a60f4606766b3d9685001558d1a974e7341513e",
	"33343633303036383738",
	"38686ff0fda2cef6bc43b58cfe6647b9e2e8176d168dec3c68ff262113760f52067ec3b651f422669601662167fa8717e976e2db5e6a4cf7c2ddabb3fde9d67d",
	"G",

	/* ecdsa_secp256r1_sha256_p1363_test.json - 75 */
	"ecdsa_secp256r1_sha256_p1363_test.json - 75",
	"042927b10512bae3eddcfe467828128bad2903269919f7086069c8c4df6c732838c7787964eaac00e5921fb1498a60f4606766b3d9685001558d1a974e7341513e",
	"39383137333230323837",
	"44a3e23bf314f2b344fc25c7f2de8b6af3e17d27f5ee844b225985ab6e2775cf2d48e223205e98041ddc87be532abed584f0411f5729500493c9cc3f4dd15e86",
	"G",

	/* ecdsa_secp256r1_sha256_p1363_test.json - 76 */
	"ecdsa_secp256r1_sha256_p1363_test.json - 76",
	"042927b10512bae3eddcfe467828128bad2903269919f7086069c8c4df6c732838c7787964eaac00e5921fb1498a60f4606766b3d9685001558d1a974e7341513e",
	"33323232303431303436",
	"2ded5b7ec8e90e7bf11f967a3d95110c41b99db3b5aa8d330eb9d638781688e97d5792c53628155e1bfc46fb1a67e3088de049c328ae1f44ec69238a009808f9",
	"G",

	/* ecdsa_secp256r1_sha256_p1363_test.json - 77 */
	"ecdsa_secp256r1_sha256_p1363_test.json - 77",
	"042927b10512bae3eddcfe467828128bad2903269919f7086069c8c4df6c732838c7787964eaac00e5921fb1498a60f4606766b3d9685001558d1a974e7341513e",
	"36363636333037313034",
	"bdae7bcb580bf335efd3bc3d31870f923eaccafcd40ec2f605976f15137d8b8ff6dfa12f19e525270b0106eecfe257499f373a4fb318994f24838122ce7ec3c7",
	"G",

	/* ecdsa_secp256r1_sha256_p1363_test.json - 78 */
	"ecdsa_secp256r1_sha256_p1363_test.json - 78",
	"042927b10512bae3eddcfe467828128bad2903269919f7086069c8c4df6c732838c7787964eaac00e5921fb1498a60f4606766b3d9685001558d1a974e7341513e",
	"31303335393531383938",
	"50f9c4f0cd6940e162720957ffff513799209b78596956d21ece251c2401f1c6d7033a0a787d338e889defaaabb106b95a4355e411a59c32aa5167dfab244726",
	"G",

	/* ecdsa_secp256r1_sha256_p1363_test.json - 79 */
	"ecdsa_secp256r1_sha256_p1363_test.json - 79",
	"042927b10512bae3eddcfe467828128bad2903269919f7086069c8c4df6c732838c7787964eaac00e5921fb1498a60f4606766b3d9685001558d1a974e7341513e",
	"31383436353937313935",
	"f612820687604fa01906066a378d67540982e29575d019aabe90924ead5c860d3f9367702dd7dd4f75ea98afd20e328a1a99f4857b316525328230ce294b0fef",
	"G",

	/* ecdsa_secp256r1_sha256_p1363_test.json - 80 */
	"ecdsa_secp256r1_sha256_p1363_test.json - 80",
	"042927b10512bae3eddcfe467828128bad2903269919f7086069c8c4df6c732838c7787964eaac00e5921fb1498a60f4606766b3d9685001558d1a974e7341513e",
	"33313336303436313839",
	"9505e407657d6e8bc93db5da7aa6f5081f61980c1949f56b0f2f507da5782a7ac60d31904e3669738ffbeccab6c3656c08e0ed5cb92b3cfa5e7f71784f9c5021",
	"G",

	/* ecdsa_secp256r1_sha256_p1363_test.json - 81 */
	"ecdsa_secp256r1_sha256_p1363_test.json - 81",
	"042927b10512bae3eddcfe467828128bad2903269919f7086069c8c4df6c732838c7787964eaac00e5921fb1498a60f4606766b3d9685001558d1a974e7341513e",
	"32363633373834323534",
	"bbd16fbbb656b6d0d83e6a7787cd691b08735aed371732723e1c68a40404517d9d8e35dba96028b7787d91315be675877d2d097be5e8ee34560e3e7fd25c0f00",
	"G",

	/* ecdsa_secp256r1_sha256_p1363_test.json - 82 */
	"ecdsa_secp256r1_sha256_p1363_test.json - 82",
	"042927b10512bae3eddcfe467828128bad2903269919f7086069c8c4df6c732838c7787964eaac00e5921fb1498a60f4606766b3d9685001558d1a974e7341513e",
	"31363532313030353234",
	"2ec9760122db98fd06ea76848d35a6da442d2ceef7559a30cf57c61e92df327e7ab271da90859479701fccf86e462ee3393fb6814c27b760c4963625c0a19878",
	"G",

	/* ecdsa_secp256r1_sha256_p1363_test.json - 83 */
	"ecdsa_secp256r1_sha256_p1363_test.json - 83",
	"042927b10512bae3eddcfe467828128bad2903269919f7086069c8c4df6c732838c7787964eaac00e5921fb1498a60f4606766b3d9685001558d1a974e7341513e",
	"35373438303831363936",
	"54e76b7683b6650baa6a7fc49b1c51eed9ba9dd463221f7a4f1005a89fe00c592ea076886c773eb937ec1cc8374b7915cfd11b1c1ae1166152f2f7806a31c8fd",
	"G",

	/* ecdsa_secp256r1_sha256_p1363_test.json - 84 */
	"ecdsa_secp256r1_sha256_p1363_test.json - 84",
	"042927b10512bae3eddcfe467828128bad2903269919f7086069c8c4df6c732838c7787964eaac00e5921fb1498a60f4606766b3d9685001558d1a974e7341513e",
	"36333433393133343638",
	"5291deaf24659ffbbce6e3c26f6021097a74abdbb69be4fb10419c0c496c946665d6fcf336d27cc7cdb982bb4e4ecef5827f84742f29f10abf83469270a03dc3",
	"G",

	/* ecdsa_secp256r1_sha256_p1363_test.json - 85 */
	"ecdsa_secp256r1_sha256_p1363_test.json - 85",
	"042927b10512bae3eddcfe467828128bad2903269919f7086069c8c4df6c732838c7787964eaac00e5921fb1498a60f4606766b3d9685001558d1a974e7341513e",
	"31353431313033353938",
	"207a3241812d75d947419dc58efb05e8003b33fc17eb50f9d15166a88479f107cdee749f2e492b213ce80b32d0574f62f1c5d70793cf55e382d5caadf7592767",
	"G",

	/* ecdsa_secp256r1_sha256_p1363_test.json - 86 */
	"ecdsa_secp256r1_sha256_p1363_test.json - 86",
	"042927b10512bae3eddcfe467828128bad2903269919f7086069c8c4df6c732838c7787964eaac00e5921fb1498a60f4606766b3d9685001558d1a974e7341513e",
	"3130343738353830313238",
	"6554e49f82a855204328ac94913bf01bbe84437a355a0a37c0dee3cf81aa7728aea00de2507ddaf5c94e1e126980d3df16250a2eaebc8be486effe7f22b4f929",
	"G",

	/* ecdsa_secp256r1_sha256_p1363_test.json - 87 */
	"ecdsa_secp256r1_sha256_p1363_test.json - 87",
	"042927b10512bae3eddcfe467828128bad2903269919f7086069c8c4df6c732838c7787964eaac00e5921fb1498a60f4606766b3d9685001558d1a974e7341513e",
	"3130353336323835353638",
	"a54c5062648339d2bff06f71c88216c26c6e19b4d80a8c602990ac82707efdfce99bbe7fcfafae3e69fd016777517aa01056317f467ad09aff09be73c9731b0d",
	"G",

	/* ecdsa_secp256r1_sha256_p1363_test.json - 88 */
	"ecdsa_secp256r1_sha256_p1363_test.json - 88",
	"042927b10512bae3eddcfe467828128bad2903269919f7086069c8c4df6c732838c7787964eaac00e5921fb1498a60f4606766b3d9685001558d1a974e7341513e",
	"393533393034313035",
	"975bd7157a8d363b309f1f444012b1a1d23096593133e71b4ca8b059cff37eaf7faa7a28b1c822baa241793f2abc930bd4c69840fe090f2aacc46786bf919622",
	"G",

	/* ecdsa_secp256r1_sha256_p1363_test.json - 89 */
	"ecdsa_secp256r1_sha256_p1363_test.json - 89",
	"042927b10512bae3eddcfe467828128bad2903269919f7086069c8c4df6c732838c7787964eaac00e5921fb1498a60f4606766b3d9685001558d1a974e7341513e",
	"393738383438303339",
	"5694a6f84b8f875c276afd2ebcfe4d61de9ec90305afb1357b95b3e0da43885e0dffad9ffd0b757d8051dec02ebdf70d8ee2dc5c7870c0823b6ccc7c679cbaa4",
	"G",

	/* ecdsa_secp256r1_sha256_p1363_test.json - 90 */
	"ecdsa_secp256r1_sha256_p1363_test.json - 90",
	"042927b10512bae3eddcfe467828128bad2903269919f7086069c8c4df6c732838c7787964eaac00e5921fb1498a60f4606766b3d9685001558d1a974e7341513e",
	"33363130363732343432",
	"a0c30e8026fdb2b4b4968a27d16a6d08f7098f1a98d21620d7454ba9790f1ba65e470453a8a399f15baf463f9deceb53acc5ca64459149688bd2760c65424339",
	"G",

	/* ecdsa_secp256r1_sha256_p1363_test.json - 91 */
	"ecdsa_secp256r1_sha256_p1363_test.json - 91",
	"042927b10512bae3eddcfe467828128bad2903269919f7086069c8c4df6c732838c7787964eaac00e5921fb1498a60f4606766b3d9685001558d1a974e7341513e",
	"31303534323430373035",
	"614ea84acf736527dd73602cd4bb4eea1dfebebd5ad8aca52aa0228cf7b99a88737cc85f5f2d2f60d1b8183f3ed490e4de14368e96a9482c2a4dd193195c902f",
	"G",

	/* ecdsa_secp256r1_sha256_p1363_test.json - 92 */
	"ecdsa_secp256r1_sha256_p1363_test.json - 92",
	"042927b10512bae3eddcfe467828128bad2903269919f7086069c8c4df6c732838c7787964eaac00e5921fb1498a60f4606766b3d9685001558d1a974e7341513e",
	"35313734343438313937",
	"bead6734ebe44b810d3fb2ea00b1732945377338febfd439a8d74dfbd0f942fa6bb18eae36616a7d3cad35919fd21a8af4bbe7a10f73b3e036a46b103ef56e2a",
	"G",

	/* ecdsa_secp256r1_sha256_p1363_test.json - 93 */
	"ecdsa_secp256r1_sha256_p1363_test.json - 93",
	"042927b10512bae3eddcfe467828128bad2903269919f7086069c8c4df6c732838c7787964eaac00e5921fb1498a60f4606766b3d9685001558d1a974e7341513e",
	"31393637353631323531",
	"499625479e161dacd4db9d9ce64854c98d922cbf212703e9654fae182df9bad242c177cf37b8193a0131108d97819edd9439936028864ac195b64fca76d9d693",
	"G",

	/* ecdsa_secp256r1_sha256_p1363_test.json - 94 */
	"ecdsa_secp256r1_sha256_p1363_test.json - 94",
	"042927b10512bae3eddcfe467828128bad2903269919f7086069c8c4df6c732838c7787964eaac00e5921fb1498a60f4606766b3d9685001558d1a974e7341513e",
	"33343437323533333433",
	"08f16b8093a8fb4d66a2c8065b541b3d31e3bfe694f6b89c50fb1aaa6ff6c9b29d6455e2d5d1779748573b611cb95d4a21f967410399b39b535ba3e5af81ca2e",
	"G",

	/* ecdsa_secp256r1_sha256_p1363_test.json - 95 */
	"ecdsa_secp256r1_sha256_p1363_test.json - 95",
	"042927b10512bae3eddcfe467828128bad2903269919f7086069c8c4df6c732838c7787964eaac00e5921fb1498a60f4606766b3d9685001558d1a974e7341513e",
	"333638323634333138",
	"be26231b6191658a19dd72ddb99ed8f8c579b6938d19bce8eed8dc2b338cb5f8e1d9a32ee56cffed37f0f22b2dcb57d5c943c14f79694a03b9c5e96952575c89",
	"G",

	/* ecdsa_secp256r1_sha256_p1363_test.json - 96 */
	"ecdsa_secp256r1_sha256_p1363_test.json - 96",
	"042927b10512bae3eddcfe467828128bad2903269919f7086069c8c4df6c732838c7787964eaac00e5921fb1498a60f4606766b3d9685001558d1a974e7341513e",
	"33323631313938363038",
	"15e76880898316b16204ac920a02d58045f36a229d4aa4f812638c455abe0443e74d357d3fcb5c8c5337bd6aba4178b455ca10e226e13f9638196506a1939123",
	"G",

	/* ecdsa_secp256r1_sha256_p1363_test.json - 97 */
	"ecdsa_secp256r1_sha256_p1363_test.json - 97",
	"042927b10512bae3eddcfe467828128bad2903269919f7086069c8c4df6c732838c7787964eaac00e5921fb1498a60f4606766b3d9685001558d1a974e7341513e",
	"39363738373831303934",
	"352ecb53f8df2c503a45f9846fc28d1d31e6307d3ddbffc1132315cc07f16dad1348dfa9c482c558e1d05c5242ca1c39436726ecd28258b1899792887dd0a3c6",
	"G",

	/* ecdsa_secp256r1_sha256_p1363_test.json - 98 */
	"ecdsa_secp256r1_sha256_p1363_test.json - 98",
	"042927b10512bae3eddcfe467828128bad2903269919f7086069c8c4df6c732838c7787964eaac00e5921fb1498a60f4606766b3d9685001558d1a974e7341513e",
	"34393538383233383233",
	"4a40801a7e606ba78a0da9882ab23c7677b8642349ed3d652c5bfa5f2a9558fb3a49b64848d682ef7f605f2832f7384bdc24ed2925825bf8ea77dc5981725782",
	"G",

	/* ecdsa_secp256r1_sha256_p1363_test.json - 99 */
	"ecdsa_secp256r1_sha256_p1363_test.json - 99",
	"042927b10512bae3eddcfe467828128bad2903269919f7086069c8c4df6c732838c7787964eaac00e5921fb1498a60f4606766b3d9685001558d1a974e7341513e",
	"383234363337383337",
	"eacc5e1a8304a74d2be412b078924b3bb3511bac855c05c9e5e9e44df3d61e967451cd8e18d6ed1885dd827714847f96ec4bb0ed4c36ce9808db8f714204f6d1",
	"G",

	/* ecdsa_secp256r1_sha256_p1363_test.json - 100 */
	"ecdsa_secp256r1_sha256_p1363_test.json - 100",
	"042927b10512bae3eddcfe467828128bad2903269919f7086069c8c4df6c732838c7787964eaac00e5921fb1498a60f4606766b3d9685001558d1a974e7341513e",
	"3131303230383333373736",
	"2f7a5e9e5771d424f30f67fdab61e8ce4f8cd1214882adb65f7de94c31577052ac4e69808345809b44acb0b2bd889175fb75dd050c5a449ab9528f8f78daa10c",
	"G",

	/* ecdsa_secp256r1_sha256_p1363_test.json - 101 */
	"ecdsa_secp256r1_sha256_p1363_test.json - 101",
	"042927b10512bae3eddcfe467828128bad2903269919f7086069c8c4df6c732838c7787964eaac00e5921fb1498a60f4606766b3d9685001558d1a974e7341513e",
	"313333383731363438",
	"ffcda40f792ce4d93e7e0f0e95e1a2147dddd7f6487621c30a03d710b330021979938b55f8a17f7ed7ba9ade8f2065a1fa77618f0b67add8d58c422c2453a49a",
	"G",

	/* ecdsa_secp256r1_sha256_p1363_test.json - 102 */
	"ecdsa_secp256r1_sha256_p1363_test.json - 102",
	"042927b10512bae3eddcfe467828128bad2903269919f7086069c8c4df6c732838c7787964eaac00e5921fb1498a60f4606766b3d9685001558d1a974e7341513e",
	"333232313434313632",
	"81f2359c4faba6b53d3e8c8c3fcc16a948350f7ab3a588b28c17603a431e39a8cd6f6a5cc3b55ead0ff695d06c6860b509e46d99fccefb9f7f9e101857f74300",
	"G",

	/* ecdsa_secp256r1_sha256_p1363_test.json - 103 */
	"ecdsa_secp256r1_sha256_p1363_test.json - 103",
	"042927b10512bae3eddcfe467828128bad2903269919f7086069c8c4df6c732838c7787964eaac00e5921fb1498a60f4606766b3d9685001558d1a974e7341513e",
	"3130363836363535353436",
	"dfc8bf520445cbb8ee1596fb073ea283ea130251a6fdffa5c3f5f2aaf75ca808048e33efce147c9dd92823640e338e68bfd7d0dc7a4905b3a7ac711e577e90e7",
	"G",

	/* ecdsa_secp256r1_sha256_p1363_test.json - 104 */
	"ecdsa_secp256r1_sha256_p1363_test.json - 104",
	"042927b10512bae3eddcfe467828128bad2903269919f7086069c8c4df6c732838c7787964eaac00e5921fb1498a60f4606766b3d9685001558d1a974e7341513e",
	"3632313535323436",
	"ad019f74c6941d20efda70b46c53db166503a0e393e932f688227688ba6a576293320eb7ca0710255346bdbb3102cdcf7964ef2e0988e712bc05efe16c199345",
	"G",

	/* ecdsa_secp256r1_sha256_p1363_test.json - 105 */
	"ecdsa_secp256r1_sha256_p1363_test.json - 105",
	"042927b10512bae3eddcfe467828128bad2903269919f7086069c8c4df6c732838c7787964eaac00e5921fb1498a60f4606766b3d9685001558d1a974e7341513e",
	"37303330383138373734",
	"ac8096842e8add68c34e78ce11dd71e4b54316bd3ebf7fffdeb7bd5a3ebc1883f5ca2f4f23d674502d4caf85d187215d36e3ce9f0ce219709f21a3aac003b7a8",
	"G",

	/* ecdsa_secp256r1_sha256_p1363_test.json - 106 */
	"ecdsa_secp256r1_sha256_p1363_test.json - 106",
	"042927b10512bae3eddcfe467828128bad2903269919f7086069c8c4df6c732838c7787964eaac00e5921fb1498a60f4606766b3d9685001558d1a974e7341513e",
	"35393234353233373434",
	"677b2d3a59b18a5ff939b70ea002250889ddcd7b7b9d776854b4943693fb92f76b4ba856ade7677bf30307b21f3ccda35d2f63aee81efd0bab6972cc0795db55",
	"G",

	/* ecdsa_secp256r1_sha256_p1363_test.json - 107 */
	"ecdsa_secp256r1_sha256_p1363_test.json - 107",
	"042927b10512bae3eddcfe467828128bad2903269919f7086069c8c4df6c732838c7787964eaac00e5921fb1498a60f4606766b3d9685001558d1a974e7341513e",
	"31343935353836363231",
	"479e1ded14bcaed0379ba8e1b73d3115d84d31d4b7c30e1f05e1fc0d5957cfb0918f79e35b3d89487cf634a4f05b2e0c30857ca879f97c771e877027355b2443",
	"G",

	/* ecdsa_secp256r1_sha256_p1363_test.json - 108 */
	"ecdsa_secp256r1_sha256_p1363_test.json - 108",
	"042927b10512bae3eddcfe467828128bad2903269919f7086069c8c4df6c732838c7787964eaac00e5921fb1498a60f4606766b3d9685001558d1a974e7341513e",
	"34303035333134343036",
	"43dfccd0edb9e280d9a58f01164d55c3d711e14b12ac5cf3b64840ead512a0a31dbe33fa8ba84533cd5c4934365b3442ca1174899b78ef9a3199f49584389772",
	"G",

	/* ecdsa_secp256r1_sha256_p1363_test.json - 109 */
	"ecdsa_secp256r1_sha256_p1363_test.json - 109",
	"042927b10512bae3eddcfe467828128bad2903269919f7086069c8c4df6c732838c7787964eaac00e5921fb1498a60f4606766b3d9685001558d1a974e7341513e",
	"33303936343537353132",
	"5b09ab637bd4caf0f4c7c7e4bca592fea20e9087c259d26a38bb4085f0bbff1145b7eb467b6748af618e9d80d6fdcd6aa24964e5a13f885bca8101de08eb0d75",
	"G",

	/* ecdsa_secp256r1_sha256_p1363_test.json - 110 */
	"ecdsa_secp256r1_sha256_p1363_test.json - 110",
	"042927b10512bae3eddcfe467828128bad2903269919f7086069c8c4df6c732838c7787964eaac00e5921fb1498a60f4606766b3d9685001558d1a974e7341513e",
	"32373834303235363230",
	"5e9b1c5a028070df5728c5c8af9b74e0667afa570a6cfa0114a5039ed15ee06fb1360907e2d9785ead362bb8d7bd661b6c29eeffd3c5037744edaeb9ad990c20",
	"G",

	/* ecdsa_secp256r1_sha256_p1363_test.json - 111 */
	"ecdsa_secp256r1_sha256_p1363_test.json - 111",
	"042927b10512bae3eddcfe467828128bad2903269919f7086069c8c4df6c732838c7787964eaac00e5921fb1498a60f4606766b3d9685001558d1a974e7341513e",
	"32363138373837343138",
	"0671a0a85c2b72d54a2fb0990e34538b4890050f5a5712f6d1a7a5fb8578f32edb1846bab6b7361479ab9c3285ca41291808f27fd5bd4fdac720e5854713694c",
	"G",

	/* ecdsa_secp256r1_sha256_p1363_test.json - 112 */
	"ecdsa_secp256r1_sha256_p1363_test.json - 112",
	"042927b10512bae3eddcfe467828128bad2903269919f7086069c8c4df6c732838c7787964eaac00e5921fb1498a60f4606766b3d9685001558d1a974e7341513e",
	"31363432363235323632",
	"7673f8526748446477dbbb0590a45492c5d7d69859d301abbaedb35b2095103a3dc70ddf9c6b524d886bed9e6af02e0e4dec0d417a414fed3807ef4422913d7c",
	"G",

	/* ecdsa_secp256r1_sha256_p1363_test.json - 113 */
	"ecdsa_secp256r1_sha256_p1363_test.json - 113",
	"042927b10512bae3eddcfe467828128bad2903269919f7086069c8c4df6c732838c7787964eaac00e5921fb1498a60f4606766b3d9685001558d1a974e7341513e",
	"36383234313839343336",
	"7f085441070ecd2bb21285089ebb1aa6450d1a06c36d3ff39dfd657a796d12b5249712012029870a2459d18d47da9aa492a5e6cb4b2d8dafa9e4c5c54a2b9a8b",
	"G",

	/* ecdsa_secp256r1_sha256_p1363_test.json - 114 */
	"ecdsa_secp256r1_sha256_p1363_test.json - 114",
	"042927b10512bae3eddcfe467828128bad2903269919f7086069c8c4df6c732838c7787964eaac00e5921fb1498a60f4606766b3d9685001558d1a974e7341513e",
	"343834323435343235",
	"914c67fb61dd1e27c867398ea7322d5ab76df04bc5aa6683a8e0f30a5d287348fa07474031481dda4953e3ac1959ee8cea7e66ec412b38d6c96d28f6d37304ea",
	"G",

	/* ecdsa_secp256r1_sha256_p1363_test.json - 115 */
	"ecdsa_secp256r1_sha256_p1363_test.json - 115",
	"040ad99500288d466940031d72a9f5445a4d43784640855bf0a69874d2de5fe103c5011e6ef2c42dcd50d5d3d29f99ae6eba2c80c9244f4c5422f0979ff0c3ba5e",
	"313233343030",
	"000000000000000000000000000000004319055358e8617b0c46353d039cdaabffffffff00000000ffffffffffffffffbce6faada7179e84f3b9cac2fc63254e",
	"G",

	/* ecdsa_secp256r1_sha256_p1363_test.json - 116 */
	"ecdsa_secp256r1_sha256_p1363_test.json - 116",
	"040ad99500288d466940031d72a9f5445a4d43784640855bf0a69874d2de5fe103c5011e6ef2c42dcd50d5d3d29f99ae6eba2c80c9244f4c5422f0979ff0c3ba5e",
	"313233343030",
	"ffffffff00000001000000000000000000000000fffffffffffffffffffffffcffffffff00000000ffffffffffffffffbce6faada7179e84f3b9cac2fc63254e",
	"F",

	/* ecdsa_secp256r1_sha256_p1363_test.json - 117 */
	"ecdsa_secp256r1_sha256_p1363_test.json - 117",
	"04ab05fd9d0de26b9ce6f4819652d9fc69193d0aa398f0fba8013e09c58220455419235271228c786759095d12b75af0692dd4103f19f6a8c32f49435a1e9b8d45",
	"313233343030",
	"ffffffff00000000ffffffffffffffffbce6faada7179e84f3b9cac2fc63254fffffffff00000000ffffffffffffffffbce6faada7179e84f3b9cac2fc63254e",
	"G",

	/* ecdsa_secp256r1_sha256_p1363_test.json - 118 */
	"ecdsa_secp256r1_sha256_p1363_test.json - 118",
	"0480984f39a1ff38a86a68aa4201b6be5dfbfecf876219710b07badf6fdd4c6c5611feb97390d9826e7a06dfb41871c940d74415ed3cac2089f1445019bb55ed95",
	"313233343030",
	"7ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffd909135bdb6799286170f5ead2de4f6511453fe50914f3df2de54a36383df8dd4",
	"G",

	/* ecdsa_secp256r1_sha256_p1363_test.json - 119 */
	"ecdsa_secp256r1_sha256_p1363_test.json - 119",
	"044201b4272944201c3294f5baa9a3232b6dd687495fcc19a70a95bc602b4f7c0595c37eba9ee8171c1bb5ac6feaf753bc36f463e3aef16629572c0c0a8fb0800e",
	"313233343030",
	"7ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffd27b4577ca009376f71303fd5dd227dcef5deb773ad5f5a84360644669ca249a5",
	"G",

	/* ecdsa_secp256r1_sha256_p1363_test.json - 120 */
	"ecdsa_secp256r1_sha256_p1363_test.json - 120",
	"04a71af64de5126a4a4e02b7922d66ce9415ce88a4c9d25514d91082c8725ac9575d47723c8fbe580bb369fec9c2665d8e30a435b9932645482e7c9f11e872296b",
	"313233343030",
	"00000000000000000000000000000000000000000000000000000000000000050000000000000000000000000000000000000000000000000000000000000001",
	"G",

	/* ecdsa_secp256r1_sha256_p1363_test.json - 121 */
	"ecdsa_secp256r1_sha256_p1363_test.json - 121",
	"04a71af64de5126a4a4e02b7922d66ce9415ce88a4c9d25514d91082c8725ac9575d47723c8fbe580bb369fec9c2665d8e30a435b9932645482e7c9f11e872296b",
	"313233343030",
	"0501",
	"F",

	/* ecdsa_secp256r1_sha256_p1363_test.json - 122 */
	"ecdsa_secp256r1_sha256_p1363_test.json - 122",
	"046627cec4f0731ea23fc2931f90ebe5b7572f597d20df08fc2b31ee8ef16b15726170ed77d8d0a14fc5c9c3c4c9be7f0d3ee18f709bb275eaf2073e258fe694a5",
	"313233343030",
	"00000000000000000000000000000000000000000000000000000000000000050000000000000000000000000000000000000000000000000000000000000003",
	"G",

	/* ecdsa_secp256r1_sha256_p1363_test.json - 123 */
	"ecdsa_secp256r1_sha256_p1363_test.json - 123",
	"046627cec4f0731ea23fc2931f90ebe5b7572f597d20df08fc2b31ee8ef16b15726170ed77d8d0a14fc5c9c3c4c9be7f0d3ee18f709bb275eaf2073e258fe694a5",
	"313233343030",
	"0503",
	"F",

	/* ecdsa_secp256r1_sha256_p1363_test.json - 124 */
	"ecdsa_secp256r1_sha256_p1363_test.json - 124",
	"045a7c8825e85691cce1f5e7544c54e73f14afc010cb731343262ca7ec5a77f5bfef6edf62a4497c1bd7b147fb6c3d22af3c39bfce95f30e13a16d3d7b2812f813",
	"313233343030",
	"00000000000000000000000000000000000000000000000000000000000000050000000000000000000000000000000000000000000000000000000000000005",
	"G",

	/* ecdsa_secp256r1_sha256_p1363_test.json - 125 */
	"ecdsa_secp256r1_sha256_p1363_test.json - 125",
	"045a7c8825e85691cce1f5e7544c54e73f14afc010cb731343262ca7ec5a77f5bfef6edf62a4497c1bd7b147fb6c3d22af3c39bfce95f30e13a16d3d7b2812f813",
	"313233343030",
	"0505",
	"F",

	/* ecdsa_secp256r1_sha256_p1363_test.json - 126 */
	"ecdsa_secp256r1_sha256_p1363_test.json - 126",
	"04cbe0c29132cd738364fedd603152990c048e5e2fff996d883fa6caca7978c73770af6a8ce44cb41224b2603606f4c04d188e80bff7cc31ad5189d4ab0d70e8c1",
	"313233343030",
	"00000000000000000000000000000000000000000000000000000000000000050000000000000000000000000000000000000000000000000000000000000006",
	"G",

	/* ecdsa_secp256r1_sha256_p1363_test.json - 127 */
	"ecdsa_secp256r1_sha256_p1363_test.json - 127",
	"04cbe0c29132cd738364fedd603152990c048e5e2fff996d883fa6caca7978c73770af6a8ce44cb41224b2603606f4c04d188e80bff7cc31ad5189d4ab0d70e8c1",
	"313233343030",
	"0506",
	"F",

	/* ecdsa_secp256r1_sha256_p1363_test.json - 128 */
	"ecdsa_secp256r1_sha256_p1363_test.json - 128",
	"042ef747671c97d9c7f9cb2f6a30d678c3d84757ba241ef7183d51a29f52d87c2ea8fb2ea635b761baefc1c4ded2099281b844e13e044c328553bbbafa337d8a76",
	"313233343030",
	"00000000000000000000000000000000000000000000000000000000000000060000000000000000000000000000000000000000000000000000000000000001",
	"G",

	/* ecdsa_secp256r1_sha256_p1363_test.json - 129 */
	"ecdsa_secp256r1_sha256_p1363_test.json - 129",
	"042ef747671c97d9c7f9cb2f6a30d678c3d84757ba241ef7183d51a29f52d87c2ea8fb2ea635b761baefc1c4ded2099281b844e13e044c328553bbbafa337d8a76",
	"313233343030",
	"0601",
	"F",

	/* ecdsa_secp256r1_sha256_p1363_test.json - 130 */
	"ecdsa_secp256r1_sha256_p1363_test.json - 130",
	"04931cc49cda4d87d25b1601c56c3b83b4f45e44971998f2d3e7d3c55152214edf058dc140abbba42fc1ddbf30dab8eb9b46ee7338b3f7ee96242bf45e1df5e995",
	"313233343030",
	"00000000000000000000000000000000000000000000000000000000000000060000000000000000000000000000000000000000000000000000000000000003",
	"G",

	/* ecdsa_secp256r1_sha256_p1363_test.json - 131 */
	"ecdsa_secp256r1_sha256_p1363_test.json - 131",
	"04931cc49cda4d87d25b1601c56c3b83b4f45e44971998f2d3e7d3c55152214edf058dc140abbba42fc1ddbf30dab8eb9b46ee7338b3f7ee96242bf45e1df5e995",
	"313233343030",
	"0603",
	"F",

	/* ecdsa_secp256r1_sha256_p1363_test.json - 132 */
	"ecdsa_secp256r1_sha256_p1363_test.json - 132",
	"04899a4af61867e3f3c190dbb48f8bc9fc74b70a467a4a1f06477b3af2f39ab8ed47ac000f9ea8a3034939bf48ad5d061a69fc8495ae4df2dbec7effa03a0062b3",
	"313233343030",
	"00000000000000000000000000000000000000000000000000000000000000060000000000000000000000000000000000000000000000000000000000000006",
	"G",

	/* ecdsa_secp256r1_sha256_p1363_test.json - 133 */
	"ecdsa_secp256r1_sha256_p1363_test.json - 133",
	"04899a4af61867e3f3c190dbb48f8bc9fc74b70a467a4a1f06477b3af2f39ab8ed47ac000f9ea8a3034939bf48ad5d061a69fc8495ae4df2dbec7effa03a0062b3",
	"313233343030",
	"0606",
	"F",

	/* ecdsa_secp256r1_sha256_p1363_test.json - 134 */
	"ecdsa_secp256r1_sha256_p1363_test.json - 134",
	"04d03eb09913cc20c6a8d0070f0d8d2a7f63527fafa44117fce6bd1ef2aa4ae3c46d5df3f45ac58fa334c6d102381b3120b7a2455600dcaff3d1a845514f12bf46",
	"313233343030",
	"00000000000000000000000000000000000000000000000000000000000000060000000000000000000000000000000000000000000000000000000000000007",
	"G",

	/* ecdsa_secp256r1_sha256_p1363_test.json - 135 */
	"ecdsa_secp256r1_sha256_p1363_test.json - 135",
	"04d03eb09913cc20c6a8d0070f0d8d2a7f63527fafa44117fce6bd1ef2aa4ae3c46d5df3f45ac58fa334c6d102381b3120b7a2455600dcaff3d1a845514f12bf46",
	"313233343030",
	"0607",
	"F",

	/* ecdsa_secp256r1_sha256_p1363_test.json - 136 */
	"ecdsa_secp256r1_sha256_p1363_test.json - 136",
	"04d03eb09913cc20c6a8d0070f0d8d2a7f63527fafa44117fce6bd1ef2aa4ae3c46d5df3f45ac58fa334c6d102381b3120b7a2455600dcaff3d1a845514f12bf46",
	"313233343030",
	"ffffffff00000000ffffffffffffffffbce6faada7179e84f3b9cac2fc6325570000000000000000000000000000000000000000000000000000000000000007",
	"F",

	/* ecdsa_secp256r1_sha256_p1363_test.json - 137 */
	"ecdsa_secp256r1_sha256_p1363_test.json - 137",
	"043a72476291571193b4d109b2c37b59f2807e8fe9cffd804eacded903e77ca0da592dbc74fee0ca7508cc7bc282b0c51a143286ff53c60131668e7a0929e4ed04",
	"313233343030",
	"0000000000000000000000000000000000000000000000000000000000000006ffffffff00000000ffffffffffffffffbce6faada7179e84f3b9cac2fc75fbd8",
	"F",

	/* ecdsa_secp256r1_sha256_p1363_test.json - 138 */
	"ecdsa_secp256r1_sha256_p1363_test.json - 138",
	"04d0f73792203716afd4be4329faa48d269f15313ebbba379d7783c97bf3e890d9971f4a3206605bec21782bf5e275c714417e8f566549e6bc68690d2363c89cc1",
	"313233343030",
	"00000000000000000000000000000000000000000000000000000000000001008f1e3c7862c58b16bb76eddbb76eddbb516af4f63f2d74d76e0d28c9bb75ea88",
	"G",

	/* ecdsa_secp256r1_sha256_p1363_test.json - 139 */
	"ecdsa_secp256r1_sha256_p1363_test.json - 139",
	"044838b2be35a6276a80ef9e228140f9d9b96ce83b7a254f71ccdebbb8054ce05ffa9cbc123c919b19e00238198d04069043bd660a828814051fcb8aac738a6c6b",
	"313233343030",
	"000000000000000000000000000000000000000000000000002d9b4d347952d6ef3043e7329581dbb3974497710ab11505ee1c87ff907beebadd195a0ffe6d7a",
	"G",

	/* ecdsa_secp256r1_sha256_p1363_test.json - 140 */
	"ecdsa_secp256r1_sha256_p1363_test.json - 140",
	"047393983ca30a520bbc4783dc9960746aab444ef520c0a8e771119aa4e74b0f64e9d7be1ab01a0bf626e709863e6a486dbaf32793afccf774e2c6cd27b1857526",
	"313233343030",
	"000000000000000000000000000000000000001033e67e37b32b445580bf4eff8b748b74000000008b748b748b748b7466e769ad4a16d3dcd87129b8e91d1b4d",
	"G",

	/* ecdsa_secp256r1_sha256_p1363_test.json - 141 */
	"ecdsa_secp256r1_sha256_p1363_test.json - 141",
	"045ac331a1103fe966697379f356a937f350588a05477e308851b8a502d5dfcdc5fe9993df4b57939b2b8da095bf6d794265204cfe03be995a02e65d408c871c0b",
	"313233343030",
	"0000000000000000000000000000000000000000000000000000000000000100ef9f6ba4d97c09d03178fa20b4aaad83be3cf9cb824a879fec3270fc4b81ef5b",
	"G",

	/* ecdsa_secp256r1_sha256_p1363_test.json - 142 */
	"ecdsa_secp256r1_sha256_p1363_test.json - 142",
	"041d209be8de2de877095a399d3904c74cc458d926e27bb8e58e5eae5767c41509dd59e04c214f7b18dce351fc2a549893a6860e80163f38cc60a4f2c9d040d8c9",
	"313233343030",
	"00000000000000000000000000000000000000062522bbd3ecbe7c39e93e7c25ef9f6ba4d97c09d03178fa20b4aaad83be3cf9cb824a879fec3270fc4b81ef5b",
	"G",

	/* ecdsa_secp256r1_sha256_p1363_test.json - 143 */
	"ecdsa_secp256r1_sha256_p1363_test.json - 143",
	"04083539fbee44625e3acaafa2fcb41349392cef0633a1b8fabecee0c133b10e99915c1ebe7bf00df8535196770a58047ae2a402f26326bb7d41d4d7616337911e",
	"313233343030",
	"ffffffff00000000ffffffffffffffffbce6faada7179e84f3b9cac2fc6324d5555555550000000055555555555555553ef7a8e48d07df81a693439654210c70",
	"G",

	/* ecdsa_secp256r1_sha256_p1363_test.json - 144 */
	"ecdsa_secp256r1_sha256_p1363_test.json - 144",
	"04e075effd9607d08d5f34e3652f64cfa3bd6d20c58d0a232f058491260ab212a4cc61760ac8b0680c1b644c03cc628ba9dc4a3c0561368489c692bd40f43aa3ca",
	"313233343030",
	"0000000000000000000000000000000000000000000000009c44febf31c3594f000000000000000000000000000000000000000000000000839ed28247c2b06b",
	"G",

	/* ecdsa_secp256r1_sha256_p1363_test.json - 145 */
	"ecdsa_secp256r1_sha256_p1363_test.json - 145",
	"04e075effd9607d08d5f34e3652f64cfa3bd6d20c58d0a232f058491260ab212a4cc61760ac8b0680c1b644c03cc628ba9dc4a3c0561368489c692bd40f43aa3ca",
	"313233343030",
	"9c44febf31c3594f839ed28247c2b06b",
	"F",

	/* ecdsa_secp256r1_sha256_p1363_test.json - 146 */
	"ecdsa_secp256r1_sha256_p1363_test.json - 146",
	"04cffb758c3073ea3c08efd9f7f17a85b6ae385c5a140c146ad5f1f5a826718bc8dfdc6bebc894144c6d418ac5d97339726ad2ae925df868426e5628e9f4e62342",
	"313233343030",
	"0000000000000000000000000000000000000009df8b682430beef6f5fd7c7cd000000000000000000000000000000000000000fd0a62e13778f4222a0d61c8a",
	"G",

	/* ecdsa_secp256r1_sha256_p1363_test.json - 147 */
	"ecdsa_secp256r1_sha256_p1363_test.json - 147",
	"04cffb758c3073ea3c08efd9f7f17a85b6ae385c5a140c146ad5f1f5a826718bc8dfdc6bebc894144c6d418ac5d97339726ad2ae925df868426e5628e9f4e62342",
	"313233343030",
	"09df8b682430beef6f5fd7c7cd0fd0a62e13778f4222a0d61c8a",
	"F",

	/* ecdsa_secp256r1_sha256_p1363_test.json - 148 */
	"ecdsa_secp256r1_sha256_p1363_test.json - 148",
	"04b98740e69e61a325d5f772e3b5c4f67fb7150b16a9afeca9ddc4afcbb6fa0549c446e814138e4ebc82dbf86a390056d4595dcf45e381fef217a4597d7bd51498",
	"313233343030",
	"000000000000000000000000000000008a598e563a89f526c32ebec8de26367c0000000000000000000000000000000084f633e2042630e99dd0f1e16f7a04bf",
	"G",

	/* ecdsa_secp256r1_sha256_p1363_test.json - 149 */
	"ecdsa_secp256r1_sha256_p1363_test.json - 149",
	"04b98740e69e61a325d5f772e3b5c4f67fb7150b16a9afeca9ddc4afcbb6fa0549c446e814138e4ebc82dbf86a390056d4595dcf45e381fef217a4597d7bd51498",
	"313233343030",
	"8a598e563a89f526c32ebec8de26367c84f633e2042630e99dd0f1e16f7a04bf",
	"F",

	/* ecdsa_secp256r1_sha256_p1363_test.json - 150 */
	"ecdsa_secp256r1_sha256_p1363_test.json - 150",
	"0484536a270c3932bb2084732adf2c768efc6d3977e5220229ea9a44888b8f9d7b1766398cdac2fc8000017b29a7ba15a58f196037f35f7008ed4286ddff00fd46",
	"313233343030",
	"000000000000000000000000aa6eeb5823f7fa31b466bb473797f0d0314c0bdf000000000000000000000000e2977c479e6d25703cebbc6bd561938cc9d1bfb9",
	"G",

	/* ecdsa_secp256r1_sha256_p1363_test.json - 151 */
	"ecdsa_secp256r1_sha256_p1363_test.json - 151",
	"0484536a270c3932bb2084732adf2c768efc6d3977e5220229ea9a44888b8f9d7b1766398cdac2fc8000017b29a7ba15a58f196037f35f7008ed4286ddff00fd46",
	"313233343030",
	"aa6eeb5823f7fa31b466bb473797f0d0314c0bdfe2977c479e6d25703cebbc6bd561938cc9d1bfb9",
	"F",

	/* ecdsa_secp256r1_sha256_p1363_test.json - 152 */
	"ecdsa_secp256r1_sha256_p1363_test.json - 152",
	"048aeb368a7027a4d64abdea37390c0c1d6a26f399e2d9734de1eb3d0e1937387405bd13834715e1dbae9b875cf07bd55e1b6691c7f7536aef3b19bf7a4adf576d",
	"313233343030",
	"555555550000000055555555555555553ef7a8e48d07df81a693439654210c700000000000000000000000000000000000000000000000000000000000000001",
	"G",

	/* ecdsa_secp256r1_sha256_p1363_test.json - 153 */
	"ecdsa_secp256r1_sha256_p1363_test.json - 153",
	"048aeb368a7027a4d64abdea37390c0c1d6a26f399e2d9734de1eb3d0e1937387405bd13834715e1dbae9b875cf07bd55e1b6691c7f7536aef3b19bf7a4adf576d",
	"313233343030",
	"555555550000000055555555555555553ef7a8e48d07df81a693439654210c700000000000000000000000000000000000000000000000000000000000000000",
	"F",

	/* ecdsa_secp256r1_sha256_p1363_test.json - 154 */
	"ecdsa_secp256r1_sha256_p1363_test.json - 154",
	"0461722eaba731c697c7a9ba4d0afdbb5713d8aa12b0eab601bb33dbaf792c5adc272cd993b2b663aba5b3a26c101182ff178684945e83879e71598b95fe647dfc",
	"313233343030",
	"555555550000000055555555555555553ef7a8e48d07df81a693439654210c7002f676969f451a8ccafa4c4f09791810e6d632dbd60b1d5540f3284fbe1889b0",
	"G",

	/* ecdsa_secp256r1_sha256_p1363_test.json - 155 */
	"ecdsa_secp256r1_sha256_p1363_test.json - 155",
	"04c4c91981e720e20d7e478ff19d09b95a98f58c0f469b72801a8ce844a347316594afcd4188182e7779889b3258d0368ece1e66797fe7c648c6f0b9e26bd71871",
	"313233343030",
	"555555550000000055555555555555553ef7a8e48d07df81a693439654210c704e260962e33362ef0046126d2d5a4edc6947ab20e19b8ec19cf79e5908b6e628",
	"G",

	/* ecdsa_secp256r1_sha256_p1363_test.json - 156 */
	"ecdsa_secp256r1_sha256_p1363_test.json - 156",
	"04d58d47bf49bc8f416641f6f760fcbca80aa52a814e56a5fa40bab44fd6f6317216deaa84d45d8e0e29cc9ecf5653f8ee6444750813becae8deb42b04ba07a634",
	"313233343030",
	"555555550000000055555555555555553ef7a8e48d07df81a693439654210c70077ed0d8f20f697d8fc591ac64dd5219c7932122b4f9b9ec6441e44a0092cf21",
	"G",

	/* ecdsa_secp256r1_sha256_p1363_test.json - 157 */
	"ecdsa_secp256r1_sha256_p1363_test.json - 157",
	"0491e305822e5e44f3fdb616e2ef42cd98f241b86e9f68815bc4dba6a945e4eefb3c5937e2ac1d9466f6d65e49b35fc8d75ffc22e1fe2f32af42f5fa3c26f9b4b0",
	"313233343030",
	"555555550000000055555555555555553ef7a8e48d07df81a693439654210c703e0292a67e181c6c0105ee35e956e78e9bdd033c6e71ae57884039a245e4175f",
	"G",

	/* ecdsa_secp256r1_sha256_p1363_test.json - 158 */
	"ecdsa_secp256r1_sha256_p1363_test.json - 158",
	"0424a0bc4d16dbbd40d2fd81a7c3f8d8ec741607d5bb406a0611cc60d0e683bd46b575cad039c15f7f3dffcfc007b4b0f743c871ecc76a504a32672fd84526d861",
	"313233343030",
	"555555550000000055555555555555553ef7a8e48d07df81a693439654210c7013d22b06d6b8f5d97e0c64962b4a3bae30f668ca6217ef5b35d799f159e23ebe",
	"G",

	/* ecdsa_secp256r1_sha256_p1363_test.json - 159 */
	"ecdsa_secp256r1_sha256_p1363_test.json - 159",
	"04d24dd06745cafb39186d22a92aa0e58169a79ab69488628a9da5ed3ef747269b7e9209d98faeb95355948adae61d5291c6015d3ee9513486d886fb05cbd25c6a",
	"313233343030",
	"555555550000000055555555555555553ef7a8e48d07df81a693439654210c704523ce342e4994bb8968bf6613f60c06c86111f15a3a389309e72cd447d5dd99",
	"G",

	/* ecdsa_secp256r1_sha256_p1363_test.json - 160 */
	"ecdsa_secp256r1_sha256_p1363_test.json - 160",
	"048200f148e7eab1581bcd1e23946f8a9b8191d9641f9560341721f9d3fec3d63ece795669e0481e035de8623d716a6984d0a4809d6c65519443ee55260f7f3dcb",
	"313233343030",
	"555555550000000055555555555555553ef7a8e48d07df81a693439654210c7037d765be3c9c78189ad30edb5097a4db670de11686d01420e37039d4677f4809",
	"G",

	/* ecdsa_secp256r1_sha256_p1363_test.json - 161 */
	"ecdsa_secp256r1_sha256_p1363_test.json - 161",
	"04a8a69c5ed33b150ce8d37ac197070ed894c05d47258a80c9041d92486622024de85997c9666b60a393568efede8f4ca0167c1e10f626e62fc1b8c8e9c6ba6ed7",
	"313233343030",
	"555555550000000055555555555555553ef7a8e48d07df81a693439654210c7044237823b54e0c74c2bf5f759d9ac5f8cb897d537ffa92effd4f0bb6c9acd860",
	"G",

	/* ecdsa_secp256r1_sha256_p1363_test.json - 162 */
	"ecdsa_secp256r1_sha256_p1363_test.json - 162",
	"04ed0587e75b3b9a1dd0794f41d1729fcd432b2436cbf51c230d8bc7273273181735a57f09c7873d3964aa8102c9e25fa53070cd924cb7e3a459174740b8b71c34",
	"313233343030",
	"555555550000000055555555555555553ef7a8e48d07df81a693439654210c70266d30a485385906054ca86d46f5f2b17e7f4646a3092092ad92877126538111",
	"G",

	/* ecdsa_secp256r1_sha256_p1363_test.json - 163 */
	"ecdsa_secp256r1_sha256_p1363_test.json - 163",
	"04077091d99004a99ee08224e59a46a70495e6fba4eff681c3ce42127e588681ef4f1c16c77dfa440dde18245c9de76243d8f2fd9dea3f2782d6c04974d02f25dc",
	"313233343030",
	"555555550000000055555555555555553ef7a8e48d07df81a693439654210c70538c7b3798e84d0ce90340165806348971ed44db8f0c674f5f215968390f92ee",
	"G",

	/* ecdsa_secp256r1_sha256_p1363_test.json - 164 */
	"ecdsa_secp256r1_sha256_p1363_test.json - 164",
	"04616a8b8e57d82c11678f5827911024cd23a16cb52a65f230fb554a7b110c35a5bb466660be5cab3e4b587c12b45bd998bd56c7d66c2f94d03a1a6d2028d8a154",
	"313233343030",
	"555555550000000055555555555555553ef7a8e48d07df81a693439654210c706fef0ef15d1688e15e704c4e6bb8bb7f40d52d3af5c661bb78c4ed9b408699b3",
	"G",

	/* ecdsa_secp256r1_sha256_p1363_test.json - 165 */
	"ecdsa_secp256r1_sha256_p1363_test.json - 165",
	"0471dc92b2b1baa7612c4a53427a0d2dfe548fa9cf829bb6b248f736a5eb30b513f91c7dff1144cb36057c2b859f35bd666a7961833b06de0f45159fbae208e326",
	"313233343030",
	"555555550000000055555555555555553ef7a8e48d07df81a693439654210c706f44275e9aeb1331efcb8d58f35c0252791427e403ad84daad51d247cc2a64c6",
	"G",

	/* ecdsa_secp256r1_sha256_p1363_test.json - 166 */
	"ecdsa_secp256r1_sha256_p1363_test.json - 166",
	"04662f43ae614bd9c90ff3fcded25cf0ef186b6967a47aa6aa7ae7f396594df931f5f94a525edd50d3738f7a28d03d7a2a70095c8f89de9bb2c645fea8d8bac9e0",
	"313233343030",
	"555555550000000055555555555555553ef7a8e48d07df81a693439654210c7021323755b103d2f9da6ab83eccab9ad8598bcf625652f10e7a3eeee3c3945fb3",
	"G",

	/* ecdsa_secp256r1_sha256_p1363_test.json - 167 */
	"ecdsa_secp256r1_sha256_p1363_test.json - 167",
	"04dff107959bd2f7386497a5624430a0ab35e552c1a4e4dc9c298caeb96353170dcb5065d7947a676c76287ca8e430324f8a534b0ba6f21200e033c4b88852a3cc",
	"313233343030",
	"555555550000000055555555555555553ef7a8e48d07df81a693439654210c706c50acfe76de1289e7a5edb240f1c2a7879db6873d5d931f3c6ac467a6eac171",
	"G",

	/* ecdsa_secp256r1_sha256_p1363_test.json - 168 */
	"ecdsa_secp256r1_sha256_p1363_test.json - 168",
	"04bd0862b0bfba85036922e06f5458754aafc3075b603a814b3ac75659bf24d7528258a607ffca2cfe05a300cb4c3c4e1963bbb1bc54d320e16969f85aad243385",
	"313233343030",
	"555555550000000055555555555555553ef7a8e48d07df81a693439654210c70755b7fffb0b17ad57dca50fcefb7fe297b029df25e5ccb5069e8e70c2742c2a6",
	"G",

	/* ecdsa_secp256r1_sha256_p1363_test.json - 169 */
	"ecdsa_secp256r1_sha256_p1363_test.json - 169",
	"04b533d4695dd5b8c5e07757e55e6e516f7e2c88fa0239e23f60e8ec07dd70f2871b134ee58cc583278456863f33c3a85d881f7d4a39850143e29d4eaf009afe47",
	"313233343030",
	"7fffffff800000007fffffffffffffffde737d56d38bcf4279dce5617e3192a8555555550000000055555555555555553ef7a8e48d07df81a693439654210c70",
	"F",

	/* ecdsa_secp256r1_sha256_p1363_test.json - 170 */
	"ecdsa_secp256r1_sha256_p1363_test.json - 170",
	"04f50d371b91bfb1d7d14e1323523bc3aa8cbf2c57f9e284de628c8b4536787b86f94ad887ac94d527247cd2e7d0c8b1291c553c9730405380b14cbb209f5fa2dd",
	"313233343030",
	"7fffffff800000007fffffffffffffffde737d56d38bcf4279dce5617e3192a97fffffff800000007fffffffffffffffde737d56d38bcf4279dce5617e3192a8",
	"G",

	/* ecdsa_secp256r1_sha256_p1363_test.json - 171 */
	"ecdsa_secp256r1_sha256_p1363_test.json - 171",
	"0468ec6e298eafe16539156ce57a14b04a7047c221bafc3a582eaeb0d857c4d94697bed1af17850117fdb39b2324f220a5698ed16c426a27335bb385ac8ca6fb30",
	"313233343030",
	"7fffffff800000007fffffffffffffffde737d56d38bcf4279dce5617e3192a97fffffff800000007fffffffffffffffde737d56d38bcf4279dce5617e3192a9",
	"G",

	/* ecdsa_secp256r1_sha256_p1363_test.json - 172 */
	"ecdsa_secp256r1_sha256_p1363_test.json - 172",
	"0469da0364734d2e530fece94019265fefb781a0f1b08f6c8897bdf6557927c8b866d2d3c7dcd518b23d726960f069ad71a933d86ef8abbcce8b20f71e2a847002",
	"313233343030",
	"555555550000000055555555555555553ef7a8e48d07df81a693439654210c70bb5a52f42f9c9261ed4361f59422a1e30036e7c32b270c8807a419feca605023",
	"G",

	/* ecdsa_secp256r1_sha256_p1363_test.json - 173 */
	"ecdsa_secp256r1_sha256_p1363_test.json - 173",
	"04d8adc00023a8edc02576e2b63e3e30621a471e2b2320620187bf067a1ac1ff3233e2b50ec09807accb36131fff95ed12a09a86b4ea9690aa32861576ba2362e1",
	"313233343030",
	"555555550000000055555555555555553ef7a8e48d07df81a693439654210c7044a5ad0ad0636d9f12bc9e0a6bdd5e1cbcb012ea7bf091fcec15b0c43202d52e",
	"G",

	/* ecdsa_secp256r1_sha256_p1363_test.json - 174 */
	"ecdsa_secp256r1_sha256_p1363_test.json - 174",
	"043623ac973ced0a56fa6d882f03a7d5c7edca02cfc7b2401fab3690dbe75ab7858db06908e64b28613da7257e737f39793da8e713ba0643b92e9bb3252be7f8fe",
	"313233343030",
	"555555550000000055555555555555553ef7a8e48d07df81a693439654210c70555555550000000055555555555555553ef7a8e48d07df81a693439654210c70",
	"G",

	/* ecdsa_secp256r1_sha256_p1363_test.json - 175 */
	"ecdsa_secp256r1_sha256_p1363_test.json - 175",
	"04cf04ea77e9622523d894b93ff52dc3027b31959503b6fa3890e5e04263f922f1e8528fb7c006b3983c8b8400e57b4ed71740c2f3975438821199bedeaecab2e9",
	"313233343030",
	"555555550000000055555555555555553ef7a8e48d07df81a693439654210c70aaaaaaaa00000000aaaaaaaaaaaaaaaa7def51c91a0fbf034d26872ca84218e1",
	"G",

	/* ecdsa_secp256r1_sha256_p1363_test.json - 176 */
	"ecdsa_secp256r1_sha256_p1363_test.json - 176",
	"04db7a2c8a1ab573e5929dc24077b508d7e683d49227996bda3e9f78dbeff773504f417f3bc9a88075c2e0aadd5a13311730cf7cc76a82f11a36eaf08a6c99a206",
	"313233343030",
	"7ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffde91e1ba60fdedb76a46bcb51dc0b8b4b7e019f0a28721885fa5d3a8196623397",
	"G",

	/* ecdsa_secp256r1_sha256_p1363_test.json - 177 */
	"ecdsa_secp256r1_sha256_p1363_test.json - 177",
	"04dead11c7a5b396862f21974dc4752fadeff994efe9bbd05ab413765ea80b6e1f1de3f0640e8ac6edcf89cff53c40e265bb94078a343736df07aa0318fc7fe1ff",
	"313233343030",
	"7ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffdfdea5843ffeb73af94313ba4831b53fe24f799e525b1e8e8c87b59b95b430ad9",
	"G",

	/* ecdsa_secp256r1_sha256_p1363_test.json - 178 */
	"ecdsa_secp256r1_sha256_p1363_test.json - 178",
	"04d0bc472e0d7c81ebaed3a6ef96c18613bb1fea6f994326fbe80e00dfde67c7e9986c723ea4843d48389b946f64ad56c83ad70ff17ba85335667d1bb9fa619efd",
	"313233343030",
	"7ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffd03ffcabf2f1b4d2a65190db1680d62bb994e41c5251cd73b3c3dfc5e5bafc035",
	"G",

	/* ecdsa_secp256r1_sha256_p1363_test.json - 179 */
	"ecdsa_secp256r1_sha256_p1363_test.json - 179",
	"04a0a44ca947d66a2acb736008b9c08d1ab2ad03776e02640f78495d458dd51c326337fe5cf8c4604b1f1c409dc2d872d4294a4762420df43a30a2392e40426add",
	"313233343030",
	"7ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffd4dfbc401f971cd304b33dfdb17d0fed0fe4c1a88ae648e0d2847f74977534989",
	"G",

	/* ecdsa_secp256r1_sha256_p1363_test.json - 180 */
	"ecdsa_secp256r1_sha256_p1363_test.json - 180",
	"04c9c2115290d008b45fb65fad0f602389298c25420b775019d42b62c3ce8a96b73877d25a8080dc02d987ca730f0405c2c9dbefac46f9e601cc3f06e9713973fd",
	"313233343030",
	"7ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffdbc4024761cd2ffd43dfdb17d0fed112b988977055cd3a8e54971eba9cda5ca71",
	"G",

	/* ecdsa_secp256r1_sha256_p1363_test.json - 181 */
	"ecdsa_secp256r1_sha256_p1363_test.json - 181",
	"045eca1ef4c287dddc66b8bccf1b88e8a24c0018962f3c5e7efa83bc1a5ff6033e5e79c4cb2c245b8c45abdce8a8e4da758d92a607c32cd407ecaef22f1c934a71",
	"313233343030",
	"7ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffd788048ed39a5ffa77bfb62fa1fda2257742bf35d128fb3459f2a0c909ee86f91",
	"G",

	/* ecdsa_secp256r1_sha256_p1363_test.json - 182 */
	"ecdsa_secp256r1_sha256_p1363_test.json - 182",
	"045caaa030e7fdf0e4936bc7ab5a96353e0a01e4130c3f8bf22d473e317029a47adeb6adc462f7058f2a20d371e9702254e9b201642005b3ceda926b42b178bef9",
	"313233343030",
	"7ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffd476d9131fd381bd917d0fed112bc9e0a5924b5ed5b11167edd8b23582b3cb15e",
	"G",

	/* ecdsa_secp256r1_sha256_p1363_test.json - 183 */
	"ecdsa_secp256r1_sha256_p1363_test.json - 183",
	"04c2fd20bac06e555bb8ac0ce69eb1ea20f83a1fc3501c8a66469b1a31f619b0986237050779f52b615bd7b8d76a25fc95ca2ed32525c75f27ffc87ac397e6cbaf",
	"313233343030",
	"7ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffd8374253e3e21bd154448d0a8f640fe46fafa8b19ce78d538f6cc0a19662d3601",
	"G",

	/* ecdsa_secp256r1_sha256_p1363_test.json - 184 */
	"ecdsa_secp256r1_sha256_p1363_test.json - 184",
	"043fd6a1ca7f77fb3b0bbe726c372010068426e11ea6ae78ce17bedae4bba86ced03ce5516406bf8cfaab8745eac1cd69018ad6f50b5461872ddfc56e0db3c8ff4",
	"313233343030",
	"7ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffd357cfd3be4d01d413c5b9ede36cba5452c11ee7fe14879e749ae6a2d897a52d6",
	"G",

	/* ecdsa_secp256r1_sha256_p1363_test.json - 185 */
	"ecdsa_secp256r1_sha256_p1363_test.json - 185",
	"049cb8e51e27a5ae3b624a60d6dc32734e4989db20e9bca3ede1edf7b086911114b4c104ab3c677e4b36d6556e8ad5f523410a19f2e277aa895fc57322b4427544",
	"313233343030",
	"7ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffd29798c5c0ee287d4a5e8e6b799fd86b8df5225298e6ffc807cd2f2bc27a0a6d8",
	"G",

	/* ecdsa_secp256r1_sha256_p1363_test.json - 186 */
	"ecdsa_secp256r1_sha256_p1363_test.json - 186",
	"04a3e52c156dcaf10502620b7955bc2b40bc78ef3d569e1223c262512d8f49602a4a2039f31c1097024ad3cc86e57321de032355463486164cf192944977df147f",
	"313233343030",
	"7ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffd0b70f22c781092452dca1a5711fa3a5a1f72add1bf52c2ff7cae4820b30078dd",
	"G",

	/* ecdsa_secp256r1_sha256_p1363_test.json - 187 */
	"ecdsa_secp256r1_sha256_p1363_test.json - 187",
	"04f19b78928720d5bee8e670fb90010fb15c37bf91b58a5157c3f3c059b2655e88cf701ec962fb4a11dcf273f5dc357e58468560c7cfeb942d074abd4329260509",
	"313233343030",
	"7ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffd16e1e458f021248a5b9434ae23f474b43ee55ba37ea585fef95c90416600f1ba",
	"G",

	/* ecdsa_secp256r1_sha256_p1363_test.json - 188 */
	"ecdsa_secp256r1_sha256_p1363_test.json - 188",
	"0483a744459ecdfb01a5cf52b27a05bb7337482d242f235d7b4cb89345545c90a8c05d49337b9649813287de9ffe90355fd905df5f3c32945828121f37cc50de6e",
	"313233343030",
	"7ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffd2252d6856831b6cf895e4f0535eeaf0e5e5809753df848fe760ad86219016a97",
	"G",

	/* ecdsa_secp256r1_sha256_p1363_test.json - 189 */
	"ecdsa_secp256r1_sha256_p1363_test.json - 189",
	"04dd13c6b34c56982ddae124f039dfd23f4b19bbe88cee8e528ae51e5d6f3a21d7bfad4c2e6f263fe5eb59ca974d039fc0e4c3345692fb5320bdae4bd3b42a45ff",
	"313233343030",
	"7ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffd81ffe55f178da695b28c86d8b406b15dab1a9e39661a3ae017fbe390ac0972c3",
	"G",

	/* ecdsa_secp256r1_sha256_p1363_test.json - 190 */
	"ecdsa_secp256r1_sha256_p1363_test.json - 190",
	"0467e6f659cdde869a2f65f094e94e5b4dfad636bbf95192feeed01b0f3deb7460a37e0a51f258b7aeb51dfe592f5cfd5685bbe58712c8d9233c62886437c38ba0",
	"313233343030",
	"7ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffd7fffffffaaaaaaaaffffffffffffffffe9a2538f37b28a2c513dee40fecbb71a",
	"G",

	/* ecdsa_secp256r1_sha256_p1363_test.json - 191 */
	"ecdsa_secp256r1_sha256_p1363_test.json - 191",
	"042eb6412505aec05c6545f029932087e490d05511e8ec1f599617bb367f9ecaaf805f51efcc4803403f9b1ae0124890f06a43fedcddb31830f6669af292895cb0",
	"313233343030",
	"7ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffdb62f26b5f2a2b26f6de86d42ad8a13da3ab3cccd0459b201de009e526adf21f2",
	"G",

	/* ecdsa_secp256r1_sha256_p1363_test.json - 192 */
	"ecdsa_secp256r1_sha256_p1363_test.json - 192",
	"0484db645868eab35e3a9fd80e056e2e855435e3a6b68d75a50a854625fe0d7f356d2589ac655edc9a11ef3e075eddda9abf92e72171570ef7bf43a2ee39338cfe",
	"313233343030",
	"7ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffdbb1d9ac949dd748cd02bbbe749bd351cd57b38bb61403d700686aa7b4c90851e",
	"G",

	/* ecdsa_secp256r1_sha256_p1363_test.json - 193 */
	"ecdsa_secp256r1_sha256_p1363_test.json - 193",
	"0491b9e47c56278662d75c0983b22ca8ea6aa5059b7a2ff7637eb2975e386ad66349aa8ff283d0f77c18d6d11dc062165fd13c3c0310679c1408302a16854ecfbd",
	"313233343030",
	"7ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffd66755a00638cdaec1c732513ca0234ece52545dac11f816e818f725b4f60aaf2",
	"G",

	/* ecdsa_secp256r1_sha256_p1363_test.json - 194 */
	"ecdsa_secp256r1_sha256_p1363_test.json - 194",
	"04f3ec2f13caf04d0192b47fb4c5311fb6d4dc6b0a9e802e5327f7ec5ee8e4834df97e3e468b7d0db867d6ecfe81e2b0f9531df87efdb47c1338ac321fefe5a432",
	"313233343030",
	"7ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffd55a00c9fcdaebb6032513ca0234ecfffe98ebe492fdf02e48ca48e982beb3669",
	"G",

	/* ecdsa_secp256r1_sha256_p1363_test.json - 195 */
	"ecdsa_secp256r1_sha256_p1363_test.json - 195",
	"04d92b200aefcab6ac7dafd9acaf2fa10b3180235b8f46b4503e4693c670fccc885ef2f3aebf5b317475336256768f7c19efb7352d27e4cccadc85b6b8ab922c72",
	"313233343030",
	"7ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffdab40193f9b5d76c064a27940469d9fffd31d7c925fbe05c919491d3057d66cd2",
	"G",

	/* ecdsa_secp256r1_sha256_p1363_test.json - 196 */
	"ecdsa_secp256r1_sha256_p1363_test.json - 196",
	"040a88361eb92ecca2625b38e5f98bbabb96bf179b3d76fc48140a3bcd881523cde6bdf56033f84a5054035597375d90866aa2c96b86a41ccf6edebf47298ad489",
	"313233343030",
	"7ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffdca0234ebb5fdcb13ca0234ecffffffffcb0dadbbc7f549f8a26b4408d0dc8600",
	"G",

	/* ecdsa_secp256r1_sha256_p1363_test.json - 197 */
	"ecdsa_secp256r1_sha256_p1363_test.json - 197",
	"04d0fb17ccd8fafe827e0c1afc5d8d80366e2b20e7f14a563a2ba50469d84375e868612569d39e2bb9f554355564646de99ac602cc6349cf8c1e236a7de7637d93",
	"313233343030",
	"7ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffdbfffffff3ea3677e082b9310572620ae19933a9e65b285598711c77298815ad3",
	"G",

	/* ecdsa_secp256r1_sha256_p1363_test.json - 198 */
	"ecdsa_secp256r1_sha256_p1363_test.json - 198",
	"04836f33bbc1dc0d3d3abbcef0d91f11e2ac4181076c9af0a22b1e4309d3edb2769ab443ff6f901e30c773867582997c2bec2b0cb8120d760236f3a95bbe881f75",
	"313233343030",
	"7ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffd266666663bbbbbbbe6666666666666665b37902e023fab7c8f055d86e5cc41f4",
	"G",

	/* ecdsa_secp256r1_sha256_p1363_test.json - 199 */
	"ecdsa_secp256r1_sha256_p1363_test.json - 199",
	"0492f99fbe973ed4a299719baee4b432741237034dec8d72ba5103cb33e55feeb8033dd0e91134c734174889f3ebcf1b7a1ac05767289280ee7a794cebd6e69697",
	"313233343030",
	"7ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffdbfffffff36db6db7a492492492492492146c573f4c6dfc8d08a443e258970b09",
	"G",

	/* ecdsa_secp256r1_sha256_p1363_test.json - 200 */
	"ecdsa_secp256r1_sha256_p1363_test.json - 200",
	"04d35ba58da30197d378e618ec0fa7e2e2d12cffd73ebbb2049d130bba434af09eff83986e6875e41ea432b7585a49b3a6c77cbb3c47919f8e82874c794635c1d2",
	"313233343030",
	"7ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffdbfffffff2aaaaaab7fffffffffffffffc815d0e60b3e596ecb1ad3a27cfd49c4",
	"G",

	/* ecdsa_secp256r1_sha256_p1363_test.json - 201 */
	"ecdsa_secp256r1_sha256_p1363_test.json - 201",
	"048651ce490f1b46d73f3ff475149be29136697334a519d7ddab0725c8d0793224e11c65bd8ca92dc8bc9ae82911f0b52751ce21dd9003ae60900bd825f590cc28",
	"313233343030",
	"7ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffd7fffffff55555555ffffffffffffffffd344a71e6f651458a27bdc81fd976e37",
	"G",

	/* ecdsa_secp256r1_sha256_p1363_test.json - 202 */
	"ecdsa_secp256r1_sha256_p1363_test.json - 202",
	"046d8e1b12c831a0da8795650ff95f101ed921d9e2f72b15b1cdaca9826b9cfc6def6d63e2bc5c089570394a4bc9f892d5e6c7a6a637b20469a58c106ad486bf37",
	"313233343030",
	"7ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffd3fffffff800000007fffffffffffffffde737d56d38bcf4279dce5617e3192aa",
	"G",

	/* ecdsa_secp256r1_sha256_p1363_test.json - 203 */
	"ecdsa_secp256r1_sha256_p1363_test.json - 203",
	"040ae580bae933b4ef2997cbdbb0922328ca9a410f627a0f7dff24cb4d920e15428911e7f8cc365a8a88eb81421a361ccc2b99e309d8dcd9a98ba83c3949d893e3",
	"313233343030",
	"7ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffd5d8ecd64a4eeba466815ddf3a4de9a8e6abd9c5db0a01eb80343553da648428f",
	"G",

	/* ecdsa_secp256r1_sha256_p1363_test.json - 204 */
	"ecdsa_secp256r1_sha256_p1363_test.json - 204",
	"045b812fd521aafa69835a849cce6fbdeb6983b442d2444fe70e134c027fc46963838a40f2a36092e9004e92d8d940cf5638550ce672ce8b8d4e15eba5499249e9",
	"313233343030",
	"6f2347cab7dd76858fe0555ac3bc99048c4aacafdfb6bcbe05ea6c42c4934569bb726660235793aa9957a61e76e00c2c435109cf9a15dd624d53f4301047856b",
	"G",

	/* ecdsa_secp256r1_sha256_p1363_test.json - 205 */
	"ecdsa_secp256r1_sha256_p1363_test.json - 205",
	"045b812fd521aafa69835a849cce6fbdeb6983b442d2444fe70e134c027fc469637c75bf0c5c9f6d17ffb16d2726bf30a9c7aaf31a8d317472b1ea145ab66db616",
	"313233343030",
	"6f2347cab7dd76858fe0555ac3bc99048c4aacafdfb6bcbe05ea6c42c4934569bb726660235793aa9957a61e76e00c2c435109cf9a15dd624d53f4301047856b",
	"F",

	/* ecdsa_secp256r1_sha256_p1363_test.json - 206 */
	"ecdsa_secp256r1_sha256_p1363_test.json - 206",
	"046adda82b90261b0f319faa0d878665a6b6da497f09c903176222c34acfef72a647e6f50dcc40ad5d9b59f7602bb222fad71a41bf5e1f9df4959a364c62e488d9",
	"313233343030",
	"0000000000000000000000000000000000000000000000000000000000000001555555550000000055555555555555553ef7a8e48d07df81a693439654210c70",
	"F",

	/* ecdsa_secp256r1_sha256_p1363_test.json - 207 */
	"ecdsa_secp256r1_sha256_p1363_test.json - 207",
	"042fca0d0a47914de77ed56e7eccc3276a601120c6df0069c825c8f6a01c9f382065f3450a1d17c6b24989a39beb1c7decfca8384fbdc294418e5d807b3c6ed7de",
	"313233343030",
	"010000000000000000000000000000000000000000000000000000000000000000003333333300000000333333333333333325c7cbbc549e52e763f1f55a327a3aa9",
	"F",

	/* ecdsa_secp256r1_sha256_p1363_test.json - 208 */
	"ecdsa_secp256r1_sha256_p1363_test.json - 208",
	"04dd86d3b5f4a13e8511083b78002081c53ff467f11ebd98a51a633db76665d25045d5c8200c89f2fa10d849349226d21d8dfaed6ff8d5cb3e1b7e17474ebc18f7",
	"313233343030",
	"555555550000000055555555555555553ef7a8e48d07df81a693439654210c703333333300000000333333333333333325c7cbbc549e52e763f1f55a327a3aa9",
	"F",

	/* ecdsa_secp256r1_sha256_p1363_test.json - 209 */
	"ecdsa_secp256r1_sha256_p1363_test.json - 209",
	"044fea55b32cb32aca0c12c4cd0abfb4e64b0f5a516e578c016591a93f5a0fbcc5d7d3fd10b2be668c547b212f6bb14c88f0fecd38a8a4b2c785ed3be62ce4b280",
	"313233343030",
	"7cf27b188d034f7e8a52380304b51ac3c08969e277f21b35a60b48fc47669978555555550000000055555555555555553ef7a8e48d07df81a693439654210c70",
	"G",

	/* ecdsa_secp256r1_sha256_p1363_test.json - 210 */
	"ecdsa_secp256r1_sha256_p1363_test.json - 210",
	"04c6a771527024227792170a6f8eee735bf32b7f98af669ead299802e32d7c3107bc3b4b5e65ab887bbd343572b3e5619261fe3a073e2ffd78412f726867db589e",
	"313233343030",
	"7cf27b188d034f7e8a52380304b51ac3c08969e277f21b35a60b48fc47669978b6db6db6249249254924924924924924625bd7a09bec4ca81bcdd9f8fd6b63cc",
	"G",

	/* ecdsa_secp256r1_sha256_p1363_test.json - 211 */
	"ecdsa_secp256r1_sha256_p1363_test.json - 211",
	"04851c2bbad08e54ec7a9af99f49f03644d6ec6d59b207fec98de85a7d15b956efcee9960283045075684b410be8d0f7494b91aa2379f60727319f10ddeb0fe9d6",
	"313233343030",
	"7cf27b188d034f7e8a52380304b51ac3c08969e277f21b35a60b48fc47669978cccccccc00000000cccccccccccccccc971f2ef152794b9d8fc7d568c9e8eaa7",
	"G",

	/* ecdsa_secp256r1_sha256_p1363_test.json - 212 */
	"ecdsa_secp256r1_sha256_p1363_test.json - 212",
	"04f6417c8a670584e388676949e53da7fc55911ff68318d1bf3061205acb19c48f8f2b743df34ad0f72674acb7505929784779cd9ac916c3669ead43026ab6d43f",
	"313233343030",
	"7cf27b188d034f7e8a52380304b51ac3c08969e277f21b35a60b48fc476699783333333300000000333333333333333325c7cbbc549e52e763f1f55a327a3aaa",
	"G",

	/* ecdsa_secp256r1_sha256_p1363_test.json - 213 */
	"ecdsa_secp256r1_sha256_p1363_test.json - 213",
	"04501421277be45a5eefec6c639930d636032565af420cf3373f557faa7f8a06438673d6cb6076e1cfcdc7dfe7384c8e5cac08d74501f2ae6e89cad195d0aa1371",
	"313233343030",
	"7cf27b188d034f7e8a52380304b51ac3c08969e277f21b35a60b48fc4766997849249248db6db6dbb6db6db6db6db6db5a8b230d0b2b51dcd7ebf0c9fef7c185",
	"G",

	/* ecdsa_secp256r1_sha256_p1363_test.json - 214 */
	"ecdsa_secp256r1_sha256_p1363_test.json - 214",
	"040d935bf9ffc115a527735f729ca8a4ca23ee01a4894adf0e3415ac84e808bb343195a3762fea29ed38912bd9ea6c4fde70c3050893a4375850ce61d82eba33c5",
	"313233343030",
	"7cf27b188d034f7e8a52380304b51ac3c08969e277f21b35a60b48fc4766997816a4502e2781e11ac82cbc9d1edd8c981584d13e18411e2f6e0478c34416e3bb",
	"G",

	/* ecdsa_secp256r1_sha256_p1363_test.json - 215 */
	"ecdsa_secp256r1_sha256_p1363_test.json - 215",
	"045e59f50708646be8a589355014308e60b668fb670196206c41e748e64e4dca215de37fee5c97bcaf7144d5b459982f52eeeafbdf03aacbafef38e213624a01de",
	"313233343030",
	"6b17d1f2e12c4247f8bce6e563a440f277037d812deb33a0f4a13945d898c296555555550000000055555555555555553ef7a8e48d07df81a693439654210c70",
	"G",

	/* ecdsa_secp256r1_sha256_p1363_test.json - 216 */
	"ecdsa_secp256r1_sha256_p1363_test.json - 216",
	"04169fb797325843faff2f7a5b5445da9e2fd6226f7ef90ef0bfe924104b02db8e7bbb8de662c7b9b1cf9b22f7a2e582bd46d581d68878efb2b861b131d8a1d667",
	"313233343030",
	"6b17d1f2e12c4247f8bce6e563a440f277037d812deb33a0f4a13945d898c296b6db6db6249249254924924924924924625bd7a09bec4ca81bcdd9f8fd6b63cc",
	"G",

	/* ecdsa_secp256r1_sha256_p1363_test.json - 217 */
	"ecdsa_secp256r1_sha256_p1363_test.json - 217",
	"04271cd89c000143096b62d4e9e4ca885aef2f7023d18affdaf8b7b548981487540a1c6e954e32108435b55fa385b0f76481a609b9149ccb4b02b2ca47fe8e4da5",
	"313233343030",
	"6b17d1f2e12c4247f8bce6e563a440f277037d812deb33a0f4a13945d898c296cccccccc00000000cccccccccccccccc971f2ef152794b9d8fc7d568c9e8eaa7",
	"G",

	/* ecdsa_secp256r1_sha256_p1363_test.json - 218 */
	"ecdsa_secp256r1_sha256_p1363_test.json - 218",
	"043d0bc7ed8f09d2cb7ddb46ebc1ed799ab1563a9ab84bf524587a220afe499c12e22dc3b3c103824a4f378d96adb0a408abf19ce7d68aa6244f78cb216fa3f8df",
	"313233343030",
	"6b17d1f2e12c4247f8bce6e563a440f277037d812deb33a0f4a13945d898c2963333333300000000333333333333333325c7cbbc549e52e763f1f55a327a3aaa",
	"G",

	/* ecdsa_secp256r1_sha256_p1363_test.json - 219 */
	"ecdsa_secp256r1_sha256_p1363_test.json - 219",
	"04a6c885ade1a4c566f9bb010d066974abb281797fa701288c721bcbd23663a9b72e424b690957168d193a6096fc77a2b004a9c7d467e007e1f2058458f98af316",
	"313233343030",
	"6b17d1f2e12c4247f8bce6e563a440f277037d812deb33a0f4a13945d898c29649249248db6db6dbb6db6db6db6db6db5a8b230d0b2b51dcd7ebf0c9fef7c185",
	"G",

	/* ecdsa_secp256r1_sha256_p1363_test.json - 220 */
	"ecdsa_secp256r1_sha256_p1363_test.json - 220",
	"048d3c2c2c3b765ba8289e6ac3812572a25bf75df62d87ab7330c3bdbad9ebfa5c4c6845442d66935b238578d43aec54f7caa1621d1af241d4632e0b780c423f5d",
	"313233343030",
	"6b17d1f2e12c4247f8bce6e563a440f277037d812deb33a0f4a13945d898c29616a4502e2781e11ac82cbc9d1edd8c981584d13e18411e2f6e0478c34416e3bb",
	"G",

	/* ecdsa_secp256r1_sha256_p1363_test.json - 221 */
	"ecdsa_secp256r1_sha256_p1363_test.json - 221",
	"046b17d1f2e12c4247f8bce6e563a440f277037d812deb33a0f4a13945d898c2964fe342e2fe1a7f9b8ee7eb4a7c0f9e162bce33576b315ececbb6406837bf51f5",
	"313233343030",
	"bb5a52f42f9c9261ed4361f59422a1e30036e7c32b270c8807a419feca605023249249246db6db6ddb6db6db6db6db6dad4591868595a8ee6bf5f864ff7be0c2",
	"F",

	/* ecdsa_secp256r1_sha256_p1363_test.json - 222 */
	"ecdsa_secp256r1_sha256_p1363_test.json - 222",
	"046b17d1f2e12c4247f8bce6e563a440f277037d812deb33a0f4a13945d898c2964fe342e2fe1a7f9b8ee7eb4a7c0f9e162bce33576b315ececbb6406837bf51f5",
	"313233343030",
	"44a5ad0ad0636d9f12bc9e0a6bdd5e1cbcb012ea7bf091fcec15b0c43202d52e249249246db6db6ddb6db6db6db6db6dad4591868595a8ee6bf5f864ff7be0c2",
	"F",

	/* ecdsa_secp256r1_sha256_p1363_test.json - 223 */
	"ecdsa_secp256r1_sha256_p1363_test.json - 223",
	"046b17d1f2e12c4247f8bce6e563a440f277037d812deb33a0f4a13945d898c296b01cbd1c01e58065711814b583f061e9d431cca994cea1313449bf97c840ae0a",
	"313233343030",
	"bb5a52f42f9c9261ed4361f59422a1e30036e7c32b270c8807a419feca605023249249246db6db6ddb6db6db6db6db6dad4591868595a8ee6bf5f864ff7be0c2",
	"F",

	/* ecdsa_secp256r1_sha256_p1363_test.json - 224 */
	"ecdsa_secp256r1_sha256_p1363_test.json - 224",
	"046b17d1f2e12c4247f8bce6e563a440f277037d812deb33a0f4a13945d898c296b01cbd1c01e58065711814b583f061e9d431cca994cea1313449bf97c840ae0a",
	"313233343030",
	"44a5ad0ad0636d9f12bc9e0a6bdd5e1cbcb012ea7bf091fcec15b0c43202d52e249249246db6db6ddb6db6db6db6db6dad4591868595a8ee6bf5f864ff7be0c2",
	"F",

	/* ecdsa_secp256r1_sha256_p1363_test.json - 225 */
	"ecdsa_secp256r1_sha256_p1363_test.json - 225",
	"0404aaec73635726f213fb8a9e64da3b8632e41495a944d0045b522eba7240fad587d9315798aaa3a5ba01775787ced05eaaf7b4e09fc81d6d1aa546e8365d525d",
	"",
	"b292a619339f6e567a305c951c0dcbcc42d16e47f219f9e98e76e09d8770b34a0177e60492c5a8242f76f07bfe3661bde59ec2a17ce5bd2dab2abebdf89a62e2",
	"G",

	/* ecdsa_secp256r1_sha256_p1363_test.json - 226 */
	"ecdsa_secp256r1_sha256_p1363_test.json - 226",
	"0404aaec73635726f213fb8a9e64da3b8632e41495a944d0045b522eba7240fad587d9315798aaa3a5ba01775787ced05eaaf7b4e09fc81d6d1aa546e8365d525d",
	"4d7367",
	"530bd6b0c9af2d69ba897f6b5fb59695cfbf33afe66dbadcf5b8d2a2a6538e23d85e489cb7a161fd55ededcedbf4cc0c0987e3e3f0f242cae934c72caa3f43e9",
	"G",

	/* ecdsa_secp256r1_sha256_p1363_test.json - 227 */
	"ecdsa_secp256r1_sha256_p1363_test.json - 227",
	"0404aaec73635726f213fb8a9e64da3b8632e41495a944d0045b522eba7240fad587d9315798aaa3a5ba01775787ced05eaaf7b4e09fc81d6d1aa546e8365d525d",
	"313233343030",
	"a8ea150cb80125d7381c4c1f1da8e9de2711f9917060406a73d7904519e51388f3ab9fa68bd47973a73b2d40480c2ba50c22c9d76ec217257288293285449b86",
	"G",

	/* ecdsa_secp256r1_sha256_p1363_test.json - 228 */
	"ecdsa_secp256r1_sha256_p1363_test.json - 228",
	"0404aaec73635726f213fb8a9e64da3b8632e41495a944d0045b522eba7240fad587d9315798aaa3a5ba01775787ced05eaaf7b4e09fc81d6d1aa546e8365d525d",
	"0000000000000000000000000000000000000000",
	"986e65933ef2ed4ee5aada139f52b70539aaf63f00a91f29c69178490d57fb713dafedfb8da6189d372308cbf1489bbbdabf0c0217d1c0ff0f701aaa7a694b9c",
	"G",

	/* ecdsa_secp256r1_sha256_p1363_test.json - 229 */
	"ecdsa_secp256r1_sha256_p1363_test.json - 229",
	"044f337ccfd67726a805e4f1600ae2849df3807eca117380239fbd816900000000ed9dea124cc8c396416411e988c30f427eb504af43a3146cd5df7ea60666d685",
	"4d657373616765",
	"d434e262a49eab7781e353a3565e482550dd0fd5defa013c7f29745eff3569f19b0c0a93f267fb6052fd8077be769c2b98953195d7bc10de844218305c6ba17a",
	"G",

	/* ecdsa_secp256r1_sha256_p1363_test.json - 230 */
	"ecdsa_secp256r1_sha256_p1363_test.json - 230",
	"044f337ccfd67726a805e4f1600ae2849df3807eca117380239fbd816900000000ed9dea124cc8c396416411e988c30f427eb504af43a3146cd5df7ea60666d685",
	"4d657373616765",
	"0fe774355c04d060f76d79fd7a772e421463489221bf0a33add0be9b1979110b500dcba1c69a8fbd43fa4f57f743ce124ca8b91a1f325f3fac6181175df55737",
	"G",

	/* ecdsa_secp256r1_sha256_p1363_test.json - 231 */
	"ecdsa_secp256r1_sha256_p1363_test.json - 231",
	"044f337ccfd67726a805e4f1600ae2849df3807eca117380239fbd816900000000ed9dea124cc8c396416411e988c30f427eb504af43a3146cd5df7ea60666d685",
	"4d657373616765",
	"bb40bf217bed3fb3950c7d39f03d36dc8e3b2cd79693f125bfd06595ee1135e3541bf3532351ebb032710bdb6a1bf1bfc89a1e291ac692b3fa4780745bb55677",
	"G",

	/* ecdsa_secp256r1_sha256_p1363_test.json - 232 */
	"ecdsa_secp256r1_sha256_p1363_test.json - 232",
	"043cf03d614d8939cfd499a07873fac281618f06b8ff87e8015c3f49726500493584fa174d791c72bf2ce3880a8960dd2a7c7a1338a82f85a9e59cdbde80000000",
	"4d657373616765",
	"664eb7ee6db84a34df3c86ea31389a5405badd5ca99231ff556d3e75a233e73a59f3c752e52eca46137642490a51560ce0badc678754b8f72e51a2901426a1bd",
	"G",

	/* ecdsa_secp256r1_sha256_p1363_test.json - 233 */
	"ecdsa_secp256r1_sha256_p1363_test.json - 233",
	"043cf03d614d8939cfd499a07873fac281618f06b8ff87e8015c3f49726500493584fa174d791c72bf2ce3880a8960dd2a7c7a1338a82f85a9e59cdbde80000000",
	"4d657373616765",
	"4cd0429bbabd2827009d6fcd843d4ce39c3e42e2d1631fd001985a79d1fd8b439638bf12dd682f60be7ef1d0e0d98f08b7bca77a1a2b869ae466189d2acdabe3",
	"G",

	/* ecdsa_secp256r1_sha256_p1363_test.json - 234 */
	"ecdsa_secp256r1_sha256_p1363_test.json - 234",
	"043cf03d614d8939cfd499a07873fac281618f06b8ff87e8015c3f49726500493584fa174d791c72bf2ce3880a8960dd2a7c7a1338a82f85a9e59cdbde80000000",
	"4d657373616765",
	"e56c6ea2d1b017091c44d8b6cb62b9f460e3ce9aed5e5fd41e8added97c56c04a308ec31f281e955be20b457e463440b4fcf2b80258078207fc1378180f89b55",
	"G",

	/* ecdsa_secp256r1_sha256_p1363_test.json - 235 */
	"ecdsa_secp256r1_sha256_p1363_test.json - 235",
	"043cf03d614d8939cfd499a07873fac281618f06b8ff87e8015c3f4972650049357b05e8b186e38d41d31c77f5769f22d58385ecc857d07a561a6324217fffffff",
	"4d657373616765",
	"1158a08d291500b4cabed3346d891eee57c176356a2624fb011f8fbbf3466830228a8c486a736006e082325b85290c5bc91f378b75d487dda46798c18f285519",
	"G",

	/* ecdsa_secp256r1_sha256_p1363_test.json - 236 */
	"ecdsa_secp256r1_sha256_p1363_test.json - 236",
	"043cf03d614d8939cfd499a07873fac281618f06b8ff87e8015c3f4972650049357b05e8b186e38d41d31c77f5769f22d58385ecc857d07a561a6324217fffffff",
	"4d657373616765",
	"b1db9289649f59410ea36b0c0fc8d6aa2687b29176939dd23e0dde56d309fa9d3e1535e4280559015b0dbd987366dcf43a6d1af5c23c7d584e1c3f48a1251336",
	"G",

	/* ecdsa_secp256r1_sha256_p1363_test.json - 237 */
	"ecdsa_secp256r1_sha256_p1363_test.json - 237",
	"043cf03d614d8939cfd499a07873fac281618f06b8ff87e8015c3f4972650049357b05e8b186e38d41d31c77f5769f22d58385ecc857d07a561a6324217fffffff",
	"4d657373616765",
	"b7b16e762286cb96446aa8d4e6e7578b0a341a79f2dd1a220ac6f0ca4e24ed86ddc60a700a139b04661c547d07bbb0721780146df799ccf55e55234ecb8f12bc",
	"G",

	/* ecdsa_secp256r1_sha256_p1363_test.json - 238 */
	"ecdsa_secp256r1_sha256_p1363_test.json - 238",
	"042829c31faa2e400e344ed94bca3fcd0545956ebcfe8ad0f6dfa5ff8effffffffa01aafaf000e52585855afa7676ade284113099052df57e7eb3bd37ebeb9222e",
	"4d657373616765",
	"d82a7c2717261187c8e00d8df963ff35d796edad36bc6e6bd1c91c670d9105b43dcabddaf8fcaa61f4603e7cbac0f3c0351ecd5988efb23f680d07debd139929",
	"G",

	/* ecdsa_secp256r1_sha256_p1363_test.json - 239 */
	"ecdsa_secp256r1_sha256_p1363_test.json - 239",
	"042829c31faa2e400e344ed94bca3fcd0545956ebcfe8ad0f6dfa5ff8effffffffa01aafaf000e52585855afa7676ade284113099052df57e7eb3bd37ebeb9222e",
	"4d657373616765",
	"5eb9c8845de68eb13d5befe719f462d77787802baff30ce96a5cba063254af782c026ae9be2e2a5e7ca0ff9bbd92fb6e44972186228ee9a62b87ddbe2ef66fb5",
	"G",

	/* ecdsa_secp256r1_sha256_p1363_test.json - 240 */
	"ecdsa_secp256r1_sha256_p1363_test.json - 240",
	"042829c31faa2e400e344ed94bca3fcd0545956ebcfe8ad0f6dfa5ff8effffffffa01aafaf000e52585855afa7676ade284113099052df57e7eb3bd37ebeb9222e",
	"4d657373616765",
	"96843dd03c22abd2f3b782b170239f90f277921becc117d0404a8e4e36230c28f2be378f526f74a543f67165976de9ed9a31214eb4d7e6db19e1ede123dd991d",
	"G",

	/* ecdsa_secp256r1_sha256_p1363_test.json - 241 */
	"ecdsa_secp256r1_sha256_p1363_test.json - 241",
	"04fffffff948081e6a0458dd8f9e738f2665ff9059ad6aac0708318c4ca9a7a4f55a8abcba2dda8474311ee54149b973cae0c0fb89557ad0bf78e6529a1663bd73",
	"4d657373616765",
	"766456dce1857c906f9996af729339464d27e9d98edc2d0e3b760297067421f6402385ecadae0d8081dccaf5d19037ec4e55376eced699e93646bfbbf19d0b41",
	"G",

	/* ecdsa_secp256r1_sha256_p1363_test.json - 242 */
	"ecdsa_secp256r1_sha256_p1363_test.json - 242",
	"04fffffff948081e6a0458dd8f9e738f2665ff9059ad6aac0708318c4ca9a7a4f55a8abcba2dda8474311ee54149b973cae0c0fb89557ad0bf78e6529a1663bd73",
	"4d657373616765",
	"c605c4b2edeab20419e6518a11b2dbc2b97ed8b07cced0b19c34f777de7b9fd9edf0f612c5f46e03c719647bc8af1b29b2cde2eda700fb1cff5e159d47326dba",
	"G",

	/* ecdsa_secp256r1_sha256_p1363_test.json - 243 */
	"ecdsa_secp256r1_sha256_p1363_test.json - 243",
	"04fffffff948081e6a0458dd8f9e738f2665ff9059ad6aac0708318c4ca9a7a4f55a8abcba2dda8474311ee54149b973cae0c0fb89557ad0bf78e6529a1663bd73",
	"4d657373616765",
	"d48b68e6cabfe03cf6141c9ac54141f210e64485d9929ad7b732bfe3b7eb8a84feedae50c61bd00e19dc26f9b7e2265e4508c389109ad2f208f0772315b6c941",
	"G",

	/* ecdsa_secp256r1_sha256_p1363_test.json - 244 */
	"ecdsa_secp256r1_sha256_p1363_test.json - 244",
	"0400000003fa15f963949d5f03a6f5c7f86f9e0015eeb23aebbff1173937ba748e1099872070e8e87c555fa13659cca5d7fadcfcb0023ea889548ca48af2ba7e71",
	"4d657373616765",
	"b7c81457d4aeb6aa65957098569f0479710ad7f6595d5874c35a93d12a5dd4c7b7961a0b652878c2d568069a432ca18a1a9199f2ca574dad4b9e3a05c0a1cdb3",
	"G",

	/* ecdsa_secp256r1_sha256_p1363_test.json - 245 */
	"ecdsa_secp256r1_sha256_p1363_test.json - 245",
	"0400000003fa15f963949d5f03a6f5c7f86f9e0015eeb23aebbff1173937ba748e1099872070e8e87c555fa13659cca5d7fadcfcb0023ea889548ca48af2ba7e71",
	"4d657373616765",
	"6b01332ddb6edfa9a30a1321d5858e1ee3cf97e263e669f8de5e9652e76ff3f75939545fced457309a6a04ace2bd0f70139c8f7d86b02cb1cc58f9e69e96cd5a",
	"G",

	/* ecdsa_secp256r1_sha256_p1363_test.json - 246 */
	"ecdsa_secp256r1_sha256_p1363_test.json - 246",
	"0400000003fa15f963949d5f03a6f5c7f86f9e0015eeb23aebbff1173937ba748e1099872070e8e87c555fa13659cca5d7fadcfcb0023ea889548ca48af2ba7e71",
	"4d657373616765",
	"efdb884720eaeadc349f9fc356b6c0344101cd2fd8436b7d0e6a4fb93f106361f24bee6ad5dc05f7613975473aadf3aacba9e77de7d69b6ce48cb60d8113385d",
	"G",

	/* ecdsa_secp256r1_sha256_p1363_test.json - 247 */
	"ecdsa_secp256r1_sha256_p1363_test.json - 247",
	"04bcbb2914c79f045eaa6ecbbc612816b3be5d2d6796707d8125e9f851c18af015000000001352bb4a0fa2ea4cceb9ab63dd684ade5a1127bcf300a698a7193bc2",
	"4d657373616765",
	"31230428405560dcb88fb5a646836aea9b23a23dd973dcbe8014c87b8b20eb070f9344d6e812ce166646747694a41b0aaf97374e19f3c5fb8bd7ae3d9bd0beff",
	"G",

	/* ecdsa_secp256r1_sha256_p1363_test.json - 248 */
	"ecdsa_secp256r1_sha256_p1363_test.json - 248",
	"04bcbb2914c79f045eaa6ecbbc612816b3be5d2d6796707d8125e9f851c18af015000000001352bb4a0fa2ea4cceb9ab63dd684ade5a1127bcf300a698a7193bc2",
	"4d657373616765",
	"caa797da65b320ab0d5c470cda0b36b294359c7db9841d679174db34c4855743cf543a62f23e212745391aaf7505f345123d2685ee3b941d3de6d9b36242e5a0",
	"G",

	/* ecdsa_secp256r1_sha256_p1363_test.json - 249 */
	"ecdsa_secp256r1_sha256_p1363_test.json - 249",
	"04bcbb2914c79f045eaa6ecbbc612816b3be5d2d6796707d8125e9f851c18af015000000001352bb4a0fa2ea4cceb9ab63dd684ade5a1127bcf300a698a7193bc2",
	"4d657373616765",
	"7e5f0ab5d900d3d3d7867657e5d6d36519bc54084536e7d21c336ed8001859459450c07f201faec94b82dfb322e5ac676688294aad35aa72e727ff0b19b646aa",
	"G",

	/* ecdsa_secp256r1_sha256_p1363_test.json - 250 */
	"ecdsa_secp256r1_sha256_p1363_test.json - 250",
	"04bcbb2914c79f045eaa6ecbbc612816b3be5d2d6796707d8125e9f851c18af015fffffffeecad44b6f05d15b33146549c2297b522a5eed8430cff596758e6c43d",
	"4d657373616765",
	"d7d70c581ae9e3f66dc6a480bf037ae23f8a1e4a2136fe4b03aa69f0ca25b35689c460f8a5a5c2bbba962c8a3ee833a413e85658e62a59e2af41d9127cc47224",
	"G",

	/* ecdsa_secp256r1_sha256_p1363_test.json - 251 */
	"ecdsa_secp256r1_sha256_p1363_test.json - 251",
	"04bcbb2914c79f045eaa6ecbbc612816b3be5d2d6796707d8125e9f851c18af015fffffffeecad44b6f05d15b33146549c2297b522a5eed8430cff596758e6c43d",
	"4d657373616765",
	"341c1b9ff3c83dd5e0dfa0bf68bcdf4bb7aa20c625975e5eeee34bb396266b3472b69f061b750fd5121b22b11366fad549c634e77765a017902a67099e0a4469",
	"G",

	/* ecdsa_secp256r1_sha256_p1363_test.json - 252 */
	"ecdsa_secp256r1_sha256_p1363_test.json - 252",
	"04bcbb2914c79f045eaa6ecbbc612816b3be5d2d6796707d8125e9f851c18af015fffffffeecad44b6f05d15b33146549c2297b522a5eed8430cff596758e6c43d",
	"4d657373616765",
	"70bebe684cdcb5ca72a42f0d873879359bd1781a591809947628d313a3814f67aec03aca8f5587a4d535fa31027bbe9cc0e464b1c3577f4c2dcde6b2094798a9",
	"G",

	/* ecdsa_secp256r1_sha256_test.json - 1 */
	"ecdsa_secp256r1_sha256_test.json - 1",
	"0404aaec73635726f213fb8a9e64da3b8632e41495a944d0045b522eba7240fad587d9315798aaa3a5ba01775787ced05eaaf7b4e09fc81d6d1aa546e8365d525d",
	"",
	"b292a619339f6e567a305c951c0dcbcc42d16e47f219f9e98e76e09d8770b34a0177e60492c5a8242f76f07bfe3661bde59ec2a17ce5bd2dab2abebdf89a62e2",
	"G",

	/* ecdsa_secp256r1_sha256_test.json - 2 */
	"ecdsa_secp256r1_sha256_test.json - 2",
	"0404aaec73635726f213fb8a9e64da3b8632e41495a944d0045b522eba7240fad587d9315798aaa3a5ba01775787ced05eaaf7b4e09fc81d6d1aa546e8365d525d",
	"4d7367",
	"530bd6b0c9af2d69ba897f6b5fb59695cfbf33afe66dbadcf5b8d2a2a6538e23d85e489cb7a161fd55ededcedbf4cc0c0987e3e3f0f242cae934c72caa3f43e9",
	"G",

	/* ecdsa_secp256r1_sha256_test.json - 3 */
	"ecdsa_secp256r1_sha256_test.json - 3",
	"0404aaec73635726f213fb8a9e64da3b8632e41495a944d0045b522eba7240fad587d9315798aaa3a5ba01775787ced05eaaf7b4e09fc81d6d1aa546e8365d525d",
	"313233343030",
	"a8ea150cb80125d7381c4c1f1da8e9de2711f9917060406a73d7904519e51388f3ab9fa68bd47973a73b2d40480c2ba50c22c9d76ec217257288293285449b86",
	"G",

	/* ecdsa_secp256r1_sha256_test.json - 4 */
	"ecdsa_secp256r1_sha256_test.json - 4",
	"0404aaec73635726f213fb8a9e64da3b8632e41495a944d0045b522eba7240fad587d9315798aaa3a5ba01775787ced05eaaf7b4e09fc81d6d1aa546e8365d525d",
	"0000000000000000000000000000000000000000",
	"986e65933ef2ed4ee5aada139f52b70539aaf63f00a91f29c69178490d57fb713dafedfb8da6189d372308cbf1489bbbdabf0c0217d1c0ff0f701aaa7a694b9c",
	"G",

	/* ecdsa_secp256r1_sha256_test.json - 5 */
	"ecdsa_secp256r1_sha256_test.json - 5",
	"042927b10512bae3eddcfe467828128bad2903269919f7086069c8c4df6c732838c7787964eaac00e5921fb1498a60f4606766b3d9685001558d1a974e7341513e",
	"313233343030",
	"2ba3a8be6b94d5ec80a6d9d1190a436effe50d85a1eee859b8cc6af9bd5c2e184cd60b855d442f5b3c7b11eb6c4e0ae7525fe710fab9aa7c77a67f79e6fadd76",
	"G",

	/* ecdsa_secp256r1_sha256_test.json - 7 */
	"ecdsa_secp256r1_sha256_test.json - 7",
	"042927b10512bae3eddcfe467828128bad2903269919f7086069c8c4df6c732838c7787964eaac00e5921fb1498a60f4606766b3d9685001558d1a974e7341513e",
	"313233343030",
	"2ba3a8be6b94d5ec80a6d9d1190a436effe50d85a1eee859b8cc6af9bd5c2e18b329f479a2bbd0a5c384ee1493b1f5186a87139cac5df4087c134b49156847db",
	"G",

	/* ecdsa_secp256r1_sha256_test.json - 156 */
	"ecdsa_secp256r1_sha256_test.json - 156",
	"042927b10512bae3eddcfe467828128bad2903269919f7086069c8c4df6c732838c7787964eaac00e5921fb1498a60f4606766b3d9685001558d1a974e7341513e",
	"313233343030",
	"d45c5740946b2a147f59262ee6f5bc90bd01ed280528b62b3aed5fc93f06f739b329f479a2bbd0a5c384ee1493b1f5186a87139cac5df4087c134b49156847db",
	"F",

	/* ecdsa_secp256r1_sha256_test.json - 168 */
	"ecdsa_secp256r1_sha256_test.json - 168",
	"042927b10512bae3eddcfe467828128bad2903269919f7086069c8c4df6c732838c7787964eaac00e5921fb1498a60f4606766b3d9685001558d1a974e7341513e",
	"313233343030",
	"00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000",
	"F",

	/* ecdsa_secp256r1_sha256_test.json - 169 */
	"ecdsa_secp256r1_sha256_test.json - 169",
	"042927b10512bae3eddcfe467828128bad2903269919f7086069c8c4df6c732838c7787964eaac00e5921fb1498a60f4606766b3d9685001558d1a974e7341513e",
	"313233343030",
	"00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000001",
	"F",

	/* ecdsa_secp256r1_sha256_test.json - 171 */
	"ecdsa_secp256r1_sha256_test.json - 171",
	"042927b10512bae3eddcfe467828128bad2903269919f7086069c8c4df6c732838c7787964eaac00e5921fb1498a60f4606766b3d9685001558d1a974e7341513e",
	"313233343030",
	"0000000000000000000000000000000000000000000000000000000000000000ffffffff00000000ffffffffffffffffbce6faada7179e84f3b9cac2fc632551",
	"F",

	/* ecdsa_secp256r1_sha256_test.json - 172 */
	"ecdsa_secp256r1_sha256_test.json - 172",
	"042927b10512bae3eddcfe467828128bad2903269919f7086069c8c4df6c732838c7787964eaac00e5921fb1498a60f4606766b3d9685001558d1a974e7341513e",
	"313233343030",
	"0000000000000000000000000000000000000000000000000000000000000000ffffffff00000000ffffffffffffffffbce6faada7179e84f3b9cac2fc632550",
	"F",

	/* ecdsa_secp256r1_sha256_test.json - 173 */
	"ecdsa_secp256r1_sha256_test.json - 173",
	"042927b10512bae3eddcfe467828128bad2903269919f7086069c8c4df6c732838c7787964eaac00e5921fb1498a60f4606766b3d9685001558d1a974e7341513e",
	"313233343030",
	"0000000000000000000000000000000000000000000000000000000000000000ffffffff00000000ffffffffffffffffbce6faada7179e84f3b9cac2fc632552",
	"F",

	/* ecdsa_secp256r1_sha256_test.json - 174 */
	"ecdsa_secp256r1_sha256_test.json - 174",
	"042927b10512bae3eddcfe467828128bad2903269919f7086069c8c4df6c732838c7787964eaac00e5921fb1498a60f4606766b3d9685001558d1a974e7341513e",
	"313233343030",
	"0000000000000000000000000000000000000000000000000000000000000000ffffffff00000001000000000000000000000000ffffffffffffffffffffffff",
	"F",

	/* ecdsa_secp256r1_sha256_test.json - 175 */
	"ecdsa_secp256r1_sha256_test.json - 175",
	"042927b10512bae3eddcfe467828128bad2903269919f7086069c8c4df6c732838c7787964eaac00e5921fb1498a60f4606766b3d9685001558d1a974e7341513e",
	"313233343030",
	"0000000000000000000000000000000000000000000000000000000000000000ffffffff00000001000000000000000000000001000000000000000000000000",
	"F",

	/* ecdsa_secp256r1_sha256_test.json - 176 */
	"ecdsa_secp256r1_sha256_test.json - 176",
	"042927b10512bae3eddcfe467828128bad2903269919f7086069c8c4df6c732838c7787964eaac00e5921fb1498a60f4606766b3d9685001558d1a974e7341513e",
	"313233343030",
	"00000000000000000000000000000000000000000000000000000000000000010000000000000000000000000000000000000000000000000000000000000000",
	"F",

	/* ecdsa_secp256r1_sha256_test.json - 177 */
	"ecdsa_secp256r1_sha256_test.json - 177",
	"042927b10512bae3eddcfe467828128bad2903269919f7086069c8c4df6c732838c7787964eaac00e5921fb1498a60f4606766b3d9685001558d1a974e7341513e",
	"313233343030",
	"00000000000000000000000000000000000000000000000000000000000000010000000000000000000000000000000000000000000000000000000000000001",
	"F",

	/* ecdsa_secp256r1_sha256_test.json - 179 */
	"ecdsa_secp256r1_sha256_test.json - 179",
	"042927b10512bae3eddcfe467828128bad2903269919f7086069c8c4df6c732838c7787964eaac00e5921fb1498a60f4606766b3d9685001558d1a974e7341513e",
	"313233343030",
	"0000000000000000000000000000000000000000000000000000000000000001ffffffff00000000ffffffffffffffffbce6faada7179e84f3b9cac2fc632551",
	"F",

	/* ecdsa_secp256r1_sha256_test.json - 180 */
	"ecdsa_secp256r1_sha256_test.json - 180",
	"042927b10512bae3eddcfe467828128bad2903269919f7086069c8c4df6c732838c7787964eaac00e5921fb1498a60f4606766b3d9685001558d1a974e7341513e",
	"313233343030",
	"0000000000000000000000000000000000000000000000000000000000000001ffffffff00000000ffffffffffffffffbce6faada7179e84f3b9cac2fc632550",
	"F",

	/* ecdsa_secp256r1_sha256_test.json - 181 */
	"ecdsa_secp256r1_sha256_test.json - 181",
	"042927b10512bae3eddcfe467828128bad2903269919f7086069c8c4df6c732838c7787964eaac00e5921fb1498a60f4606766b3d9685001558d1a974e7341513e",
	"313233343030",
	"0000000000000000000000000000000000000000000000000000000000000001ffffffff00000000ffffffffffffffffbce6faada7179e84f3b9cac2fc632552",
	"F",

	/* ecdsa_secp256r1_sha256_test.json - 182 */
	"ecdsa_secp256r1_sha256_test.json - 182",
	"042927b10512bae3eddcfe467828128bad2903269919f7086069c8c4df6c732838c7787964eaac00e5921fb1498a60f4606766b3d9685001558d1a974e7341513e",
	"313233343030",
	"0000000000000000000000000000000000000000000000000000000000000001ffffffff00000001000000000000000000000000ffffffffffffffffffffffff",
	"F",

	/* ecdsa_secp256r1_sha256_test.json - 183 */
	"ecdsa_secp256r1_sha256_test.json - 183",
	"042927b10512bae3eddcfe467828128bad2903269919f7086069c8c4df6c732838c7787964eaac00e5921fb1498a60f4606766b3d9685001558d1a974e7341513e",
	"313233343030",
	"0000000000000000000000000000000000000000000000000000000000000001ffffffff00000001000000000000000000000001000000000000000000000000",
	"F",

	/* ecdsa_secp256r1_sha256_test.json - 192 */
	"ecdsa_secp256r1_sha256_test.json - 192",
	"042927b10512bae3eddcfe467828128bad2903269919f7086069c8c4df6c732838c7787964eaac00e5921fb1498a60f4606766b3d9685001558d1a974e7341513e",
	"313233343030",
	"ffffffff00000000ffffffffffffffffbce6faada7179e84f3b9cac2fc6325510000000000000000000000000000000000000000000000000000000000000000",
	"F",

	/* ecdsa_secp256r1_sha256_test.json - 193 */
	"ecdsa_secp256r1_sha256_test.json - 193",
	"042927b10512bae3eddcfe467828128bad2903269919f7086069c8c4df6c732838c7787964eaac00e5921fb1498a60f4606766b3d9685001558d1a974e7341513e",
	"313233343030",
	"ffffffff00000000ffffffffffffffffbce6faada7179e84f3b9cac2fc6325510000000000000000000000000000000000000000000000000000000000000001",
	"F",

	/* ecdsa_secp256r1_sha256_test.json - 195 */
	"ecdsa_secp256r1_sha256_test.json - 195",
	"042927b10512bae3eddcfe467828128bad2903269919f7086069c8c4df6c732838c7787964eaac00e5921fb1498a60f4606766b3d9685001558d1a974e7341513e",
	"313233343030",
	"ffffffff00000000ffffffffffffffffbce6faada7179e84f3b9cac2fc632551ffffffff00000000ffffffffffffffffbce6faada7179e84f3b9cac2fc632551",
	"F",

	/* ecdsa_secp256r1_sha256_test.json - 196 */
	"ecdsa_secp256r1_sha256_test.json - 196",
	"042927b10512bae3eddcfe467828128bad2903269919f7086069c8c4df6c732838c7787964eaac00e5921fb1498a60f4606766b3d9685001558d1a974e7341513e",
	"313233343030",
	"ffffffff00000000ffffffffffffffffbce6faada7179e84f3b9cac2fc632551ffffffff00000000ffffffffffffffffbce6faada7179e84f3b9cac2fc632550",
	"F",

	/* ecdsa_secp256r1_sha256_test.json - 197 */
	"ecdsa_secp256r1_sha256_test.json - 197",
	"042927b10512bae3eddcfe467828128bad2903269919f7086069c8c4df6c732838c7787964eaac00e5921fb1498a60f4606766b3d9685001558d1a974e7341513e",
	"313233343030",
	"ffffffff00000000ffffffffffffffffbce6faada7179e84f3b9cac2fc632551ffffffff00000000ffffffffffffffffbce6faada7179e84f3b9cac2fc632552",
	"F",

	/* ecdsa_secp256r1_sha256_test.json - 198 */
	"ecdsa_secp256r1_sha256_test.json - 198",
	"042927b10512bae3eddcfe467828128bad2903269919f7086069c8c4df6c732838c7787964eaac00e5921fb1498a60f4606766b3d9685001558d1a974e7341513e",
	"313233343030",
	"ffffffff00000000ffffffffffffffffbce6faada7179e84f3b9cac2fc632551ffffffff00000001000000000000000000000000ffffffffffffffffffffffff",
	"F",

	/* ecdsa_secp256r1_sha256_test.json - 199 */
	"ecdsa_secp256r1_sha256_test.json - 199",
	"042927b10512bae3eddcfe467828128bad2903269919f7086069c8c4df6c732838c7787964eaac00e5921fb1498a60f4606766b3d9685001558d1a974e7341513e",
	"313233343030",
	"ffffffff00000000ffffffffffffffffbce6faada7179e84f3b9cac2fc632551ffffffff00000001000000000000000000000001000000000000000000000000",
	"F",

	/* ecdsa_secp256r1_sha256_test.json - 200 */
	"ecdsa_secp256r1_sha256_test.json - 200",
	"042927b10512bae3eddcfe467828128bad2903269919f7086069c8c4df6c732838c7787964eaac00e5921fb1498a60f4606766b3d9685001558d1a974e7341513e",
	"313233343030",
	"ffffffff00000000ffffffffffffffffbce6faada7179e84f3b9cac2fc6325500000000000000000000000000000000000000000000000000000000000000000",
	"F",

	/* ecdsa_secp256r1_sha256_test.json - 201 */
	"ecdsa_secp256r1_sha256_test.json - 201",
	"042927b10512bae3eddcfe467828128bad2903269919f7086069c8c4df6c732838c7787964eaac00e5921fb1498a60f4606766b3d9685001558d1a974e7341513e",
	"313233343030",
	"ffffffff00000000ffffffffffffffffbce6faada7179e84f3b9cac2fc6325500000000000000000000000000000000000000000000000000000000000000001",
	"F",

	/* ecdsa_secp256r1_sha256_test.json - 203 */
	"ecdsa_secp256r1_sha256_test.json - 203",
	"042927b10512bae3eddcfe467828128bad2903269919f7086069c8c4df6c732838c7787964eaac00e5921fb1498a60f4606766b3d9685001558d1a974e7341513e",
	"313233343030",
	"ffffffff00000000ffffffffffffffffbce6faada7179e84f3b9cac2fc632550ffffffff00000000ffffffffffffffffbce6faada7179e84f3b9cac2fc632551",
	"F",

	/* ecdsa_secp256r1_sha256_test.json - 204 */
	"ecdsa_secp256r1_sha256_test.json - 204",
	"042927b10512bae3eddcfe467828128bad2903269919f7086069c8c4df6c732838c7787964eaac00e5921fb1498a60f4606766b3d9685001558d1a974e7341513e",
	"313233343030",
	"ffffffff00000000ffffffffffffffffbce6faada7179e84f3b9cac2fc632550ffffffff00000000ffffffffffffffffbce6faada7179e84f3b9cac2fc632550",
	"F",

	/* ecdsa_secp256r1_sha256_test.json - 205 */
	"ecdsa_secp256r1_sha256_test.json - 205",
	"042927b10512bae3eddcfe467828128bad2903269919f7086069c8c4df6c732838c7787964eaac00e5921fb1498a60f4606766b3d9685001558d1a974e7341513e",
	"313233343030",
	"ffffffff00000000ffffffffffffffffbce6faada7179e84f3b9cac2fc632550ffffffff00000000ffffffffffffffffbce6faada7179e84f3b9cac2fc632552",
	"F",

	/* ecdsa_secp256r1_sha256_test.json - 206 */
	"ecdsa_secp256r1_sha256_test.json - 206",
	"042927b10512bae3eddcfe467828128bad2903269919f7086069c8c4df6c732838c7787964eaac00e5921fb1498a60f4606766b3d9685001558d1a974e7341513e",
	"313233343030",
	"ffffffff00000000ffffffffffffffffbce6faada7179e84f3b9cac2fc632550ffffffff00000001000000000000000000000000ffffffffffffffffffffffff",
	"F",

	/* ecdsa_secp256r1_sha256_test.json - 207 */
	"ecdsa_secp256r1_sha256_test.json - 207",
	"042927b10512bae3eddcfe467828128bad2903269919f7086069c8c4df6c732838c7787964eaac00e5921fb1498a60f4606766b3d9685001558d1a974e7341513e",
	"313233343030",
	"ffffffff00000000ffffffffffffffffbce6faada7179e84f3b9cac2fc632550ffffffff00000001000000000000000000000001000000000000000000000000",
	"F",

	/* ecdsa_secp256r1_sha256_test.json - 208 */
	"ecdsa_secp256r1_sha256_test.json - 208",
	"042927b10512bae3eddcfe467828128bad2903269919f7086069c8c4df6c732838c7787964eaac00e5921fb1498a60f4606766b3d9685001558d1a974e7341513e",
	"313233343030",
	"ffffffff00000000ffffffffffffffffbce6faada7179e84f3b9cac2fc6325520000000000000000000000000000000000000000000000000000000000000000",
	"F",

	/* ecdsa_secp256r1_sha256_test.json - 209 */
	"ecdsa_secp256r1_sha256_test.json - 209",
	"042927b10512bae3eddcfe467828128bad2903269919f7086069c8c4df6c732838c7787964eaac00e5921fb1498a60f4606766b3d9685001558d1a974e7341513e",
	"313233343030",
	"ffffffff00000000ffffffffffffffffbce6faada7179e84f3b9cac2fc6325520000000000000000000000000000000000000000000000000000000000000001",
	"F",

	/* ecdsa_secp256r1_sha256_test.json - 211 */
	"ecdsa_secp256r1_sha256_test.json - 211",
	"042927b10512bae3eddcfe467828128bad2903269919f7086069c8c4df6c732838c7787964eaac00e5921fb1498a60f4606766b3d9685001558d1a974e7341513e",
	"313233343030",
	"ffffffff00000000ffffffffffffffffbce6faada7179e84f3b9cac2fc632552ffffffff00000000ffffffffffffffffbce6faada7179e84f3b9cac2fc632551",
	"F",

	/* ecdsa_secp256r1_sha256_test.json - 212 */
	"ecdsa_secp256r1_sha256_test.json - 212",
	"042927b10512bae3eddcfe467828128bad2903269919f7086069c8c4df6c732838c7787964eaac00e5921fb1498a60f4606766b3d9685001558d1a974e7341513e",
	"313233343030",
	"ffffffff00000000ffffffffffffffffbce6faada7179e84f3b9cac2fc632552ffffffff00000000ffffffffffffffffbce6faada7179e84f3b9cac2fc632550",
	"F",

	/* ecdsa_secp256r1_sha256_test.json - 213 */
	"ecdsa_secp256r1_sha256_test.json - 213",
	"042927b10512bae3eddcfe467828128bad2903269919f7086069c8c4df6c732838c7787964eaac00e5921fb1498a60f4606766b3d9685001558d1a974e7341513e",
	"313233343030",
	"ffffffff00000000ffffffffffffffffbce6faada7179e84f3b9cac2fc632552ffffffff00000000ffffffffffffffffbce6faada7179e84f3b9cac2fc632552",
	"F",

	/* ecdsa_secp256r1_sha256_test.json - 214 */
	"ecdsa_secp256r1_sha256_test.json - 214",
	"042927b10512bae3eddcfe467828128bad2903269919f7086069c8c4df6c732838c7787964eaac00e5921fb1498a60f4606766b3d9685001558d1a974e7341513e",
	"313233343030",
	"ffffffff00000000ffffffffffffffffbce6faada7179e84f3b9cac2fc632552ffffffff00000001000000000000000000000000ffffffffffffffffffffffff",
	"F",

	/* ecdsa_secp256r1_sha256_test.json - 215 */
	"ecdsa_secp256r1_sha256_test.json - 215",
	"042927b10512bae3eddcfe467828128bad2903269919f7086069c8c4df6c732838c7787964eaac00e5921fb1498a60f4606766b3d9685001558d1a974e7341513e",
	"313233343030",
	"ffffffff00000000ffffffffffffffffbce6faada7179e84f3b9cac2fc632552ffffffff00000001000000000000000000000001000000000000000000000000",
	"F",

	/* ecdsa_secp256r1_sha256_test.json - 216 */
	"ecdsa_secp256r1_sha256_test.json - 216",
	"042927b10512bae3eddcfe467828128bad2903269919f7086069c8c4df6c732838c7787964eaac00e5921fb1498a60f4606766b3d9685001558d1a974e7341513e",
	"313233343030",
	"ffffffff00000001000000000000000000000000ffffffffffffffffffffffff0000000000000000000000000000000000000000000000000000000000000000",
	"F",

	/* ecdsa_secp256r1_sha256_test.json - 217 */
	"ecdsa_secp256r1_sha256_test.json - 217",
	"042927b10512bae3eddcfe467828128bad2903269919f7086069c8c4df6c732838c7787964eaac00e5921fb1498a60f4606766b3d9685001558d1a974e7341513e",
	"313233343030",
	"ffffffff00000001000000000000000000000000ffffffffffffffffffffffff0000000000000000000000000000000000000000000000000000000000000001",
	"F",

	/* ecdsa_secp256r1_sha256_test.json - 219 */
	"ecdsa_secp256r1_sha256_test.json - 219",
	"042927b10512bae3eddcfe467828128bad2903269919f7086069c8c4df6c732838c7787964eaac00e5921fb1498a60f4606766b3d9685001558d1a974e7341513e",
	"313233343030",
	"ffffffff00000001000000000000000000000000ffffffffffffffffffffffffffffffff00000000ffffffffffffffffbce6faada7179e84f3b9cac2fc632551",
	"F",

	/* ecdsa_secp256r1_sha256_test.json - 220 */
	"ecdsa_secp256r1_sha256_test.json - 220",
	"042927b10512bae3eddcfe467828128bad2903269919f7086069c8c4df6c732838c7787964eaac00e5921fb1498a60f4606766b3d9685001558d1a974e7341513e",
	"313233343030",
	"ffffffff00000001000000000000000000000000ffffffffffffffffffffffffffffffff00000000ffffffffffffffffbce6faada7179e84f3b9cac2fc632550",
	"F",

	/* ecdsa_secp256r1_sha256_test.json - 221 */
	"ecdsa_secp256r1_sha256_test.json - 221",
	"042927b10512bae3eddcfe467828128bad2903269919f7086069c8c4df6c732838c7787964eaac00e5921fb1498a60f4606766b3d9685001558d1a974e7341513e",
	"313233343030",
	"ffffffff00000001000000000000000000000000ffffffffffffffffffffffffffffffff00000000ffffffffffffffffbce6faada7179e84f3b9cac2fc632552",
	"F",

	/* ecdsa_secp256r1_sha256_test.json - 222 */
	"ecdsa_secp256r1_sha256_test.json - 222",
	"042927b10512bae3eddcfe467828128bad2903269919f7086069c8c4df6c732838c7787964eaac00e5921fb1498a60f4606766b3d9685001558d1a974e7341513e",
	"313233343030",
	"ffffffff00000001000000000000000000000000ffffffffffffffffffffffffffffffff00000001000000000000000000000000ffffffffffffffffffffffff",
	"F",

	/* ecdsa_secp256r1_sha256_test.json - 223 */
	"ecdsa_secp256r1_sha256_test.json - 223",
	"042927b10512bae3eddcfe467828128bad2903269919f7086069c8c4df6c732838c7787964eaac00e5921fb1498a60f4606766b3d9685001558d1a974e7341513e",
	"313233343030",
	"ffffffff00000001000000000000000000000000ffffffffffffffffffffffffffffffff00000001000000000000000000000001000000000000000000000000",
	"F",

	/* ecdsa_secp256r1_sha256_test.json - 224 */
	"ecdsa_secp256r1_sha256_test.json - 224",
	"042927b10512bae3eddcfe467828128bad2903269919f7086069c8c4df6c732838c7787964eaac00e5921fb1498a60f4606766b3d9685001558d1a974e7341513e",
	"313233343030",
	"ffffffff000000010000000000000000000000010000000000000000000000000000000000000000000000000000000000000000000000000000000000000000",
	"F",

	/* ecdsa_secp256r1_sha256_test.json - 225 */
	"ecdsa_secp256r1_sha256_test.json - 225",
	"042927b10512bae3eddcfe467828128bad2903269919f7086069c8c4df6c732838c7787964eaac00e5921fb1498a60f4606766b3d9685001558d1a974e7341513e",
	"313233343030",
	"ffffffff000000010000000000000000000000010000000000000000000000000000000000000000000000000000000000000000000000000000000000000001",
	"F",

	/* ecdsa_secp256r1_sha256_test.json - 227 */
	"ecdsa_secp256r1_sha256_test.json - 227",
	"042927b10512bae3eddcfe467828128bad2903269919f7086069c8c4df6c732838c7787964eaac00e5921fb1498a60f4606766b3d9685001558d1a974e7341513e",
	"313233343030",
	"ffffffff00000001000000000000000000000001000000000000000000000000ffffffff00000000ffffffffffffffffbce6faada7179e84f3b9cac2fc632551",
	"F",

	/* ecdsa_secp256r1_sha256_test.json - 228 */
	"ecdsa_secp256r1_sha256_test.json - 228",
	"042927b10512bae3eddcfe467828128bad2903269919f7086069c8c4df6c732838c7787964eaac00e5921fb1498a60f4606766b3d9685001558d1a974e7341513e",
	"313233343030",
	"ffffffff00000001000000000000000000000001000000000000000000000000ffffffff00000000ffffffffffffffffbce6faada7179e84f3b9cac2fc632550",
	"F",

	/* ecdsa_secp256r1_sha256_test.json - 229 */
	"ecdsa_secp256r1_sha256_test.json - 229",
	"042927b10512bae3eddcfe467828128bad2903269919f7086069c8c4df6c732838c7787964eaac00e5921fb1498a60f4606766b3d9685001558d1a974e7341513e",
	"313233343030",
	"ffffffff00000001000000000000000000000001000000000000000000000000ffffffff00000000ffffffffffffffffbce6faada7179e84f3b9cac2fc632552",
	"F",

	/* ecdsa_secp256r1_sha256_test.json - 230 */
	"ecdsa_secp256r1_sha256_test.json - 230",
	"042927b10512bae3eddcfe467828128bad2903269919f7086069c8c4df6c732838c7787964eaac00e5921fb1498a60f4606766b3d9685001558d1a974e7341513e",
	"313233343030",
	"ffffffff00000001000000000000000000000001000000000000000000000000ffffffff00000001000000000000000000000000ffffffffffffffffffffffff",
	"F",

	/* ecdsa_secp256r1_sha256_test.json - 231 */
	"ecdsa_secp256r1_sha256_test.json - 231",
	"042927b10512bae3eddcfe467828128bad2903269919f7086069c8c4df6c732838c7787964eaac00e5921fb1498a60f4606766b3d9685001558d1a974e7341513e",
	"313233343030",
	"ffffffff00000001000000000000000000000001000000000000000000000000ffffffff00000001000000000000000000000001000000000000000000000000",
	"F",

	/* ecdsa_secp256r1_sha256_test.json - 295 */
	"ecdsa_secp256r1_sha256_test.json - 295",
	"042927b10512bae3eddcfe467828128bad2903269919f7086069c8c4df6c732838c7787964eaac00e5921fb1498a60f4606766b3d9685001558d1a974e7341513e",
	"3639383139",
	"64a1aab5000d0e804f3e2fc02bdee9be8ff312334e2ba16d11547c97711c898e6af015971cc30be6d1a206d4e013e0997772a2f91d73286ffd683b9bb2cf4f1b",
	"G",

	/* ecdsa_secp256r1_sha256_test.json - 296 */
	"ecdsa_secp256r1_sha256_test.json - 296",
	"042927b10512bae3eddcfe467828128bad2903269919f7086069c8c4df6c732838c7787964eaac00e5921fb1498a60f4606766b3d9685001558d1a974e7341513e",
	"343236343739373234",
	"16aea964a2f6506d6f78c81c91fc7e8bded7d397738448de1e19a0ec580bf266252cd762130c6667cfe8b7bc47d27d78391e8e80c578d1cd38c3ff033be928e9",
	"G",

	/* ecdsa_secp256r1_sha256_test.json - 297 */
	"ecdsa_secp256r1_sha256_test.json - 297",
	"042927b10512bae3eddcfe467828128bad2903269919f7086069c8c4df6c732838c7787964eaac00e5921fb1498a60f4606766b3d9685001558d1a974e7341513e",
	"37313338363834383931",
	"9cc98be2347d469bf476dfc26b9b733df2d26d6ef524af917c665baccb23c882093496459effe2d8d70727b82462f61d0ec1b7847929d10ea631dacb16b56c32",
	"G",

	/* ecdsa_secp256r1_sha256_test.json - 298 */
	"ecdsa_secp256r1_sha256_test.json - 298",
	"042927b10512bae3eddcfe467828128bad2903269919f7086069c8c4df6c732838c7787964eaac00e5921fb1498a60f4606766b3d9685001558d1a974e7341513e",
	"3130333539333331363638",
	"73b3c90ecd390028058164524dde892703dce3dea0d53fa8093999f07ab8aa432f67b0b8e20636695bb7d8bf0a651c802ed25a395387b5f4188c0c4075c88634",
	"G",

	/* ecdsa_secp256r1_sha256_test.json - 299 */
	"ecdsa_secp256r1_sha256_test.json - 299",
	"042927b10512bae3eddcfe467828128bad2903269919f7086069c8c4df6c732838c7787964eaac00e5921fb1498a60f4606766b3d9685001558d1a974e7341513e",
	"33393439343031323135",
	"bfab3098252847b328fadf2f89b95c851a7f0eb390763378f37e90119d5ba3ddbdd64e234e832b1067c2d058ccb44d978195ccebb65c2aaf1e2da9b8b4987e3b",
	"G",

	/* ecdsa_secp256r1_sha256_test.json - 300 */
	"ecdsa_secp256r1_sha256_test.json - 300",
	"042927b10512bae3eddcfe467828128bad2903269919f7086069c8c4df6c732838c7787964eaac00e5921fb1498a60f4606766b3d9685001558d1a974e7341513e",
	"31333434323933303739",
	"204a9784074b246d8bf8bf04a4ceb1c1f1c9aaab168b1596d17093c5cd21d2cd51cce41670636783dc06a759c8847868a406c2506fe17975582fe648d1d88b52",
	"G",

	/* ecdsa_secp256r1_sha256_test.json - 301 */
	"ecdsa_secp256r1_sha256_test.json - 301",
	"042927b10512bae3eddcfe467828128bad2903269919f7086069c8c4df6c732838c7787964eaac00e5921fb1498a60f4606766b3d9685001558d1a974e7341513e",
	"33373036323131373132",
	"ed66dc34f551ac82f63d4aa4f81fe2cb0031a91d1314f835027bca0f1ceeaa0399ca123aa09b13cd194a422e18d5fda167623c3f6e5d4d6abb8953d67c0c48c7",
	"G",

	/* ecdsa_secp256r1_sha256_test.json - 302 */
	"ecdsa_secp256r1_sha256_test.json - 302",
	"042927b10512bae3eddcfe467828128bad2903269919f7086069c8c4df6c732838c7787964eaac00e5921fb1498a60f4606766b3d9685001558d1a974e7341513e",
	"333433363838373132",
	"060b700bef665c68899d44f2356a578d126b062023ccc3c056bf0f60a237012b8d186c027832965f4fcc78a3366ca95dedbb410cbef3f26d6be5d581c11d3610",
	"G",

	/* ecdsa_secp256r1_sha256_test.json - 303 */
	"ecdsa_secp256r1_sha256_test.json - 303",
	"042927b10512bae3eddcfe467828128bad2903269919f7086069c8c4df6c732838c7787964eaac00e5921fb1498a60f4606766b3d9685001558d1a974e7341513e",
	"31333531353330333730",
	"9f6adfe8d5eb5b2c24d7aa7934b6cf29c93ea76cd313c9132bb0c8e38c96831db26a9c9e40e55ee0890c944cf271756c906a33e66b5bd15e051593883b5e9902",
	"G",

	/* ecdsa_secp256r1_sha256_test.json - 304 */
	"ecdsa_secp256r1_sha256_test.json - 304",
	"042927b10512bae3eddcfe467828128bad2903269919f7086069c8c4df6c732838c7787964eaac00e5921fb1498a60f4606766b3d9685001558d1a974e7341513e",
	"36353533323033313236",
	"a1af03ca91677b673ad2f33615e56174a1abf6da168cebfa8868f4ba273f16b720aa73ffe48afa6435cd258b173d0c2377d69022e7d098d75caf24c8c5e06b1c",
	"G",

	/* ecdsa_secp256r1_sha256_test.json - 305 */
	"ecdsa_secp256r1_sha256_test.json - 305",
	"042927b10512bae3eddcfe467828128bad2903269919f7086069c8c4df6c732838c7787964eaac00e5921fb1498a60f4606766b3d9685001558d1a974e7341513e",
	"31353634333436363033",
	"fdc70602766f8eed11a6c99a71c973d5659355507b843da6e327a28c11893db93df5349688a085b137b1eacf456a9e9e0f6d15ec0078ca60a7f83f2b10d21350",
	"G",

	/* ecdsa_secp256r1_sha256_test.json - 306 */
	"ecdsa_secp256r1_sha256_test.json - 306",
	"042927b10512bae3eddcfe467828128bad2903269919f7086069c8c4df6c732838c7787964eaac00e5921fb1498a60f4606766b3d9685001558d1a974e7341513e",
	"34343239353339313137",
	"b516a314f2fce530d6537f6a6c49966c23456f63c643cf8e0dc738f7b876e675d39ffd033c92b6d717dd536fbc5efdf1967c4bd80954479ba66b0120cd16fff2",
	"G",

	/* ecdsa_secp256r1_sha256_test.json - 307 */
	"ecdsa_secp256r1_sha256_test.json - 307",
	"042927b10512bae3eddcfe467828128bad2903269919f7086069c8c4df6c732838c7787964eaac00e5921fb1498a60f4606766b3d9685001558d1a974e7341513e",
	"3130393533323631333531",
	"3b2cbf046eac45842ecb7984d475831582717bebb6492fd0a485c101e29ff0a84c9b7b47a98b0f82de512bc9313aaf51701099cac5f76e68c8595fc1c1d99258",
	"G",

	/* ecdsa_secp256r1_sha256_test.json - 308 */
	"ecdsa_secp256r1_sha256_test.json - 308",
	"042927b10512bae3eddcfe467828128bad2903269919f7086069c8c4df6c732838c7787964eaac00e5921fb1498a60f4606766b3d9685001558d1a974e7341513e",
	"35393837333530303431",
	"30c87d35e636f540841f14af54e2f9edd79d0312cfa1ab656c3fb15bfde48dcf47c15a5a82d24b75c85a692bd6ecafeb71409ede23efd08e0db9abf6340677ed",
	"G",

	/* ecdsa_secp256r1_sha256_test.json - 309 */
	"ecdsa_secp256r1_sha256_test.json - 309",
	"042927b10512bae3eddcfe467828128bad2903269919f7086069c8c4df6c732838c7787964eaac00e5921fb1498a60f4606766b3d9685001558d1a974e7341513e",
	"33343633303036383738",
	"38686ff0fda2cef6bc43b58cfe6647b9e2e8176d168dec3c68ff262113760f52067ec3b651f422669601662167fa8717e976e2db5e6a4cf7c2ddabb3fde9d67d",
	"G",

	/* ecdsa_secp256r1_sha256_test.json - 310 */
	"ecdsa_secp256r1_sha256_test.json - 310",
	"042927b10512bae3eddcfe467828128bad2903269919f7086069c8c4df6c732838c7787964eaac00e5921fb1498a60f4606766b3d9685001558d1a974e7341513e",
	"39383137333230323837",
	"44a3e23bf314f2b344fc25c7f2de8b6af3e17d27f5ee844b225985ab6e2775cf2d48e223205e98041ddc87be532abed584f0411f5729500493c9cc3f4dd15e86",
	"G",

	/* ecdsa_secp256r1_sha256_test.json - 311 */
	"ecdsa_secp256r1_sha256_test.json - 311",
	"042927b10512bae3eddcfe467828128bad2903269919f7086069c8c4df6c732838c7787964eaac00e5921fb1498a60f4606766b3d9685001558d1a974e7341513e",
	"33323232303431303436",
	"2ded5b7ec8e90e7bf11f967a3d95110c41b99db3b5aa8d330eb9d638781688e97d5792c53628155e1bfc46fb1a67e3088de049c328ae1f44ec69238a009808f9",
	"G",

	/* ecdsa_secp256r1_sha256_test.json - 312 */
	"ecdsa_secp256r1_sha256_test.json - 312",
	"042927b10512bae3eddcfe467828128bad2903269919f7086069c8c4df6c732838c7787964eaac00e5921fb1498a60f4606766b3d9685001558d1a974e7341513e",
	"36363636333037313034",
	"bdae7bcb580bf335efd3bc3d31870f923eaccafcd40ec2f605976f15137d8b8ff6dfa12f19e525270b0106eecfe257499f373a4fb318994f24838122ce7ec3c7",
	"G",

	/* ecdsa_secp256r1_sha256_test.json - 313 */
	"ecdsa_secp256r1_sha256_test.json - 313",
	"042927b10512bae3eddcfe467828128bad2903269919f7086069c8c4df6c732838c7787964eaac00e5921fb1498a60f4606766b3d9685001558d1a974e7341513e",
	"31303335393531383938",
	"50f9c4f0cd6940e162720957ffff513799209b78596956d21ece251c2401f1c6d7033a0a787d338e889defaaabb106b95a4355e411a59c32aa5167dfab244726",
	"G",

	/* ecdsa_secp256r1_sha256_test.json - 314 */
	"ecdsa_secp256r1_sha256_test.json - 314",
	"042927b10512bae3eddcfe467828128bad2903269919f7086069c8c4df6c732838c7787964eaac00e5921fb1498a60f4606766b3d9685001558d1a974e7341513e",
	"31383436353937313935",
	"f612820687604fa01906066a378d67540982e29575d019aabe90924ead5c860d3f9367702dd7dd4f75ea98afd20e328a1a99f4857b316525328230ce294b0fef",
	"G",

	/* ecdsa_secp256r1_sha256_test.json - 315 */
	"ecdsa_secp256r1_sha256_test.json - 315",
	"042927b10512bae3eddcfe467828128bad2903269919f7086069c8c4df6c732838c7787964eaac00e5921fb1498a60f4606766b3d9685001558d1a974e7341513e",
	"33313336303436313839",
	"9505e407657d6e8bc93db5da7aa6f5081f61980c1949f56b0f2f507da5782a7ac60d31904e3669738ffbeccab6c3656c08e0ed5cb92b3cfa5e7f71784f9c5021",
	"G",

	/* ecdsa_secp256r1_sha256_test.json - 316 */
	"ecdsa_secp256r1_sha256_test.json - 316",
	"042927b10512bae3eddcfe467828128bad2903269919f7086069c8c4df6c732838c7787964eaac00e5921fb1498a60f4606766b3d9685001558d1a974e7341513e",
	"32363633373834323534",
	"bbd16fbbb656b6d0d83e6a7787cd691b08735aed371732723e1c68a40404517d9d8e35dba96028b7787d91315be675877d2d097be5e8ee34560e3e7fd25c0f00",
	"G",

	/* ecdsa_secp256r1_sha256_test.json - 317 */
	"ecdsa_secp256r1_sha256_test.json - 317",
	"042927b10512bae3eddcfe467828128bad2903269919f7086069c8c4df6c732838c7787964eaac00e5921fb1498a60f4606766b3d9685001558d1a974e7341513e",
	"31363532313030353234",
	"2ec9760122db98fd06ea76848d35a6da442d2ceef7559a30cf57c61e92df327e7ab271da90859479701fccf86e462ee3393fb6814c27b760c4963625c0a19878",
	"G",

	/* ecdsa_secp256r1_sha256_test.json - 318 */
	"ecdsa_secp256r1_sha256_test.json - 318",
	"042927b10512bae3eddcfe467828128bad2903269919f7086069c8c4df6c732838c7787964eaac00e5921fb1498a60f4606766b3d9685001558d1a974e7341513e",
	"35373438303831363936",
	"54e76b7683b6650baa6a7fc49b1c51eed9ba9dd463221f7a4f1005a89fe00c592ea076886c773eb937ec1cc8374b7915cfd11b1c1ae1166152f2f7806a31c8fd",
	"G",

	/* ecdsa_secp256r1_sha256_test.json - 319 */
	"ecdsa_secp256r1_sha256_test.json - 319",
	"042927b10512bae3eddcfe467828128bad2903269919f7086069c8c4df6c732838c7787964eaac00e5921fb1498a60f4606766b3d9685001558d1a974e7341513e",
	"36333433393133343638",
	"5291deaf24659ffbbce6e3c26f6021097a74abdbb69be4fb10419c0c496c946665d6fcf336d27cc7cdb982bb4e4ecef5827f84742f29f10abf83469270a03dc3",
	"G",

	/* ecdsa_secp256r1_sha256_test.json - 320 */
	"ecdsa_secp256r1_sha256_test.json - 320",
	"042927b10512bae3eddcfe467828128bad2903269919f7086069c8c4df6c732838c7787964eaac00e5921fb1498a60f4606766b3d9685001558d1a974e7341513e",
	"31353431313033353938",
	"207a3241812d75d947419dc58efb05e8003b33fc17eb50f9d15166a88479f107cdee749f2e492b213ce80b32d0574f62f1c5d70793cf55e382d5caadf7592767",
	"G",

	/* ecdsa_secp256r1_sha256_test.json - 321 */
	"ecdsa_secp256r1_sha256_test.json - 321",
	"042927b10512bae3eddcfe467828128bad2903269919f7086069c8c4df6c732838c7787964eaac00e5921fb1498a60f4606766b3d9685001558d1a974e7341513e",
	"3130343738353830313238",
	"6554e49f82a855204328ac94913bf01bbe84437a355a0a37c0dee3cf81aa7728aea00de2507ddaf5c94e1e126980d3df16250a2eaebc8be486effe7f22b4f929",
	"G",

	/* ecdsa_secp256r1_sha256_test.json - 322 */
	"ecdsa_secp256r1_sha256_test.json - 322",
	"042927b10512bae3eddcfe467828128bad2903269919f7086069c8c4df6c732838c7787964eaac00e5921fb1498a60f4606766b3d9685001558d1a974e7341513e",
	"3130353336323835353638",
	"a54c5062648339d2bff06f71c88216c26c6e19b4d80a8c602990ac82707efdfce99bbe7fcfafae3e69fd016777517aa01056317f467ad09aff09be73c9731b0d",
	"G",

	/* ecdsa_secp256r1_sha256_test.json - 323 */
	"ecdsa_secp256r1_sha256_test.json - 323",
	"042927b10512bae3eddcfe467828128bad2903269919f7086069c8c4df6c732838c7787964eaac00e5921fb1498a60f4606766b3d9685001558d1a974e7341513e",
	"393533393034313035",
	"975bd7157a8d363b309f1f444012b1a1d23096593133e71b4ca8b059cff37eaf7faa7a28b1c822baa241793f2abc930bd4c69840fe090f2aacc46786bf919622",
	"G",

	/* ecdsa_secp256r1_sha256_test.json - 324 */
	"ecdsa_secp256r1_sha256_test.json - 324",
	"042927b10512bae3eddcfe467828128bad2903269919f7086069c8c4df6c732838c7787964eaac00e5921fb1498a60f4606766b3d9685001558d1a974e7341513e",
	"393738383438303339",
	"5694a6f84b8f875c276afd2ebcfe4d61de9ec90305afb1357b95b3e0da43885e0dffad9ffd0b757d8051dec02ebdf70d8ee2dc5c7870c0823b6ccc7c679cbaa4",
	"G",

	/* ecdsa_secp256r1_sha256_test.json - 325 */
	"ecdsa_secp256r1_sha256_test.json - 325",
	"042927b10512bae3eddcfe467828128bad2903269919f7086069c8c4df6c732838c7787964eaac00e5921fb1498a60f4606766b3d9685001558d1a974e7341513e",
	"33363130363732343432",
	"a0c30e8026fdb2b4b4968a27d16a6d08f7098f1a98d21620d7454ba9790f1ba65e470453a8a399f15baf463f9deceb53acc5ca64459149688bd2760c65424339",
	"G",

	/* ecdsa_secp256r1_sha256_test.json - 326 */
	"ecdsa_secp256r1_sha256_test.json - 326",
	"042927b10512bae3eddcfe467828128bad2903269919f7086069c8c4df6c732838c7787964eaac00e5921fb1498a60f4606766b3d9685001558d1a974e7341513e",
	"31303534323430373035",
	"614ea84acf736527dd73602cd4bb4eea1dfebebd5ad8aca52aa0228cf7b99a88737cc85f5f2d2f60d1b8183f3ed490e4de14368e96a9482c2a4dd193195c902f",
	"G",

	/* ecdsa_secp256r1_sha256_test.json - 327 */
	"ecdsa_secp256r1_sha256_test.json - 327",
	"042927b10512bae3eddcfe467828128bad2903269919f7086069c8c4df6c732838c7787964eaac00e5921fb1498a60f4606766b3d9685001558d1a974e7341513e",
	"35313734343438313937",
	"bead6734ebe44b810d3fb2ea00b1732945377338febfd439a8d74dfbd0f942fa6bb18eae36616a7d3cad35919fd21a8af4bbe7a10f73b3e036a46b103ef56e2a",
	"G",

	/* ecdsa_secp256r1_sha256_test.json - 328 */
	"ecdsa_secp256r1_sha256_test.json - 328",
	"042927b10512bae3eddcfe467828128bad2903269919f7086069c8c4df6c732838c7787964eaac00e5921fb1498a60f4606766b3d9685001558d1a974e7341513e",
	"31393637353631323531",
	"499625479e161dacd4db9d9ce64854c98d922cbf212703e9654fae182df9bad242c177cf37b8193a0131108d97819edd9439936028864ac195b64fca76d9d693",
	"G",

	/* ecdsa_secp256r1_sha256_test.json - 329 */
	"ecdsa_secp256r1_sha256_test.json - 329",
	"042927b10512bae3eddcfe467828128bad2903269919f7086069c8c4df6c732838c7787964eaac00e5921fb1498a60f4606766b3d9685001558d1a974e7341513e",
	"33343437323533333433",
	"08f16b8093a8fb4d66a2c8065b541b3d31e3bfe694f6b89c50fb1aaa6ff6c9b29d6455e2d5d1779748573b611cb95d4a21f967410399b39b535ba3e5af81ca2e",
	"G",

	/* ecdsa_secp256r1_sha256_test.json - 330 */
	"ecdsa_secp256r1_sha256_test.json - 330",
	"042927b10512bae3eddcfe467828128bad2903269919f7086069c8c4df6c732838c7787964eaac00e5921fb1498a60f4606766b3d9685001558d1a974e7341513e",
	"333638323634333138",
	"be26231b6191658a19dd72ddb99ed8f8c579b6938d19bce8eed8dc2b338cb5f8e1d9a32ee56cffed37f0f22b2dcb57d5c943c14f79694a03b9c5e96952575c89",
	"G",

	/* ecdsa_secp256r1_sha256_test.json - 331 */
	"ecdsa_secp256r1_sha256_test.json - 331",
	"042927b10512bae3eddcfe467828128bad2903269919f7086069c8c4df6c732838c7787964eaac00e5921fb1498a60f4606766b3d9685001558d1a974e7341513e",
	"33323631313938363038",
	"15e76880898316b16204ac920a02d58045f36a229d4aa4f812638c455abe0443e74d357d3fcb5c8c5337bd6aba4178b455ca10e226e13f9638196506a1939123",
	"G",

	/* ecdsa_secp256r1_sha256_test.json - 332 */
	"ecdsa_secp256r1_sha256_test.json - 332",
	"042927b10512bae3eddcfe467828128bad2903269919f7086069c8c4df6c732838c7787964eaac00e5921fb1498a60f4606766b3d9685001558d1a974e7341513e",
	"39363738373831303934",
	"352ecb53f8df2c503a45f9846fc28d1d31e6307d3ddbffc1132315cc07f16dad1348dfa9c482c558e1d05c5242ca1c39436726ecd28258b1899792887dd0a3c6",
	"G",

	/* ecdsa_secp256r1_sha256_test.json - 333 */
	"ecdsa_secp256r1_sha256_test.json - 333",
	"042927b10512bae3eddcfe467828128bad2903269919f7086069c8c4df6c732838c7787964eaac00e5921fb1498a60f4606766b3d9685001558d1a974e7341513e",
	"34393538383233383233",
	"4a40801a7e606ba78a0da9882ab23c7677b8642349ed3d652c5bfa5f2a9558fb3a49b64848d682ef7f605f2832f7384bdc24ed2925825bf8ea77dc5981725782",
	"G",

	/* ecdsa_secp256r1_sha256_test.json - 334 */
	"ecdsa_secp256r1_sha256_test.json - 334",
	"042927b10512bae3eddcfe467828128bad2903269919f7086069c8c4df6c732838c7787964eaac00e5921fb1498a60f4606766b3d9685001558d1a974e7341513e",
	"383234363337383337",
	"eacc5e1a8304a74d2be412b078924b3bb3511bac855c05c9e5e9e44df3d61e967451cd8e18d6ed1885dd827714847f96ec4bb0ed4c36ce9808db8f714204f6d1",
	"G",

	/* ecdsa_secp256r1_sha256_test.json - 335 */
	"ecdsa_secp256r1_sha256_test.json - 335",
	"042927b10512bae3eddcfe467828128bad2903269919f7086069c8c4df6c732838c7787964eaac00e5921fb1498a60f4606766b3d9685001558d1a974e7341513e",
	"3131303230383333373736",
	"2f7a5e9e5771d424f30f67fdab61e8ce4f8cd1214882adb65f7de94c31577052ac4e69808345809b44acb0b2bd889175fb75dd050c5a449ab9528f8f78daa10c",
	"G",

	/* ecdsa_secp256r1_sha256_test.json - 336 */
	"ecdsa_secp256r1_sha256_test.json - 336",
	"042927b10512bae3eddcfe467828128bad2903269919f7086069c8c4df6c732838c7787964eaac00e5921fb1498a60f4606766b3d9685001558d1a974e7341513e",
	"313333383731363438",
	"ffcda40f792ce4d93e7e0f0e95e1a2147dddd7f6487621c30a03d710b330021979938b55f8a17f7ed7ba9ade8f2065a1fa77618f0b67add8d58c422c2453a49a",
	"G",

	/* ecdsa_secp256r1_sha256_test.json - 337 */
	"ecdsa_secp256r1_sha256_test.json - 337",
	"042927b10512bae3eddcfe467828128bad2903269919f7086069c8c4df6c732838c7787964eaac00e5921fb1498a60f4606766b3d9685001558d1a974e7341513e",
	"333232313434313632",
	"81f2359c4faba6b53d3e8c8c3fcc16a948350f7ab3a588b28c17603a431e39a8cd6f6a5cc3b55ead0ff695d06c6860b509e46d99fccefb9f7f9e101857f74300",
	"G",

	/* ecdsa_secp256r1_sha256_test.json - 338 */
	"ecdsa_secp256r1_sha256_test.json - 338",
	"042927b10512bae3eddcfe467828128bad2903269919f7086069c8c4df6c732838c7787964eaac00e5921fb1498a60f4606766b3d9685001558d1a974e7341513e",
	"3130363836363535353436",
	"dfc8bf520445cbb8ee1596fb073ea283ea130251a6fdffa5c3f5f2aaf75ca808048e33efce147c9dd92823640e338e68bfd7d0dc7a4905b3a7ac711e577e90e7",
	"G",

	/* ecdsa_secp256r1_sha256_test.json - 339 */
	"ecdsa_secp256r1_sha256_test.json - 339",
	"042927b10512bae3eddcfe467828128bad2903269919f7086069c8c4df6c732838c7787964eaac00e5921fb1498a60f4606766b3d9685001558d1a974e7341513e",
	"3632313535323436",
	"ad019f74c6941d20efda70b46c53db166503a0e393e932f688227688ba6a576293320eb7ca0710255346bdbb3102cdcf7964ef2e0988e712bc05efe16c199345",
	"G",

	/* ecdsa_secp256r1_sha256_test.json - 340 */
	"ecdsa_secp256r1_sha256_test.json - 340",
	"042927b10512bae3eddcfe467828128bad2903269919f7086069c8c4df6c732838c7787964eaac00e5921fb1498a60f4606766b3d9685001558d1a974e7341513e",
	"37303330383138373734",
	"ac8096842e8add68c34e78ce11dd71e4b54316bd3ebf7fffdeb7bd5a3ebc1883f5ca2f4f23d674502d4caf85d187215d36e3ce9f0ce219709f21a3aac003b7a8",
	"G",

	/* ecdsa_secp256r1_sha256_test.json - 341 */
	"ecdsa_secp256r1_sha256_test.json - 341",
	"042927b10512bae3eddcfe467828128bad2903269919f7086069c8c4df6c732838c7787964eaac00e5921fb1498a60f4606766b3d9685001558d1a974e7341513e",
	"35393234353233373434",
	"677b2d3a59b18a5ff939b70ea002250889ddcd7b7b9d776854b4943693fb92f76b4ba856ade7677bf30307b21f3ccda35d2f63aee81efd0bab6972cc0795db55",
	"G",

	/* ecdsa_secp256r1_sha256_test.json - 342 */
	"ecdsa_secp256r1_sha256_test.json - 342",
	"042927b10512bae3eddcfe467828128bad2903269919f7086069c8c4df6c732838c7787964eaac00e5921fb1498a60f4606766b3d9685001558d1a974e7341513e",
	"31343935353836363231",
	"479e1ded14bcaed0379ba8e1b73d3115d84d31d4b7c30e1f05e1fc0d5957cfb0918f79e35b3d89487cf634a4f05b2e0c30857ca879f97c771e877027355b2443",
	"G",

	/* ecdsa_secp256r1_sha256_test.json - 343 */
	"ecdsa_secp256r1_sha256_test.json - 343",
	"042927b10512bae3eddcfe467828128bad2903269919f7086069c8c4df6c732838c7787964eaac00e5921fb1498a60f4606766b3d9685001558d1a974e7341513e",
	"34303035333134343036",
	"43dfccd0edb9e280d9a58f01164d55c3d711e14b12ac5cf3b64840ead512a0a31dbe33fa8ba84533cd5c4934365b3442ca1174899b78ef9a3199f49584389772",
	"G",

	/* ecdsa_secp256r1_sha256_test.json - 344 */
	"ecdsa_secp256r1_sha256_test.json - 344",
	"042927b10512bae3eddcfe467828128bad2903269919f7086069c8c4df6c732838c7787964eaac00e5921fb1498a60f4606766b3d9685001558d1a974e7341513e",
	"33303936343537353132",
	"5b09ab637bd4caf0f4c7c7e4bca592fea20e9087c259d26a38bb4085f0bbff1145b7eb467b6748af618e9d80d6fdcd6aa24964e5a13f885bca8101de08eb0d75",
	"G",

	/* ecdsa_secp256r1_sha256_test.json - 345 */
	"ecdsa_secp256r1_sha256_test.json - 345",
	"042927b10512bae3eddcfe467828128bad2903269919f7086069c8c4df6c732838c7787964eaac00e5921fb1498a60f4606766b3d9685001558d1a974e7341513e",
	"32373834303235363230",
	"5e9b1c5a028070df5728c5c8af9b74e0667afa570a6cfa0114a5039ed15ee06fb1360907e2d9785ead362bb8d7bd661b6c29eeffd3c5037744edaeb9ad990c20",
	"G",

	/* ecdsa_secp256r1_sha256_test.json - 346 */
	"ecdsa_secp256r1_sha256_test.json - 346",
	"042927b10512bae3eddcfe467828128bad2903269919f7086069c8c4df6c732838c7787964eaac00e5921fb1498a60f4606766b3d9685001558d1a974e7341513e",
	"32363138373837343138",
	"0671a0a85c2b72d54a2fb0990e34538b4890050f5a5712f6d1a7a5fb8578f32edb1846bab6b7361479ab9c3285ca41291808f27fd5bd4fdac720e5854713694c",
	"G",

	/* ecdsa_secp256r1_sha256_test.json - 347 */
	"ecdsa_secp256r1_sha256_test.json - 347",
	"042927b10512bae3eddcfe467828128bad2903269919f7086069c8c4df6c732838c7787964eaac00e5921fb1498a60f4606766b3d9685001558d1a974e7341513e",
	"31363432363235323632",
	"7673f8526748446477dbbb0590a45492c5d7d69859d301abbaedb35b2095103a3dc70ddf9c6b524d886bed9e6af02e0e4dec0d417a414fed3807ef4422913d7c",
	"G",

	/* ecdsa_secp256r1_sha256_test.json - 348 */
	"ecdsa_secp256r1_sha256_test.json - 348",
	"042927b10512bae3eddcfe467828128bad2903269919f7086069c8c4df6c732838c7787964eaac00e5921fb1498a60f4606766b3d9685001558d1a974e7341513e",
	"36383234313839343336",
	"7f085441070ecd2bb21285089ebb1aa6450d1a06c36d3ff39dfd657a796d12b5249712012029870a2459d18d47da9aa492a5e6cb4b2d8dafa9e4c5c54a2b9a8b",
	"G",

	/* ecdsa_secp256r1_sha256_test.json - 349 */
	"ecdsa_secp256r1_sha256_test.json - 349",
	"042927b10512bae3eddcfe467828128bad2903269919f7086069c8c4df6c732838c7787964eaac00e5921fb1498a60f4606766b3d9685001558d1a974e7341513e",
	"343834323435343235",
	"914c67fb61dd1e27c867398ea7322d5ab76df04bc5aa6683a8e0f30a5d287348fa07474031481dda4953e3ac1959ee8cea7e66ec412b38d6c96d28f6d37304ea",
	"G",

	/* ecdsa_secp256r1_sha256_test.json - 350 */
	"ecdsa_secp256r1_sha256_test.json - 350",
	"040ad99500288d466940031d72a9f5445a4d43784640855bf0a69874d2de5fe103c5011e6ef2c42dcd50d5d3d29f99ae6eba2c80c9244f4c5422f0979ff0c3ba5e",
	"313233343030",
	"000000000000000000000000000000004319055358e8617b0c46353d039cdaabffffffff00000000ffffffffffffffffbce6faada7179e84f3b9cac2fc63254e",
	"G",

	/* ecdsa_secp256r1_sha256_test.json - 351 */
	"ecdsa_secp256r1_sha256_test.json - 351",
	"040ad99500288d466940031d72a9f5445a4d43784640855bf0a69874d2de5fe103c5011e6ef2c42dcd50d5d3d29f99ae6eba2c80c9244f4c5422f0979ff0c3ba5e",
	"313233343030",
	"ffffffff00000001000000000000000000000000fffffffffffffffffffffffcffffffff00000000ffffffffffffffffbce6faada7179e84f3b9cac2fc63254e",
	"F",

	/* ecdsa_secp256r1_sha256_test.json - 352 */
	"ecdsa_secp256r1_sha256_test.json - 352",
	"04ab05fd9d0de26b9ce6f4819652d9fc69193d0aa398f0fba8013e09c58220455419235271228c786759095d12b75af0692dd4103f19f6a8c32f49435a1e9b8d45",
	"313233343030",
	"ffffffff00000000ffffffffffffffffbce6faada7179e84f3b9cac2fc63254fffffffff00000000ffffffffffffffffbce6faada7179e84f3b9cac2fc63254e",
	"G",

	/* ecdsa_secp256r1_sha256_test.json - 353 */
	"ecdsa_secp256r1_sha256_test.json - 353",
	"0480984f39a1ff38a86a68aa4201b6be5dfbfecf876219710b07badf6fdd4c6c5611feb97390d9826e7a06dfb41871c940d74415ed3cac2089f1445019bb55ed95",
	"313233343030",
	"7ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffd909135bdb6799286170f5ead2de4f6511453fe50914f3df2de54a36383df8dd4",
	"G",

	/* ecdsa_secp256r1_sha256_test.json - 354 */
	"ecdsa_secp256r1_sha256_test.json - 354",
	"044201b4272944201c3294f5baa9a3232b6dd687495fcc19a70a95bc602b4f7c0595c37eba9ee8171c1bb5ac6feaf753bc36f463e3aef16629572c0c0a8fb0800e",
	"313233343030",
	"7ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffd27b4577ca009376f71303fd5dd227dcef5deb773ad5f5a84360644669ca249a5",
	"G",

	/* ecdsa_secp256r1_sha256_test.json - 355 */
	"ecdsa_secp256r1_sha256_test.json - 355",
	"04a71af64de5126a4a4e02b7922d66ce9415ce88a4c9d25514d91082c8725ac9575d47723c8fbe580bb369fec9c2665d8e30a435b9932645482e7c9f11e872296b",
	"313233343030",
	"00000000000000000000000000000000000000000000000000000000000000050000000000000000000000000000000000000000000000000000000000000001",
	"G",

	/* ecdsa_secp256r1_sha256_test.json - 356 */
	"ecdsa_secp256r1_sha256_test.json - 356",
	"046627cec4f0731ea23fc2931f90ebe5b7572f597d20df08fc2b31ee8ef16b15726170ed77d8d0a14fc5c9c3c4c9be7f0d3ee18f709bb275eaf2073e258fe694a5",
	"313233343030",
	"00000000000000000000000000000000000000000000000000000000000000050000000000000000000000000000000000000000000000000000000000000003",
	"G",

	/* ecdsa_secp256r1_sha256_test.json - 357 */
	"ecdsa_secp256r1_sha256_test.json - 357",
	"045a7c8825e85691cce1f5e7544c54e73f14afc010cb731343262ca7ec5a77f5bfef6edf62a4497c1bd7b147fb6c3d22af3c39bfce95f30e13a16d3d7b2812f813",
	"313233343030",
	"00000000000000000000000000000000000000000000000000000000000000050000000000000000000000000000000000000000000000000000000000000005",
	"G",

	/* ecdsa_secp256r1_sha256_test.json - 358 */
	"ecdsa_secp256r1_sha256_test.json - 358",
	"04cbe0c29132cd738364fedd603152990c048e5e2fff996d883fa6caca7978c73770af6a8ce44cb41224b2603606f4c04d188e80bff7cc31ad5189d4ab0d70e8c1",
	"313233343030",
	"00000000000000000000000000000000000000000000000000000000000000050000000000000000000000000000000000000000000000000000000000000006",
	"G",

	/* ecdsa_secp256r1_sha256_test.json - 359 */
	"ecdsa_secp256r1_sha256_test.json - 359",
	"042ef747671c97d9c7f9cb2f6a30d678c3d84757ba241ef7183d51a29f52d87c2ea8fb2ea635b761baefc1c4ded2099281b844e13e044c328553bbbafa337d8a76",
	"313233343030",
	"00000000000000000000000000000000000000000000000000000000000000060000000000000000000000000000000000000000000000000000000000000001",
	"G",

	/* ecdsa_secp256r1_sha256_test.json - 360 */
	"ecdsa_secp256r1_sha256_test.json - 360",
	"04931cc49cda4d87d25b1601c56c3b83b4f45e44971998f2d3e7d3c55152214edf058dc140abbba42fc1ddbf30dab8eb9b46ee7338b3f7ee96242bf45e1df5e995",
	"313233343030",
	"00000000000000000000000000000000000000000000000000000000000000060000000000000000000000000000000000000000000000000000000000000003",
	"G",

	/* ecdsa_secp256r1_sha256_test.json - 361 */
	"ecdsa_secp256r1_sha256_test.json - 361",
	"04899a4af61867e3f3c190dbb48f8bc9fc74b70a467a4a1f06477b3af2f39ab8ed47ac000f9ea8a3034939bf48ad5d061a69fc8495ae4df2dbec7effa03a0062b3",
	"313233343030",
	"00000000000000000000000000000000000000000000000000000000000000060000000000000000000000000000000000000000000000000000000000000006",
	"G",

	/* ecdsa_secp256r1_sha256_test.json - 362 */
	"ecdsa_secp256r1_sha256_test.json - 362",
	"04d03eb09913cc20c6a8d0070f0d8d2a7f63527fafa44117fce6bd1ef2aa4ae3c46d5df3f45ac58fa334c6d102381b3120b7a2455600dcaff3d1a845514f12bf46",
	"313233343030",
	"00000000000000000000000000000000000000000000000000000000000000060000000000000000000000000000000000000000000000000000000000000007",
	"G",

	/* ecdsa_secp256r1_sha256_test.json - 363 */
	"ecdsa_secp256r1_sha256_test.json - 363",
	"04d03eb09913cc20c6a8d0070f0d8d2a7f63527fafa44117fce6bd1ef2aa4ae3c46d5df3f45ac58fa334c6d102381b3120b7a2455600dcaff3d1a845514f12bf46",
	"313233343030",
	"ffffffff00000000ffffffffffffffffbce6faada7179e84f3b9cac2fc6325570000000000000000000000000000000000000000000000000000000000000007",
	"F",

	/* ecdsa_secp256r1_sha256_test.json - 364 */
	"ecdsa_secp256r1_sha256_test.json - 364",
	"043a72476291571193b4d109b2c37b59f2807e8fe9cffd804eacded903e77ca0da592dbc74fee0ca7508cc7bc282b0c51a143286ff53c60131668e7a0929e4ed04",
	"313233343030",
	"0000000000000000000000000000000000000000000000000000000000000006ffffffff00000000ffffffffffffffffbce6faada7179e84f3b9cac2fc75fbd8",
	"F",

	/* ecdsa_secp256r1_sha256_test.json - 365 */
	"ecdsa_secp256r1_sha256_test.json - 365",
	"04d0f73792203716afd4be4329faa48d269f15313ebbba379d7783c97bf3e890d9971f4a3206605bec21782bf5e275c714417e8f566549e6bc68690d2363c89cc1",
	"313233343030",
	"00000000000000000000000000000000000000000000000000000000000001008f1e3c7862c58b16bb76eddbb76eddbb516af4f63f2d74d76e0d28c9bb75ea88",
	"G",

	/* ecdsa_secp256r1_sha256_test.json - 366 */
	"ecdsa_secp256r1_sha256_test.json - 366",
	"044838b2be35a6276a80ef9e228140f9d9b96ce83b7a254f71ccdebbb8054ce05ffa9cbc123c919b19e00238198d04069043bd660a828814051fcb8aac738a6c6b",
	"313233343030",
	"000000000000000000000000000000000000000000000000002d9b4d347952d6ef3043e7329581dbb3974497710ab11505ee1c87ff907beebadd195a0ffe6d7a",
	"G",

	/* ecdsa_secp256r1_sha256_test.json - 367 */
	"ecdsa_secp256r1_sha256_test.json - 367",
	"047393983ca30a520bbc4783dc9960746aab444ef520c0a8e771119aa4e74b0f64e9d7be1ab01a0bf626e709863e6a486dbaf32793afccf774e2c6cd27b1857526",
	"313233343030",
	"000000000000000000000000000000000000001033e67e37b32b445580bf4eff8b748b74000000008b748b748b748b7466e769ad4a16d3dcd87129b8e91d1b4d",
	"G",

	/* ecdsa_secp256r1_sha256_test.json - 368 */
	"ecdsa_secp256r1_sha256_test.json - 368",
	"045ac331a1103fe966697379f356a937f350588a05477e308851b8a502d5dfcdc5fe9993df4b57939b2b8da095bf6d794265204cfe03be995a02e65d408c871c0b",
	"313233343030",
	"0000000000000000000000000000000000000000000000000000000000000100ef9f6ba4d97c09d03178fa20b4aaad83be3cf9cb824a879fec3270fc4b81ef5b",
	"G",

	/* ecdsa_secp256r1_sha256_test.json - 369 */
	"ecdsa_secp256r1_sha256_test.json - 369",
	"041d209be8de2de877095a399d3904c74cc458d926e27bb8e58e5eae5767c41509dd59e04c214f7b18dce351fc2a549893a6860e80163f38cc60a4f2c9d040d8c9",
	"313233343030",
	"00000000000000000000000000000000000000062522bbd3ecbe7c39e93e7c25ef9f6ba4d97c09d03178fa20b4aaad83be3cf9cb824a879fec3270fc4b81ef5b",
	"G",

	/* ecdsa_secp256r1_sha256_test.json - 370 */
	"ecdsa_secp256r1_sha256_test.json - 370",
	"04083539fbee44625e3acaafa2fcb41349392cef0633a1b8fabecee0c133b10e99915c1ebe7bf00df8535196770a58047ae2a402f26326bb7d41d4d7616337911e",
	"313233343030",
	"ffffffff00000000ffffffffffffffffbce6faada7179e84f3b9cac2fc6324d5555555550000000055555555555555553ef7a8e48d07df81a693439654210c70",
	"G",

	/* ecdsa_secp256r1_sha256_test.json - 371 */
	"ecdsa_secp256r1_sha256_test.json - 371",
	"04e075effd9607d08d5f34e3652f64cfa3bd6d20c58d0a232f058491260ab212a4cc61760ac8b0680c1b644c03cc628ba9dc4a3c0561368489c692bd40f43aa3ca",
	"313233343030",
	"0000000000000000000000000000000000000000000000009c44febf31c3594f000000000000000000000000000000000000000000000000839ed28247c2b06b",
	"G",

	/* ecdsa_secp256r1_sha256_test.json - 372 */
	"ecdsa_secp256r1_sha256_test.json - 372",
	"04cffb758c3073ea3c08efd9f7f17a85b6ae385c5a140c146ad5f1f5a826718bc8dfdc6bebc894144c6d418ac5d97339726ad2ae925df868426e5628e9f4e62342",
	"313233343030",
	"0000000000000000000000000000000000000009df8b682430beef6f5fd7c7cd000000000000000000000000000000000000000fd0a62e13778f4222a0d61c8a",
	"G",

	/* ecdsa_secp256r1_sha256_test.json - 373 */
	"ecdsa_secp256r1_sha256_test.json - 373",
	"04b98740e69e61a325d5f772e3b5c4f67fb7150b16a9afeca9ddc4afcbb6fa0549c446e814138e4ebc82dbf86a390056d4595dcf45e381fef217a4597d7bd51498",
	"313233343030",
	"000000000000000000000000000000008a598e563a89f526c32ebec8de26367c0000000000000000000000000000000084f633e2042630e99dd0f1e16f7a04bf",
	"G",

	/* ecdsa_secp256r1_sha256_test.json - 374 */
	"ecdsa_secp256r1_sha256_test.json - 374",
	"0484536a270c3932bb2084732adf2c768efc6d3977e5220229ea9a44888b8f9d7b1766398cdac2fc8000017b29a7ba15a58f196037f35f7008ed4286ddff00fd46",
	"313233343030",
	"000000000000000000000000aa6eeb5823f7fa31b466bb473797f0d0314c0bdf000000000000000000000000e2977c479e6d25703cebbc6bd561938cc9d1bfb9",
	"G",

	/* ecdsa_secp256r1_sha256_test.json - 375 */
	"ecdsa_secp256r1_sha256_test.json - 375",
	"048aeb368a7027a4d64abdea37390c0c1d6a26f399e2d9734de1eb3d0e1937387405bd13834715e1dbae9b875cf07bd55e1b6691c7f7536aef3b19bf7a4adf576d",
	"313233343030",
	"555555550000000055555555555555553ef7a8e48d07df81a693439654210c700000000000000000000000000000000000000000000000000000000000000001",
	"G",

	/* ecdsa_secp256r1_sha256_test.json - 376 */
	"ecdsa_secp256r1_sha256_test.json - 376",
	"048aeb368a7027a4d64abdea37390c0c1d6a26f399e2d9734de1eb3d0e1937387405bd13834715e1dbae9b875cf07bd55e1b6691c7f7536aef3b19bf7a4adf576d",
	"313233343030",
	"555555550000000055555555555555553ef7a8e48d07df81a693439654210c700000000000000000000000000000000000000000000000000000000000000000",
	"F",

	/* ecdsa_secp256r1_sha256_test.json - 377 */
	"ecdsa_secp256r1_sha256_test.json - 377",
	"0461722eaba731c697c7a9ba4d0afdbb5713d8aa12b0eab601bb33dbaf792c5adc272cd993b2b663aba5b3a26c101182ff178684945e83879e71598b95fe647dfc",
	"313233343030",
	"555555550000000055555555555555553ef7a8e48d07df81a693439654210c7002f676969f451a8ccafa4c4f09791810e6d632dbd60b1d5540f3284fbe1889b0",
	"G",

	/* ecdsa_secp256r1_sha256_test.json - 378 */
	"ecdsa_secp256r1_sha256_test.json - 378",
	"04c4c91981e720e20d7e478ff19d09b95a98f58c0f469b72801a8ce844a347316594afcd4188182e7779889b3258d0368ece1e66797fe7c648c6f0b9e26bd71871",
	"313233343030",
	"555555550000000055555555555555553ef7a8e48d07df81a693439654210c704e260962e33362ef0046126d2d5a4edc6947ab20e19b8ec19cf79e5908b6e628",
	"G",

	/* ecdsa_secp256r1_sha256_test.json - 379 */
	"ecdsa_secp256r1_sha256_test.json - 379",
	"04d58d47bf49bc8f416641f6f760fcbca80aa52a814e56a5fa40bab44fd6f6317216deaa84d45d8e0e29cc9ecf5653f8ee6444750813becae8deb42b04ba07a634",
	"313233343030",
	"555555550000000055555555555555553ef7a8e48d07df81a693439654210c70077ed0d8f20f697d8fc591ac64dd5219c7932122b4f9b9ec6441e44a0092cf21",
	"G",

	/* ecdsa_secp256r1_sha256_test.json - 380 */
	"ecdsa_secp256r1_sha256_test.json - 380",
	"0491e305822e5e44f3fdb616e2ef42cd98f241b86e9f68815bc4dba6a945e4eefb3c5937e2ac1d9466f6d65e49b35fc8d75ffc22e1fe2f32af42f5fa3c26f9b4b0",
	"313233343030",
	"555555550000000055555555555555553ef7a8e48d07df81a693439654210c703e0292a67e181c6c0105ee35e956e78e9bdd033c6e71ae57884039a245e4175f",
	"G",

	/* ecdsa_secp256r1_sha256_test.json - 381 */
	"ecdsa_secp256r1_sha256_test.json - 381",
	"0424a0bc4d16dbbd40d2fd81a7c3f8d8ec741607d5bb406a0611cc60d0e683bd46b575cad039c15f7f3dffcfc007b4b0f743c871ecc76a504a32672fd84526d861",
	"313233343030",
	"555555550000000055555555555555553ef7a8e48d07df81a693439654210c7013d22b06d6b8f5d97e0c64962b4a3bae30f668ca6217ef5b35d799f159e23ebe",
	"G",

	/* ecdsa_secp256r1_sha256_test.json - 382 */
	"ecdsa_secp256r1_sha256_test.json - 382",
	"04d24dd06745cafb39186d22a92aa0e58169a79ab69488628a9da5ed3ef747269b7e9209d98faeb95355948adae61d5291c6015d3ee9513486d886fb05cbd25c6a",
	"313233343030",
	"555555550000000055555555555555553ef7a8e48d07df81a693439654210c704523ce342e4994bb8968bf6613f60c06c86111f15a3a389309e72cd447d5dd99",
	"G",

	/* ecdsa_secp256r1_sha256_test.json - 383 */
	"ecdsa_secp256r1_sha256_test.json - 383",
	"048200f148e7eab1581bcd1e23946f8a9b8191d9641f9560341721f9d3fec3d63ece795669e0481e035de8623d716a6984d0a4809d6c65519443ee55260f7f3dcb",
	"313233343030",
	"555555550000000055555555555555553ef7a8e48d07df81a693439654210c7037d765be3c9c78189ad30edb5097a4db670de11686d01420e37039d4677f4809",
	"G",

	/* ecdsa_secp256r1_sha256_test.json - 384 */
	"ecdsa_secp256r1_sha256_test.json - 384",
	"04a8a69c5ed33b150ce8d37ac197070ed894c05d47258a80c9041d92486622024de85997c9666b60a393568efede8f4ca0167c1e10f626e62fc1b8c8e9c6ba6ed7",
	"313233343030",
	"555555550000000055555555555555553ef7a8e48d07df81a693439654210c7044237823b54e0c74c2bf5f759d9ac5f8cb897d537ffa92effd4f0bb6c9acd860",
	"G",

	/* ecdsa_secp256r1_sha256_test.json - 385 */
	"ecdsa_secp256r1_sha256_test.json - 385",
	"04ed0587e75b3b9a1dd0794f41d1729fcd432b2436cbf51c230d8bc7273273181735a57f09c7873d3964aa8102c9e25fa53070cd924cb7e3a459174740b8b71c34",
	"313233343030",
	"555555550000000055555555555555553ef7a8e48d07df81a693439654210c70266d30a485385906054ca86d46f5f2b17e7f4646a3092092ad92877126538111",
	"G",

	/* ecdsa_secp256r1_sha256_test.json - 386 */
	"ecdsa_secp256r1_sha256_test.json - 386",
	"04077091d99004a99ee08224e59a46a70495e6fba4eff681c3ce42127e588681ef4f1c16c77dfa440dde18245c9de76243d8f2fd9dea3f2782d6c04974d02f25dc",
	"313233343030",
	"555555550000000055555555555555553ef7a8e48d07df81a693439654210c70538c7b3798e84d0ce90340165806348971ed44db8f0c674f5f215968390f92ee",
	"G",

	/* ecdsa_secp256r1_sha256_test.json - 387 */
	"ecdsa_secp256r1_sha256_test.json - 387",
	"04616a8b8e57d82c11678f5827911024cd23a16cb52a65f230fb554a7b110c35a5bb466660be5cab3e4b587c12b45bd998bd56c7d66c2f94d03a1a6d2028d8a154",
	"313233343030",
	"555555550000000055555555555555553ef7a8e48d07df81a693439654210c706fef0ef15d1688e15e704c4e6bb8bb7f40d52d3af5c661bb78c4ed9b408699b3",
	"G",

	/* ecdsa_secp256r1_sha256_test.json - 388 */
	"ecdsa_secp256r1_sha256_test.json - 388",
	"0471dc92b2b1baa7612c4a53427a0d2dfe548fa9cf829bb6b248f736a5eb30b513f91c7dff1144cb36057c2b859f35bd666a7961833b06de0f45159fbae208e326",
	"313233343030",
	"555555550000000055555555555555553ef7a8e48d07df81a693439654210c706f44275e9aeb1331efcb8d58f35c0252791427e403ad84daad51d247cc2a64c6",
	"G",

	/* ecdsa_secp256r1_sha256_test.json - 389 */
	"ecdsa_secp256r1_sha256_test.json - 389",
	"04662f43ae614bd9c90ff3fcded25cf0ef186b6967a47aa6aa7ae7f396594df931f5f94a525edd50d3738f7a28d03d7a2a70095c8f89de9bb2c645fea8d8bac9e0",
	"313233343030",
	"555555550000000055555555555555553ef7a8e48d07df81a693439654210c7021323755b103d2f9da6ab83eccab9ad8598bcf625652f10e7a3eeee3c3945fb3",
	"G",

	/* ecdsa_secp256r1_sha256_test.json - 390 */
	"ecdsa_secp256r1_sha256_test.json - 390",
	"04dff107959bd2f7386497a5624430a0ab35e552c1a4e4dc9c298caeb96353170dcb5065d7947a676c76287ca8e430324f8a534b0ba6f21200e033c4b88852a3cc",
	"313233343030",
	"555555550000000055555555555555553ef7a8e48d07df81a693439654210c706c50acfe76de1289e7a5edb240f1c2a7879db6873d5d931f3c6ac467a6eac171",
	"G",

	/* ecdsa_secp256r1_sha256_test.json - 391 */
	"ecdsa_secp256r1_sha256_test.json - 391",
	"04bd0862b0bfba85036922e06f5458754aafc3075b603a814b3ac75659bf24d7528258a607ffca2cfe05a300cb4c3c4e1963bbb1bc54d320e16969f85aad243385",
	"313233343030",
	"555555550000000055555555555555553ef7a8e48d07df81a693439654210c70755b7fffb0b17ad57dca50fcefb7fe297b029df25e5ccb5069e8e70c2742c2a6",
	"G",

	/* ecdsa_secp256r1_sha256_test.json - 392 */
	"ecdsa_secp256r1_sha256_test.json - 392",
	"04b533d4695dd5b8c5e07757e55e6e516f7e2c88fa0239e23f60e8ec07dd70f2871b134ee58cc583278456863f33c3a85d881f7d4a39850143e29d4eaf009afe47",
	"313233343030",
	"7fffffff800000007fffffffffffffffde737d56d38bcf4279dce5617e3192a8555555550000000055555555555555553ef7a8e48d07df81a693439654210c70",
	"F",

	/* ecdsa_secp256r1_sha256_test.json - 393 */
	"ecdsa_secp256r1_sha256_test.json - 393",
	"04f50d371b91bfb1d7d14e1323523bc3aa8cbf2c57f9e284de628c8b4536787b86f94ad887ac94d527247cd2e7d0c8b1291c553c9730405380b14cbb209f5fa2dd",
	"313233343030",
	"7fffffff800000007fffffffffffffffde737d56d38bcf4279dce5617e3192a97fffffff800000007fffffffffffffffde737d56d38bcf4279dce5617e3192a8",
	"G",

	/* ecdsa_secp256r1_sha256_test.json - 394 */
	"ecdsa_secp256r1_sha256_test.json - 394",
	"0468ec6e298eafe16539156ce57a14b04a7047c221bafc3a582eaeb0d857c4d94697bed1af17850117fdb39b2324f220a5698ed16c426a27335bb385ac8ca6fb30",
	"313233343030",
	"7fffffff800000007fffffffffffffffde737d56d38bcf4279dce5617e3192a97fffffff800000007fffffffffffffffde737d56d38bcf4279dce5617e3192a9",
	"G",

	/* ecdsa_secp256r1_sha256_test.json - 395 */
	"ecdsa_secp256r1_sha256_test.json - 395",
	"0469da0364734d2e530fece94019265fefb781a0f1b08f6c8897bdf6557927c8b866d2d3c7dcd518b23d726960f069ad71a933d86ef8abbcce8b20f71e2a847002",
	"313233343030",
	"555555550000000055555555555555553ef7a8e48d07df81a693439654210c70bb5a52f42f9c9261ed4361f59422a1e30036e7c32b270c8807a419feca605023",
	"G",

	/* ecdsa_secp256r1_sha256_test.json - 396 */
	"ecdsa_secp256r1_sha256_test.json - 396",
	"04d8adc00023a8edc02576e2b63e3e30621a471e2b2320620187bf067a1ac1ff3233e2b50ec09807accb36131fff95ed12a09a86b4ea9690aa32861576ba2362e1",
	"313233343030",
	"555555550000000055555555555555553ef7a8e48d07df81a693439654210c7044a5ad0ad0636d9f12bc9e0a6bdd5e1cbcb012ea7bf091fcec15b0c43202d52e",
	"G",

	/* ecdsa_secp256r1_sha256_test.json - 397 */
	"ecdsa_secp256r1_sha256_test.json - 397",
	"043623ac973ced0a56fa6d882f03a7d5c7edca02cfc7b2401fab3690dbe75ab7858db06908e64b28613da7257e737f39793da8e713ba0643b92e9bb3252be7f8fe",
	"313233343030",
	"555555550000000055555555555555553ef7a8e48d07df81a693439654210c70555555550000000055555555555555553ef7a8e48d07df81a693439654210c70",
	"G",

	/* ecdsa_secp256r1_sha256_test.json - 398 */
	"ecdsa_secp256r1_sha256_test.json - 398",
	"04cf04ea77e9622523d894b93ff52dc3027b31959503b6fa3890e5e04263f922f1e8528fb7c006b3983c8b8400e57b4ed71740c2f3975438821199bedeaecab2e9",
	"313233343030",
	"555555550000000055555555555555553ef7a8e48d07df81a693439654210c70aaaaaaaa00000000aaaaaaaaaaaaaaaa7def51c91a0fbf034d26872ca84218e1",
	"G",

	/* ecdsa_secp256r1_sha256_test.json - 399 */
	"ecdsa_secp256r1_sha256_test.json - 399",
	"04db7a2c8a1ab573e5929dc24077b508d7e683d49227996bda3e9f78dbeff773504f417f3bc9a88075c2e0aadd5a13311730cf7cc76a82f11a36eaf08a6c99a206",
	"313233343030",
	"7ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffde91e1ba60fdedb76a46bcb51dc0b8b4b7e019f0a28721885fa5d3a8196623397",
	"G",

	/* ecdsa_secp256r1_sha256_test.json - 400 */
	"ecdsa_secp256r1_sha256_test.json - 400",
	"04dead11c7a5b396862f21974dc4752fadeff994efe9bbd05ab413765ea80b6e1f1de3f0640e8ac6edcf89cff53c40e265bb94078a343736df07aa0318fc7fe1ff",
	"313233343030",
	"7ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffdfdea5843ffeb73af94313ba4831b53fe24f799e525b1e8e8c87b59b95b430ad9",
	"G",

	/* ecdsa_secp256r1_sha256_test.json - 401 */
	"ecdsa_secp256r1_sha256_test.json - 401",
	"04d0bc472e0d7c81ebaed3a6ef96c18613bb1fea6f994326fbe80e00dfde67c7e9986c723ea4843d48389b946f64ad56c83ad70ff17ba85335667d1bb9fa619efd",
	"313233343030",
	"7ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffd03ffcabf2f1b4d2a65190db1680d62bb994e41c5251cd73b3c3dfc5e5bafc035",
	"G",

	/* ecdsa_secp256r1_sha256_test.json - 402 */
	"ecdsa_secp256r1_sha256_test.json - 402",
	"04a0a44ca947d66a2acb736008b9c08d1ab2ad03776e02640f78495d458dd51c326337fe5cf8c4604b1f1c409dc2d872d4294a4762420df43a30a2392e40426add",
	"313233343030",
	"7ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffd4dfbc401f971cd304b33dfdb17d0fed0fe4c1a88ae648e0d2847f74977534989",
	"G",

	/* ecdsa_secp256r1_sha256_test.json - 403 */
	"ecdsa_secp256r1_sha256_test.json - 403",
	"04c9c2115290d008b45fb65fad0f602389298c25420b775019d42b62c3ce8a96b73877d25a8080dc02d987ca730f0405c2c9dbefac46f9e601cc3f06e9713973fd",
	"313233343030",
	"7ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffdbc4024761cd2ffd43dfdb17d0fed112b988977055cd3a8e54971eba9cda5ca71",
	"G",

	/* ecdsa_secp256r1_sha256_test.json - 404 */
	"ecdsa_secp256r1_sha256_test.json - 404",
	"045eca1ef4c287dddc66b8bccf1b88e8a24c0018962f3c5e7efa83bc1a5ff6033e5e79c4cb2c245b8c45abdce8a8e4da758d92a607c32cd407ecaef22f1c934a71",
	"313233343030",
	"7ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffd788048ed39a5ffa77bfb62fa1fda2257742bf35d128fb3459f2a0c909ee86f91",
	"G",

	/* ecdsa_secp256r1_sha256_test.json - 405 */
	"ecdsa_secp256r1_sha256_test.json - 405",
	"045caaa030e7fdf0e4936bc7ab5a96353e0a01e4130c3f8bf22d473e317029a47adeb6adc462f7058f2a20d371e9702254e9b201642005b3ceda926b42b178bef9",
	"313233343030",
	"7ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffd476d9131fd381bd917d0fed112bc9e0a5924b5ed5b11167edd8b23582b3cb15e",
	"G",

	/* ecdsa_secp256r1_sha256_test.json - 406 */
	"ecdsa_secp256r1_sha256_test.json - 406",
	"04c2fd20bac06e555bb8ac0ce69eb1ea20f83a1fc3501c8a66469b1a31f619b0986237050779f52b615bd7b8d76a25fc95ca2ed32525c75f27ffc87ac397e6cbaf",
	"313233343030",
	"7ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffd8374253e3e21bd154448d0a8f640fe46fafa8b19ce78d538f6cc0a19662d3601",
	"G",

	/* ecdsa_secp256r1_sha256_test.json - 407 */
	"ecdsa_secp256r1_sha256_test.json - 407",
	"043fd6a1ca7f77fb3b0bbe726c372010068426e11ea6ae78ce17bedae4bba86ced03ce5516406bf8cfaab8745eac1cd69018ad6f50b5461872ddfc56e0db3c8ff4",
	"313233343030",
	"7ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffd357cfd3be4d01d413c5b9ede36cba5452c11ee7fe14879e749ae6a2d897a52d6",
	"G",

	/* ecdsa_secp256r1_sha256_test.json - 408 */
	"ecdsa_secp256r1_sha256_test.json - 408",
	"049cb8e51e27a5ae3b624a60d6dc32734e4989db20e9bca3ede1edf7b086911114b4c104ab3c677e4b36d6556e8ad5f523410a19f2e277aa895fc57322b4427544",
	"313233343030",
	"7ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffd29798c5c0ee287d4a5e8e6b799fd86b8df5225298e6ffc807cd2f2bc27a0a6d8",
	"G",

	/* ecdsa_secp256r1_sha256_test.json - 409 */
	"ecdsa_secp256r1_sha256_test.json - 409",
	"04a3e52c156dcaf10502620b7955bc2b40bc78ef3d569e1223c262512d8f49602a4a2039f31c1097024ad3cc86e57321de032355463486164cf192944977df147f",
	"313233343030",
	"7ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffd0b70f22c781092452dca1a5711fa3a5a1f72add1bf52c2ff7cae4820b30078dd",
	"G",

	/* ecdsa_secp256r1_sha256_test.json - 410 */
	"ecdsa_secp256r1_sha256_test.json - 410",
	"04f19b78928720d5bee8e670fb90010fb15c37bf91b58a5157c3f3c059b2655e88cf701ec962fb4a11dcf273f5dc357e58468560c7cfeb942d074abd4329260509",
	"313233343030",
	"7ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffd16e1e458f021248a5b9434ae23f474b43ee55ba37ea585fef95c90416600f1ba",
	"G",

	/* ecdsa_secp256r1_sha256_test.json - 411 */
	"ecdsa_secp256r1_sha256_test.json - 411",
	"0483a744459ecdfb01a5cf52b27a05bb7337482d242f235d7b4cb89345545c90a8c05d49337b9649813287de9ffe90355fd905df5f3c32945828121f37cc50de6e",
	"313233343030",
	"7ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffd2252d6856831b6cf895e4f0535eeaf0e5e5809753df848fe760ad86219016a97",
	"G",

	/* ecdsa_secp256r1_sha256_test.json - 412 */
	"ecdsa_secp256r1_sha256_test.json - 412",
	"04dd13c6b34c56982ddae124f039dfd23f4b19bbe88cee8e528ae51e5d6f3a21d7bfad4c2e6f263fe5eb59ca974d039fc0e4c3345692fb5320bdae4bd3b42a45ff",
	"313233343030",
	"7ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffd81ffe55f178da695b28c86d8b406b15dab1a9e39661a3ae017fbe390ac0972c3",
	"G",

	/* ecdsa_secp256r1_sha256_test.json - 413 */
	"ecdsa_secp256r1_sha256_test.json - 413",
	"0467e6f659cdde869a2f65f094e94e5b4dfad636bbf95192feeed01b0f3deb7460a37e0a51f258b7aeb51dfe592f5cfd5685bbe58712c8d9233c62886437c38ba0",
	"313233343030",
	"7ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffd7fffffffaaaaaaaaffffffffffffffffe9a2538f37b28a2c513dee40fecbb71a",
	"G",

	/* ecdsa_secp256r1_sha256_test.json - 414 */
	"ecdsa_secp256r1_sha256_test.json - 414",
	"042eb6412505aec05c6545f029932087e490d05511e8ec1f599617bb367f9ecaaf805f51efcc4803403f9b1ae0124890f06a43fedcddb31830f6669af292895cb0",
	"313233343030",
	"7ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffdb62f26b5f2a2b26f6de86d42ad8a13da3ab3cccd0459b201de009e526adf21f2",
	"G",

	/* ecdsa_secp256r1_sha256_test.json - 415 */
	"ecdsa_secp256r1_sha256_test.json - 415",
	"0484db645868eab35e3a9fd80e056e2e855435e3a6b68d75a50a854625fe0d7f356d2589ac655edc9a11ef3e075eddda9abf92e72171570ef7bf43a2ee39338cfe",
	"313233343030",
	"7ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffdbb1d9ac949dd748cd02bbbe749bd351cd57b38bb61403d700686aa7b4c90851e",
	"G",

	/* ecdsa_secp256r1_sha256_test.json - 416 */
	"ecdsa_secp256r1_sha256_test.json - 416",
	"0491b9e47c56278662d75c0983b22ca8ea6aa5059b7a2ff7637eb2975e386ad66349aa8ff283d0f77c18d6d11dc062165fd13c3c0310679c1408302a16854ecfbd",
	"313233343030",
	"7ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffd66755a00638cdaec1c732513ca0234ece52545dac11f816e818f725b4f60aaf2",
	"G",

	/* ecdsa_secp256r1_sha256_test.json - 417 */
	"ecdsa_secp256r1_sha256_test.json - 417",
	"04f3ec2f13caf04d0192b47fb4c5311fb6d4dc6b0a9e802e5327f7ec5ee8e4834df97e3e468b7d0db867d6ecfe81e2b0f9531df87efdb47c1338ac321fefe5a432",
	"313233343030",
	"7ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffd55a00c9fcdaebb6032513ca0234ecfffe98ebe492fdf02e48ca48e982beb3669",
	"G",

	/* ecdsa_secp256r1_sha256_test.json - 418 */
	"ecdsa_secp256r1_sha256_test.json - 418",
	"04d92b200aefcab6ac7dafd9acaf2fa10b3180235b8f46b4503e4693c670fccc885ef2f3aebf5b317475336256768f7c19efb7352d27e4cccadc85b6b8ab922c72",
	"313233343030",
	"7ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffdab40193f9b5d76c064a27940469d9fffd31d7c925fbe05c919491d3057d66cd2",
	"G",

	/* ecdsa_secp256r1_sha256_test.json - 419 */
	"ecdsa_secp256r1_sha256_test.json - 419",
	"040a88361eb92ecca2625b38e5f98bbabb96bf179b3d76fc48140a3bcd881523cde6bdf56033f84a5054035597375d90866aa2c96b86a41ccf6edebf47298ad489",
	"313233343030",
	"7ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffdca0234ebb5fdcb13ca0234ecffffffffcb0dadbbc7f549f8a26b4408d0dc8600",
	"G",

	/* ecdsa_secp256r1_sha256_test.json - 420 */
	"ecdsa_secp256r1_sha256_test.json - 420",
	"04d0fb17ccd8fafe827e0c1afc5d8d80366e2b20e7f14a563a2ba50469d84375e868612569d39e2bb9f554355564646de99ac602cc6349cf8c1e236a7de7637d93",
	"313233343030",
	"7ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffdbfffffff3ea3677e082b9310572620ae19933a9e65b285598711c77298815ad3",
	"G",

	/* ecdsa_secp256r1_sha256_test.json - 421 */
	"ecdsa_secp256r1_sha256_test.json - 421",
	"04836f33bbc1dc0d3d3abbcef0d91f11e2ac4181076c9af0a22b1e4309d3edb2769ab443ff6f901e30c773867582997c2bec2b0cb8120d760236f3a95bbe881f75",
	"313233343030",
	"7ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffd266666663bbbbbbbe6666666666666665b37902e023fab7c8f055d86e5cc41f4",
	"G",

	/* ecdsa_secp256r1_sha256_test.json - 422 */
	"ecdsa_secp256r1_sha256_test.json - 422",
	"0492f99fbe973ed4a299719baee4b432741237034dec8d72ba5103cb33e55feeb8033dd0e91134c734174889f3ebcf1b7a1ac05767289280ee7a794cebd6e69697",
	"313233343030",
	"7ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffdbfffffff36db6db7a492492492492492146c573f4c6dfc8d08a443e258970b09",
	"G",

	/* ecdsa_secp256r1_sha256_test.json - 423 */
	"ecdsa_secp256r1_sha256_test.json - 423",
	"04d35ba58da30197d378e618ec0fa7e2e2d12cffd73ebbb2049d130bba434af09eff83986e6875e41ea432b7585a49b3a6c77cbb3c47919f8e82874c794635c1d2",
	"313233343030",
	"7ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffdbfffffff2aaaaaab7fffffffffffffffc815d0e60b3e596ecb1ad3a27cfd49c4",
	"G",

	/* ecdsa_secp256r1_sha256_test.json - 424 */
	"ecdsa_secp256r1_sha256_test.json - 424",
	"048651ce490f1b46d73f3ff475149be29136697334a519d7ddab0725c8d0793224e11c65bd8ca92dc8bc9ae82911f0b52751ce21dd9003ae60900bd825f590cc28",
	"313233343030",
	"7ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffd7fffffff55555555ffffffffffffffffd344a71e6f651458a27bdc81fd976e37",
	"G",

	/* ecdsa_secp256r1_sha256_test.json - 425 */
	"ecdsa_secp256r1_sha256_test.json - 425",
	"046d8e1b12c831a0da8795650ff95f101ed921d9e2f72b15b1cdaca9826b9cfc6def6d63e2bc5c089570394a4bc9f892d5e6c7a6a637b20469a58c106ad486bf37",
	"313233343030",
	"7ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffd3fffffff800000007fffffffffffffffde737d56d38bcf4279dce5617e3192aa",
	"G",

	/* ecdsa_secp256r1_sha256_test.json - 426 */
	"ecdsa_secp256r1_sha256_test.json - 426",
	"040ae580bae933b4ef2997cbdbb0922328ca9a410f627a0f7dff24cb4d920e15428911e7f8cc365a8a88eb81421a361ccc2b99e309d8dcd9a98ba83c3949d893e3",
	"313233343030",
	"7ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffd5d8ecd64a4eeba466815ddf3a4de9a8e6abd9c5db0a01eb80343553da648428f",
	"G",

	/* ecdsa_secp256r1_sha256_test.json - 427 */
	"ecdsa_secp256r1_sha256_test.json - 427",
	"045b812fd521aafa69835a849cce6fbdeb6983b442d2444fe70e134c027fc46963838a40f2a36092e9004e92d8d940cf5638550ce672ce8b8d4e15eba5499249e9",
	"313233343030",
	"6f2347cab7dd76858fe0555ac3bc99048c4aacafdfb6bcbe05ea6c42c4934569bb726660235793aa9957a61e76e00c2c435109cf9a15dd624d53f4301047856b",
	"G",

	/* ecdsa_secp256r1_sha256_test.json - 428 */
	"ecdsa_secp256r1_sha256_test.json - 428",
	"045b812fd521aafa69835a849cce6fbdeb6983b442d2444fe70e134c027fc469637c75bf0c5c9f6d17ffb16d2726bf30a9c7aaf31a8d317472b1ea145ab66db616",
	"313233343030",
	"6f2347cab7dd76858fe0555ac3bc99048c4aacafdfb6bcbe05ea6c42c4934569bb726660235793aa9957a61e76e00c2c435109cf9a15dd624d53f4301047856b",
	"F",

	/* ecdsa_secp256r1_sha256_test.json - 429 */
	"ecdsa_secp256r1_sha256_test.json - 429",
	"046adda82b90261b0f319faa0d878665a6b6da497f09c903176222c34acfef72a647e6f50dcc40ad5d9b59f7602bb222fad71a41bf5e1f9df4959a364c62e488d9",
	"313233343030",
	"0000000000000000000000000000000000000000000000000000000000000001555555550000000055555555555555553ef7a8e48d07df81a693439654210c70",
	"F",

	/* ecdsa_secp256r1_sha256_test.json - 431 */
	"ecdsa_secp256r1_sha256_test.json - 431",
	"04dd86d3b5f4a13e8511083b78002081c53ff467f11ebd98a51a633db76665d25045d5c8200c89f2fa10d849349226d21d8dfaed6ff8d5cb3e1b7e17474ebc18f7",
	"313233343030",
	"555555550000000055555555555555553ef7a8e48d07df81a693439654210c703333333300000000333333333333333325c7cbbc549e52e763f1f55a327a3aa9",
	"F",

	/* ecdsa_secp256r1_sha256_test.json - 432 */
	"ecdsa_secp256r1_sha256_test.json - 432",
	"044fea55b32cb32aca0c12c4cd0abfb4e64b0f5a516e578c016591a93f5a0fbcc5d7d3fd10b2be668c547b212f6bb14c88f0fecd38a8a4b2c785ed3be62ce4b280",
	"313233343030",
	"7cf27b188d034f7e8a52380304b51ac3c08969e277f21b35a60b48fc47669978555555550000000055555555555555553ef7a8e48d07df81a693439654210c70",
	"G",

	/* ecdsa_secp256r1_sha256_test.json - 433 */
	"ecdsa_secp256r1_sha256_test.json - 433",
	"04c6a771527024227792170a6f8eee735bf32b7f98af669ead299802e32d7c3107bc3b4b5e65ab887bbd343572b3e5619261fe3a073e2ffd78412f726867db589e",
	"313233343030",
	"7cf27b188d034f7e8a52380304b51ac3c08969e277f21b35a60b48fc47669978b6db6db6249249254924924924924924625bd7a09bec4ca81bcdd9f8fd6b63cc",
	"G",

	/* ecdsa_secp256r1_sha256_test.json - 434 */
	"ecdsa_secp256r1_sha256_test.json - 434",
	"04851c2bbad08e54ec7a9af99f49f03644d6ec6d59b207fec98de85a7d15b956efcee9960283045075684b410be8d0f7494b91aa2379f60727319f10ddeb0fe9d6",
	"313233343030",
	"7cf27b188d034f7e8a52380304b51ac3c08969e277f21b35a60b48fc47669978cccccccc00000000cccccccccccccccc971f2ef152794b9d8fc7d568c9e8eaa7",
	"G",

	/* ecdsa_secp256r1_sha256_test.json - 435 */
	"ecdsa_secp256r1_sha256_test.json - 435",
	"04f6417c8a670584e388676949e53da7fc55911ff68318d1bf3061205acb19c48f8f2b743df34ad0f72674acb7505929784779cd9ac916c3669ead43026ab6d43f",
	"313233343030",
	"7cf27b188d034f7e8a52380304b51ac3c08969e277f21b35a60b48fc476699783333333300000000333333333333333325c7cbbc549e52e763f1f55a327a3aaa",
	"G",

	/* ecdsa_secp256r1_sha256_test.json - 436 */
	"ecdsa_secp256r1_sha256_test.json - 436",
	"04501421277be45a5eefec6c639930d636032565af420cf3373f557faa7f8a06438673d6cb6076e1cfcdc7dfe7384c8e5cac08d74501f2ae6e89cad195d0aa1371",
	"313233343030",
	"7cf27b188d034f7e8a52380304b51ac3c08969e277f21b35a60b48fc4766997849249248db6db6dbb6db6db6db6db6db5a8b230d0b2b51dcd7ebf0c9fef7c185",
	"G",

	/* ecdsa_secp256r1_sha256_test.json - 437 */
	"ecdsa_secp256r1_sha256_test.json - 437",
	"040d935bf9ffc115a527735f729ca8a4ca23ee01a4894adf0e3415ac84e808bb343195a3762fea29ed38912bd9ea6c4fde70c3050893a4375850ce61d82eba33c5",
	"313233343030",
	"7cf27b188d034f7e8a52380304b51ac3c08969e277f21b35a60b48fc4766997816a4502e2781e11ac82cbc9d1edd8c981584d13e18411e2f6e0478c34416e3bb",
	"G",

	/* ecdsa_secp256r1_sha256_test.json - 438 */
	"ecdsa_secp256r1_sha256_test.json - 438",
	"045e59f50708646be8a589355014308e60b668fb670196206c41e748e64e4dca215de37fee5c97bcaf7144d5b459982f52eeeafbdf03aacbafef38e213624a01de",
	"313233343030",
	"6b17d1f2e12c4247f8bce6e563a440f277037d812deb33a0f4a13945d898c296555555550000000055555555555555553ef7a8e48d07df81a693439654210c70",
	"G",

	/* ecdsa_secp256r1_sha256_test.json - 439 */
	"ecdsa_secp256r1_sha256_test.json - 439",
	"04169fb797325843faff2f7a5b5445da9e2fd6226f7ef90ef0bfe924104b02db8e7bbb8de662c7b9b1cf9b22f7a2e582bd46d581d68878efb2b861b131d8a1d667",
	"313233343030",
	"6b17d1f2e12c4247f8bce6e563a440f277037d812deb33a0f4a13945d898c296b6db6db6249249254924924924924924625bd7a09bec4ca81bcdd9f8fd6b63cc",
	"G",

	/* ecdsa_secp256r1_sha256_test.json - 440 */
	"ecdsa_secp256r1_sha256_test.json - 440",
	"04271cd89c000143096b62d4e9e4ca885aef2f7023d18affdaf8b7b548981487540a1c6e954e32108435b55fa385b0f76481a609b9149ccb4b02b2ca47fe8e4da5",
	"313233343030",
	"6b17d1f2e12c4247f8bce6e563a440f277037d812deb33a0f4a13945d898c296cccccccc00000000cccccccccccccccc971f2ef152794b9d8fc7d568c9e8eaa7",
	"G",

	/* ecdsa_secp256r1_sha256_test.json - 441 */
	"ecdsa_secp256r1_sha256_test.json - 441",
	"043d0bc7ed8f09d2cb7ddb46ebc1ed799ab1563a9ab84bf524587a220afe499c12e22dc3b3c103824a4f378d96adb0a408abf19ce7d68aa6244f78cb216fa3f8df",
	"313233343030",
	"6b17d1f2e12c4247f8bce6e563a440f277037d812deb33a0f4a13945d898c2963333333300000000333333333333333325c7cbbc549e52e763f1f55a327a3aaa",
	"G",

	/* ecdsa_secp256r1_sha256_test.json - 442 */
	"ecdsa_secp256r1_sha256_test.json - 442",
	"04a6c885ade1a4c566f9bb010d066974abb281797fa701288c721bcbd23663a9b72e424b690957168d193a6096fc77a2b004a9c7d467e007e1f2058458f98af316",
	"313233343030",
	"6b17d1f2e12c4247f8bce6e563a440f277037d812deb33a0f4a13945d898c29649249248db6db6dbb6db6db6db6db6db5a8b230d0b2b51dcd7ebf0c9fef7c185",
	"G",

	/* ecdsa_secp256r1_sha256_test.json - 443 */
	"ecdsa_secp256r1_sha256_test.json - 443",
	"048d3c2c2c3b765ba8289e6ac3812572a25bf75df62d87ab7330c3bdbad9ebfa5c4c6845442d66935b238578d43aec54f7caa1621d1af241d4632e0b780c423f5d",
	"313233343030",
	"6b17d1f2e12c4247f8bce6e563a440f277037d812deb33a0f4a13945d898c29616a4502e2781e11ac82cbc9d1edd8c981584d13e18411e2f6e0478c34416e3bb",
	"G",

	/* ecdsa_secp256r1_sha256_test.json - 444 */
	"ecdsa_secp256r1_sha256_test.json - 444",
	"046b17d1f2e12c4247f8bce6e563a440f277037d812deb33a0f4a13945d898c2964fe342e2fe1a7f9b8ee7eb4a7c0f9e162bce33576b315ececbb6406837bf51f5",
	"313233343030",
	"bb5a52f42f9c9261ed4361f59422a1e30036e7c32b270c8807a419feca605023249249246db6db6ddb6db6db6db6db6dad4591868595a8ee6bf5f864ff7be0c2",
	"F",

	/* ecdsa_secp256r1_sha256_test.json - 445 */
	"ecdsa_secp256r1_sha256_test.json - 445",
	"046b17d1f2e12c4247f8bce6e563a440f277037d812deb33a0f4a13945d898c2964fe342e2fe1a7f9b8ee7eb4a7c0f9e162bce33576b315ececbb6406837bf51f5",
	"313233343030",
	"44a5ad0ad0636d9f12bc9e0a6bdd5e1cbcb012ea7bf091fcec15b0c43202d52e249249246db6db6ddb6db6db6db6db6dad4591868595a8ee6bf5f864ff7be0c2",
	"F",

	/* ecdsa_secp256r1_sha256_test.json - 446 */
	"ecdsa_secp256r1_sha256_test.json - 446",
	"046b17d1f2e12c4247f8bce6e563a440f277037d812deb33a0f4a13945d898c296b01cbd1c01e58065711814b583f061e9d431cca994cea1313449bf97c840ae0a",
	"313233343030",
	"bb5a52f42f9c9261ed4361f59422a1e30036e7c32b270c8807a419feca605023249249246db6db6ddb6db6db6db6db6dad4591868595a8ee6bf5f864ff7be0c2",
	"F",

	/* ecdsa_secp256r1_sha256_test.json - 447 */
	"ecdsa_secp256r1_sha256_test.json - 447",
	"046b17d1f2e12c4247f8bce6e563a440f277037d812deb33a0f4a13945d898c296b01cbd1c01e58065711814b583f061e9d431cca994cea1313449bf97c840ae0a",
	"313233343030",
	"44a5ad0ad0636d9f12bc9e0a6bdd5e1cbcb012ea7bf091fcec15b0c43202d52e249249246db6db6ddb6db6db6db6db6dad4591868595a8ee6bf5f864ff7be0c2",
	"F",

	/* ecdsa_secp256r1_sha256_test.json - 448 */
	"ecdsa_secp256r1_sha256_test.json - 448",
	"044f337ccfd67726a805e4f1600ae2849df3807eca117380239fbd816900000000ed9dea124cc8c396416411e988c30f427eb504af43a3146cd5df7ea60666d685",
	"4d657373616765",
	"d434e262a49eab7781e353a3565e482550dd0fd5defa013c7f29745eff3569f19b0c0a93f267fb6052fd8077be769c2b98953195d7bc10de844218305c6ba17a",
	"G",

	/* ecdsa_secp256r1_sha256_test.json - 449 */
	"ecdsa_secp256r1_sha256_test.json - 449",
	"044f337ccfd67726a805e4f1600ae2849df3807eca117380239fbd816900000000ed9dea124cc8c396416411e988c30f427eb504af43a3146cd5df7ea60666d685",
	"4d657373616765",
	"0fe774355c04d060f76d79fd7a772e421463489221bf0a33add0be9b1979110b500dcba1c69a8fbd43fa4f57f743ce124ca8b91a1f325f3fac6181175df55737",
	"G",

	/* ecdsa_secp256r1_sha256_test.json - 450 */
	"ecdsa_secp256r1_sha256_test.json - 450",
	"044f337ccfd67726a805e4f1600ae2849df3807eca117380239fbd816900000000ed9dea124cc8c396416411e988c30f427eb504af43a3146cd5df7ea60666d685",
	"4d657373616765",
	"bb40bf217bed3fb3950c7d39f03d36dc8e3b2cd79693f125bfd06595ee1135e3541bf3532351ebb032710bdb6a1bf1bfc89a1e291ac692b3fa4780745bb55677",
	"G",

	/* ecdsa_secp256r1_sha256_test.json - 451 */
	"ecdsa_secp256r1_sha256_test.json - 451",
	"043cf03d614d8939cfd499a07873fac281618f06b8ff87e8015c3f49726500493584fa174d791c72bf2ce3880a8960dd2a7c7a1338a82f85a9e59cdbde80000000",
	"4d657373616765",
	"664eb7ee6db84a34df3c86ea31389a5405badd5ca99231ff556d3e75a233e73a59f3c752e52eca46137642490a51560ce0badc678754b8f72e51a2901426a1bd",
	"G",

	/* ecdsa_secp256r1_sha256_test.json - 452 */
	"ecdsa_secp256r1_sha256_test.json - 452",
	"043cf03d614d8939cfd499a07873fac281618f06b8ff87e8015c3f49726500493584fa174d791c72bf2ce3880a8960dd2a7c7a1338a82f85a9e59cdbde80000000",
	"4d657373616765",
	"4cd0429bbabd2827009d6fcd843d4ce39c3e42e2d1631fd001985a79d1fd8b439638bf12dd682f60be7ef1d0e0d98f08b7bca77a1a2b869ae466189d2acdabe3",
	"G",

	/* ecdsa_secp256r1_sha256_test.json - 453 */
	"ecdsa_secp256r1_sha256_test.json - 453",
	"043cf03d614d8939cfd499a07873fac281618f06b8ff87e8015c3f49726500493584fa174d791c72bf2ce3880a8960dd2a7c7a1338a82f85a9e59cdbde80000000",
	"4d657373616765",
	"e56c6ea2d1b017091c44d8b6cb62b9f460e3ce9aed5e5fd41e8added97c56c04a308ec31f281e955be20b457e463440b4fcf2b80258078207fc1378180f89b55",
	"G",

	/* ecdsa_secp256r1_sha256_test.json - 454 */
	"ecdsa_secp256r1_sha256_test.json - 454",
	"043cf03d614d8939cfd499a07873fac281618f06b8ff87e8015c3f4972650049357b05e8b186e38d41d31c77f5769f22d58385ecc857d07a561a6324217fffffff",
	"4d657373616765",
	"1158a08d291500b4cabed3346d891eee57c176356a2624fb011f8fbbf3466830228a8c486a736006e082325b85290c5bc91f378b75d487dda46798c18f285519",
	"G",

	/* ecdsa_secp256r1_sha256_test.json - 455 */
	"ecdsa_secp256r1_sha256_test.json - 455",
	"043cf03d614d8939cfd499a07873fac281618f06b8ff87e8015c3f4972650049357b05e8b186e38d41d31c77f5769f22d58385ecc857d07a561a6324217fffffff",
	"4d657373616765",
	"b1db9289649f59410ea36b0c0fc8d6aa2687b29176939dd23e0dde56d309fa9d3e1535e4280559015b0dbd987366dcf43a6d1af5c23c7d584e1c3f48a1251336",
	"G",

	/* ecdsa_secp256r1_sha256_test.json - 456 */
	"ecdsa_secp256r1_sha256_test.json - 456",
	"043cf03d614d8939cfd499a07873fac281618f06b8ff87e8015c3f4972650049357b05e8b186e38d41d31c77f5769f22d58385ecc857d07a561a6324217fffffff",
	"4d657373616765",
	"b7b16e762286cb96446aa8d4e6e7578b0a341a79f2dd1a220ac6f0ca4e24ed86ddc60a700a139b04661c547d07bbb0721780146df799ccf55e55234ecb8f12bc",
	"G",

	/* ecdsa_secp256r1_sha256_test.json - 457 */
	"ecdsa_secp256r1_sha256_test.json - 457",
	"042829c31faa2e400e344ed94bca3fcd0545956ebcfe8ad0f6dfa5ff8effffffffa01aafaf000e52585855afa7676ade284113099052df57e7eb3bd37ebeb9222e",
	"4d657373616765",
	"d82a7c2717261187c8e00d8df963ff35d796edad36bc6e6bd1c91c670d9105b43dcabddaf8fcaa61f4603e7cbac0f3c0351ecd5988efb23f680d07debd139929",
	"G",

	/* ecdsa_secp256r1_sha256_test.json - 458 */
	"ecdsa_secp256r1_sha256_test.json - 458",
	"042829c31faa2e400e344ed94bca3fcd0545956ebcfe8ad0f6dfa5ff8effffffffa01aafaf000e52585855afa7676ade284113099052df57e7eb3bd37ebeb9222e",
	"4d657373616765",
	"5eb9c8845de68eb13d5befe719f462d77787802baff30ce96a5cba063254af782c026ae9be2e2a5e7ca0ff9bbd92fb6e44972186228ee9a62b87ddbe2ef66fb5",
	"G",

	/* ecdsa_secp256r1_sha256_test.json - 459 */
	"ecdsa_secp256r1_sha256_test.json - 459",
	"042829c31faa2e400e344ed94bca3fcd0545956ebcfe8ad0f6dfa5ff8effffffffa01aafaf000e52585855afa7676ade284113099052df57e7eb3bd37ebeb9222e",
	"4d657373616765",
	"96843dd03c22abd2f3b782b170239f90f277921becc117d0404a8e4e36230c28f2be378f526f74a543f67165976de9ed9a31214eb4d7e6db19e1ede123dd991d",
	"G",

	/* ecdsa_secp256r1_sha256_test.json - 460 */
	"ecdsa_secp256r1_sha256_test.json - 460",
	"04fffffff948081e6a0458dd8f9e738f2665ff9059ad6aac0708318c4ca9a7a4f55a8abcba2dda8474311ee54149b973cae0c0fb89557ad0bf78e6529a1663bd73",
	"4d657373616765",
	"766456dce1857c906f9996af729339464d27e9d98edc2d0e3b760297067421f6402385ecadae0d8081dccaf5d19037ec4e55376eced699e93646bfbbf19d0b41",
	"G",

	/* ecdsa_secp256r1_sha256_test.json - 461 */
	"ecdsa_secp256r1_sha256_test.json - 461",
	"04fffffff948081e6a0458dd8f9e738f2665ff9059ad6aac0708318c4ca9a7a4f55a8abcba2dda8474311ee54149b973cae0c0fb89557ad0bf78e6529a1663bd73",
	"4d657373616765",
	"c605c4b2edeab20419e6518a11b2dbc2b97ed8b07cced0b19c34f777de7b9fd9edf0f612c5f46e03c719647bc8af1b29b2cde2eda700fb1cff5e159d47326dba",
	"G",

	/* ecdsa_secp256r1_sha256_test.json - 462 */
	"ecdsa_secp256r1_sha256_test.json - 462",
	"04fffffff948081e6a0458dd8f9e738f2665ff9059ad6aac0708318c4ca9a7a4f55a8abcba2dda8474311ee54149b973cae0c0fb89557ad0bf78e6529a1663bd73",
	"4d657373616765",
	"d48b68e6cabfe03cf6141c9ac54141f210e64485d9929ad7b732bfe3b7eb8a84feedae50c61bd00e19dc26f9b7e2265e4508c389109ad2f208f0772315b6c941",
	"G",

	/* ecdsa_secp256r1_sha256_test.json - 463 */
	"ecdsa_secp256r1_sha256_test.json - 463",
	"0400000003fa15f963949d5f03a6f5c7f86f9e0015eeb23aebbff1173937ba748e1099872070e8e87c555fa13659cca5d7fadcfcb0023ea889548ca48af2ba7e71",
	"4d657373616765",
	"b7c81457d4aeb6aa65957098569f0479710ad7f6595d5874c35a93d12a5dd4c7b7961a0b652878c2d568069a432ca18a1a9199f2ca574dad4b9e3a05c0a1cdb3",
	"G",

	/* ecdsa_secp256r1_sha256_test.json - 464 */
	"ecdsa_secp256r1_sha256_test.json - 464",
	"0400000003fa15f963949d5f03a6f5c7f86f9e0015eeb23aebbff1173937ba748e1099872070e8e87c555fa13659cca5d7fadcfcb0023ea889548ca48af2ba7e71",
	"4d657373616765",
	"6b01332ddb6edfa9a30a1321d5858e1ee3cf97e263e669f8de5e9652e76ff3f75939545fced457309a6a04ace2bd0f70139c8f7d86b02cb1cc58f9e69e96cd5a",
	"G",

	/* ecdsa_secp256r1_sha256_test.json - 465 */
	"ecdsa_secp256r1_sha256_test.json - 465",
	"0400000003fa15f963949d5f03a6f5c7f86f9e0015eeb23aebbff1173937ba748e1099872070e8e87c555fa13659cca5d7fadcfcb0023ea889548ca48af2ba7e71",
	"4d657373616765",
	"efdb884720eaeadc349f9fc356b6c0344101cd2fd8436b7d0e6a4fb93f106361f24bee6ad5dc05f7613975473aadf3aacba9e77de7d69b6ce48cb60d8113385d",
	"G",

	/* ecdsa_secp256r1_sha256_test.json - 466 */
	"ecdsa_secp256r1_sha256_test.json - 466",
	"04bcbb2914c79f045eaa6ecbbc612816b3be5d2d6796707d8125e9f851c18af015000000001352bb4a0fa2ea4cceb9ab63dd684ade5a1127bcf300a698a7193bc2",
	"4d657373616765",
	"31230428405560dcb88fb5a646836aea9b23a23dd973dcbe8014c87b8b20eb070f9344d6e812ce166646747694a41b0aaf97374e19f3c5fb8bd7ae3d9bd0beff",
	"G",

	/* ecdsa_secp256r1_sha256_test.json - 467 */
	"ecdsa_secp256r1_sha256_test.json - 467",
	"04bcbb2914c79f045eaa6ecbbc612816b3be5d2d6796707d8125e9f851c18af015000000001352bb4a0fa2ea4cceb9ab63dd684ade5a1127bcf300a698a7193bc2",
	"4d657373616765",
	"caa797da65b320ab0d5c470cda0b36b294359c7db9841d679174db34c4855743cf543a62f23e212745391aaf7505f345123d2685ee3b941d3de6d9b36242e5a0",
	"G",

	/* ecdsa_secp256r1_sha256_test.json - 468 */
	"ecdsa_secp256r1_sha256_test.json - 468",
	"04bcbb2914c79f045eaa6ecbbc612816b3be5d2d6796707d8125e9f851c18af015000000001352bb4a0fa2ea4cceb9ab63dd684ade5a1127bcf300a698a7193bc2",
	"4d657373616765",
	"7e5f0ab5d900d3d3d7867657e5d6d36519bc54084536e7d21c336ed8001859459450c07f201faec94b82dfb322e5ac676688294aad35aa72e727ff0b19b646aa",
	"G",

	/* ecdsa_secp256r1_sha256_test.json - 469 */
	"ecdsa_secp256r1_sha256_test.json - 469",
	"04bcbb2914c79f045eaa6ecbbc612816b3be5d2d6796707d8125e9f851c18af015fffffffeecad44b6f05d15b33146549c2297b522a5eed8430cff596758e6c43d",
	"4d657373616765",
	"d7d70c581ae9e3f66dc6a480bf037ae23f8a1e4a2136fe4b03aa69f0ca25b35689c460f8a5a5c2bbba962c8a3ee833a413e85658e62a59e2af41d9127cc47224",
	"G",

	/* ecdsa_secp256r1_sha256_test.json - 470 */
	"ecdsa_secp256r1_sha256_test.json - 470",
	"04bcbb2914c79f045eaa6ecbbc612816b3be5d2d6796707d8125e9f851c18af015fffffffeecad44b6f05d15b33146549c2297b522a5eed8430cff596758e6c43d",
	"4d657373616765",
	"341c1b9ff3c83dd5e0dfa0bf68bcdf4bb7aa20c625975e5eeee34bb396266b3472b69f061b750fd5121b22b11366fad549c634e77765a017902a67099e0a4469",
	"G",

	/* ecdsa_secp256r1_sha256_test.json - 471 */
	"ecdsa_secp256r1_sha256_test.json - 471",
	"04bcbb2914c79f045eaa6ecbbc612816b3be5d2d6796707d8125e9f851c18af015fffffffeecad44b6f05d15b33146549c2297b522a5eed8430cff596758e6c43d",
	"4d657373616765",
	"70bebe684cdcb5ca72a42f0d873879359bd1781a591809947628d313a3814f67aec03aca8f5587a4d535fa31027bbe9cc0e464b1c3577f4c2dcde6b2094798a9",
	"G",

	/* ecdsa_secp256r1_sha256_test.json - 475 */
	"ecdsa_secp256r1_sha256_test.json - 475",
	"04264d796a0dab9b376d34eea6fe297dde1c7b73e53944bc96c8f1e8a6850bb6c9cf5308020eed460c649ddae61d4ef8bb79958113f106befaf4f18876d12a5e64",
	"68656c6c6f2c20776f726c64",
	"0000000000000000000000000000000000000000000000000000000000000005ffffffff00000000ffffffffffffffffbce6faada7179e84f3b9cac2fc63254e",
	"G",

	/* ecdsa_secp256r1_sha256_test.json - 476 */
	"ecdsa_secp256r1_sha256_test.json - 476",
	"04add76677e54a92e79bbee36a70e1754838273ec4b39295e4018a587290a7fc73f240d625642c943e610d80d953c5c6b8a12760a624ba3b90a0b7902755e1ae79",
	"68656c6c6f2c20776f726c64",
	"0000000000000000000000000000000000000000000000000000000000000006ffffffff00000000ffffffffffffffffbce6faada7179e84f3b9cac2fc63254e",
	"F",

	/* ecdsa_secp256r1_sha256_test.json - 477 */
	"ecdsa_secp256r1_sha256_test.json - 477",
	"04264d796a0dab9b376d34eea6fe297dde1c7b73e53944bc96c8f1e8a6850bb6c9cf5308020eed460c649ddae61d4ef8bb79958113f106befaf4f18876d12a5e64",
	"68656c6c6f2c20776f726c64",
	"ffffffff00000000ffffffffffffffffbce6faada7179e84f3b9cac2fc632556ffffffff00000000ffffffffffffffffbce6faada7179e84f3b9cac2fc63254e",
	"F",

	/* ecdsa_secp256r1_sha256_test.json - 478 */
	"ecdsa_secp256r1_sha256_test.json - 478",
	"04e7e49dd82812432744fefe723f7f69663214ad1b85c02b2650b4ca0354743a325223c51c415f457aec69cb019bbe3d27585b38f8b79c39dfea6c27c2f0d8146a",
	"68656c6c6f2c20776f726c64",
	"ffffffff00000000ffffffffffffffffbce6faada7179e84f3b9cac2fc63254effffffff00000000ffffffffffffffffbce6faada7179e84f3b9cac2fc63254e",
	"F",

	/* ecdsa_secp256r1_sha256_test.json - 479 */
	"ecdsa_secp256r1_sha256_test.json - 479",
	"04ce24c99032d52ac6ead23c0ae3ec68ef41e51a281fd457808c83136d7dcce90e8f7a154b551e9f39c59279357aa491b2a62bdebc2bb78613883fc72936c057e0",
	"68656c6c6f2c20776f726c64",
	"0000000000000000000000000000000000000000000000000000000000000003ffffffff00000000ffffffffffffffffbce6faada7179e84f3b9cac2fc63254e",
	"G",

	/* ecdsa_secp256r1_sha256_test.json - 480 */
	"ecdsa_secp256r1_sha256_test.json - 480",
	"04c981c75ddfd3910387eb147098fe5658c43aaaa34c681cd6d514b6ad5b6baa6d14fbddb53a6e6db18e90602bc60f2e736d625765f7f2cca4be76f4eeccf12c18",
	"68656c6c6f2c20776f726c64",
	"0000000000000000000000000000000000000000000000000000000000000004ffffffff00000000ffffffffffffffffbce6faada7179e84f3b9cac2fc63254e",
	"F",

	/* ecdsa_secp256r1_sha256_test.json - 481 */
	"ecdsa_secp256r1_sha256_test.json - 481",
	"040ec505bc19b14a43e05678cccf07a443d3e871a2e19b68a4da91859a0650f32477300e4f64e9982d94dff5d294428bb37cc9be66117cae9c389d2d495f68b987",
	"68656c6c6f2c20776f726c64",
	"000000000000000000000000000000004319055358e8617b0c46353d039cdab3ffffffff00000000ffffffffffffffffbce6faada7179e84f3b9cac2fc63254e",
	"F",

	/* ecdsa_secp256r1_sha256_test.json - 482 */
	"ecdsa_secp256r1_sha256_test.json - 482",
	"04d42ce21e730f3d2a84e949828574b4dceeb77d4f89556735f34fba03028ee3ed32daf8bfd3f0a7a0821170840f4e032056722386b35d9bdd4f4f450696f4fb52",
	"68656c6c6f2c20776f726c64",
	"00000000ffffffff00000000000000004319055258e8617b0c46353d039cdab4ffffffff00000000ffffffffffffffffbce6faada7179e84f3b9cac2fc63254e",
	"F",

	NULL
};

static void
test_ecdsa_p256_verify(void)
{
	printf("Test ECDSA/P-256 verify: ");
	fflush(stdout);

	for (int i = 0; KAT_ECDSA_P256_SHA256_VERIFY[i] != NULL; i += 5) {
		const char *tid = KAT_ECDSA_P256_SHA256_VERIFY[i];
		uint8_t pub[65], msg[20], sig[82];
		size_t pub_len, msg_len, sig_len;
		int good;
		pub_len = hextobin(pub, sizeof pub,
			KAT_ECDSA_P256_SHA256_VERIFY[i + 1]);
		msg_len = hextobin(msg, sizeof msg,
			KAT_ECDSA_P256_SHA256_VERIFY[i + 2]);
		sig_len = hextobin(sig, sizeof sig,
			KAT_ECDSA_P256_SHA256_VERIFY[i + 3]);
		good = KAT_ECDSA_P256_SHA256_VERIFY[i + 4][0] == 'G';
		uint8_t hv[32];
		sha256_context sc;
		sha256_init(&sc);
		sha256_update(&sc, msg, msg_len);
		sha256_out(&sc, hv);

		if (tv_ecdsa_p256_verify(
			sig, sig_len, pub, pub_len, hv, 32) != good)
		{
			if (good) {
				fprintf(stderr,
					"ERR: %s: verify failed\n", tid);
			} else {
				fprintf(stderr,
					"ERR: %s: verify should have failed\n",
					tid);
			}
			exit(EXIT_FAILURE);
		}

		if (good) {
			hv[0] ^= 0x01;
			if (tv_ecdsa_p256_verify(
				sig, sig_len, pub, pub_len, hv, 32))
			{
				fprintf(stderr,
					"ERR: %s: verify should have"
					" failed (2)\n", tid);
				exit(EXIT_FAILURE);
			}
		}

		printf(".");
		fflush(stdout);
	}

	printf(" done.\n");
	fflush(stdout);
}

#if defined __aarch64__ && (defined __GNUC__ || defined __clang__) \
	|| defined __x86_64__ || defined _M_X64 \
	|| defined __i386__ || defined _M_IX86 \
	|| defined __riscv && defined __riscv_xlen && __riscv_xlen >= 64

/* On Aarch64 (with GCC or Clang), RISC-V (64-bit), and x86, we have an
   optional benchmark code. This entails reading performance counters,
   which is not generally feasible unless some OS-specific action was
   taken. On x86 systems running Linux, performance counter access can
   be enabled with a simple command (as root); on 64-bit ARM and RISC-V,
   a custom kernel module is needed. For details, see:
       https://github.com/pornin/cycle-counter
   If the performance counters are not accessible, the code below should
   still compile, but the process will crash if running the tests with
   the '-s' option. */

#define SPEED_BENCH_SUPPORTED   1

#if defined __x86_64__ || defined _M_X64 || defined __i386__ || defined _M_IX86
/* On x86, we read the cycle counter (NOT the timestamp counter, which does
   not follow CPU frequency scaling). */

#include <immintrin.h>
#ifdef _MSC_VER
/* On Windows, the intrinsic is called __readpmc(), not __rdpmc(). But it
   will usually imply a crash, since Windows does no enable access to the
   performance counters. */
#ifndef __rdpmc
#define __rdpmc   __readpmc
#endif
#else
#include <x86intrin.h>
#endif

#if defined __GNUC__ || defined __clang__
__attribute__((target("sse2")))
#endif
static inline uint64_t
core_cycles(void)
{
	_mm_lfence();
	return __rdpmc(0x40000001);
}

#elif defined __aarch64__ && (defined __GNUC__ || defined __clang__)

static inline uint64_t
core_cycles(void)
{
	uint64_t x;
	__asm__ __volatile__ ("dsb sy\n\tmrs %0, pmccntr_el0" : "=r" (x) : : );
	return x;
}

#elif defined __riscv && defined __riscv_xlen && __riscv_xlen >= 64

static inline uint64_t
core_cycles(void)
{
	uint64_t x;
	__asm__ __volatile__ ("rdcycle %0" : "=r" (x));
	return x;
}

#else
#error Architecture not supported (cycle counter)
#endif

/* Custom sort routine (bubble sort, inefficient at large sizes). */
static void
sort_tt(uint64_t *tt, size_t len)
{
	for (size_t i = 1; i < len; i ++) {
		for (size_t j = 0; (j + i) < len; j ++) {
			if (tt[j] > tt[j + 1]) {
				uint64_t x = tt[j];
				tt[j] = tt[j + 1];
				tt[j + 1] = x;
			}
		}
	}
}

/* Each triplet of values is:
     public key (65 bytes)
     hashed message (32 bytes)
     signature (64 bytes) */
static const char *const KAT_ECDSA_P256_BENCH[] = {
	"04e1cb71762d85324a3791f7de449dde8a6e7344ad03c510ce2c749a6cebc939815bd7d39abdaadd14470664ce05e23680db07a5389d4a0ce760ac134efb5b0571",
	"529501d8b3e070119a24097facfe58996ff038cfd2ca58e23dcfda8080c7dac8",
	"10033a383fa7271e82c9a4357c2cf33b9ac0f4241c2e05b0467ac97eb5b59558fc6b6642e658975ec386d21b6fffb669a14f180f69cbff9628defb7b6cda4d19",
	"04e997bb92bee53bc65e9356b6a17a7671cbe462a7fe0ac93574d90e290688739eb54dcfb48b238ce7c72fd667d018ccfac4afa6ae1daf33620b70c0fb8c44cbf3",
	"5b5819e0cfd8a46d6c831938dbb9646201366f666245f5957268817b0b1531de",
	"6daf8aca850b6fee9949aac34ad215325a407b21ff48c36d73d14c1078c70724ed145a928774e483ff3d5a9a0bc30bc1d4f258be72dba2681e8579a95807ecbe",
	"0477f6f79ff477cda45b39c76dcfd53d3d8b619ec57d19f9aee996ec8e43ffcff70a3c8202055fbd63b5d645d587a91ea36c74e027e92804034f82f368c30219e6",
	"7b4894040a854820f132a75149268d1ac2f02b99fe4d55c34933b69560189407",
	"31f28ab9d4925ccbca44d6efe60cb2206ac3abdf529ff750dad45428020a556fb05ec8f4c772a3a3e2f1cc3ceef7be65edf346d0c884bf64631553e63f37a2f9",
	"04ac7d7a3f47b83c7f37241c3b27ecece70c1f3f102979eee3263fc0a9ba2e5ea37753f349812ebc86ee3a846abfd3fea579e0ec212c2a0bfc69fc44aec6f893b2",
	"75215bef44e9fe9ffa0e4de3e0942d3e0e83178c551dfa58f907ba3fb277248f",
	"295486ed9b6ad976f3d219ea938bc998b3917a6b88f7a3f3f5bd9be6da47bd63e774c3330a85c52fce504fd4caca5b834b88a904e6c8694d8ffc9ad2a1ac962d",
	"04a31abad45e133d941aa2d405e6174a0c3cccb5be39ac3630e5730eba6f15f511a5eb70458f90a7f1930eabc55e9093a367626c66655bceeac8bdc6435351c9fc",
	"72962ff1bd5d446d6096ac4f55ac78bb2aadff3fb8df76d1a91c622d2cec5d8c",
	"6ab4d48955e639c9b84676a238378d39685c99beeb95ae969bc18a0630ea6aebdf747faacb0adf742931051064d380b1092d1facdfc30b0d4bdef45aef525fc6",
	"047ac207229d7b231993e3c1294d04b02e76c2003d3334b75b09398376ac4821084d6be65b336bc095170cfd16bacc7ce34d8bf4b3cdd054c848a640c9563adfd7",
	"90ed2e902e1d4c0c319ae120b8c949cdf822a6d97aa47736cc6eff96f4a2d950",
	"c7377f325734de2692b144c51997463aeec81c0402210c945dc51ea2abad8e72c769782fece83261dd5e48191538d1ec7ad20f38b71d84a4946c3326953c60c2",
	"04faefa458e7f8c213df2110a58e40e2099a9e03093a63c4091c1b242a49afca41b76fb35d8a18137bc5b7ca3527e86b5fb9a1b86281b1c16dce159bd4cb800787",
	"f8de84a61d987aac8d6bd6cfdbac49a39d6dbf8ab43180adb4a3f8bfc7deddb8",
	"5135969e7f33bdff879540ec38f73c159017ae6d40f5d5503458eecbabd3fa0a4f6da80bc124b4589dc5d0a337468ffaaa9c726514bc795749b24d2a66e36f24",
	"042c61753636da7dd38b9ce52f5ee8aac29f161e9df583d6cebb0bc882ca8ed8cf25a02b9478ff3de977deb2e65d372bc3452794fcb52261046207329c29ee14a2",
	"27af100fb077604f961fe2e6aa507604fae04a2d028c509509c01595631c74a8",
	"1991ea5394382393044436748da84434dd7128d5a71001282d22aa24627f1bfb1d321097002d8b1b6ad8953ad5bbf40cb8a14298525ddae6823557e33697572f",
	"04e22856b322777a4f9c961b650b0257e27bfe457f2a4533643edb27ddd421efb2a4d77f1d6fe0c0dbc130a613f594906108d8d858a04238bd676b93ee97cf16ef",
	"89b4712d91005a368547fad11dd4bed38a77e208a5fc77f17344a51608d972cc",
	"93ae207d1be9fc816f1095c56a17ef1e1fbae9e4c663dd7e80316f4d72e10fec59555561128af4e79046e37f1f04597e7af180e58cb341bd0b2fd87256cc2ab0",
	"0495323635980f544fc20e7aaa7349e79e0408ba142080a31b08100043c2498239713c486caf987765a30e14441827ba6979f708db1ea2e407cec11b124cd90949",
	"a3d8c17ad07feef9cdb072b04db2470ac7fab06a50c6fc8c72cd3f0696c2ff95",
	"cf1b2df21ab4b184bb873facd0216b104984cd08e89d74d17b08bc961ebf96cefb24b0b3d429e729049c1f004f114fab83382773e5b850f81362b2641d70e276",
	"0427e5eec3694322c041c85a822f79e608d0610fcb35d69b5784ace5537c491762b83b26812ac090d04b258e835b2f6df603eeeb83853bc40d0353c857f6896a6d",
	"0f65092bc82291e54f365cd4d1d6642e0b1170c541046b2db23d2ff719296667",
	"8ebd628d4c94c6c1c567caaa9dec3c2d04e9e99228c83e5169636c7b99da1d8f62a52dd124e4ae2a4416ce5a0f59257a486f532ce5cd195bc14d63e124e44c4f",
	"04372e0b1eb24df216d05389b118fb78ca1cb8ffdd59c02577e4ff07503afe3fa07fd8bd47b8b2748792990532de4f8d4226cfdc92dd9cd49c9d0c3c9064fc8260",
	"537ff8b85326bd84951ba1843a025cad7206bbd9769dd5a2b8733a6c5b30046f",
	"494bc9f8f09bd702193f97b727b634db83c1c2ea0bec56ca290d7f4ae15929d5048f22f807e33cf0b369b354892c66eaa384bbb8c43a29e1a0302f2271d62c12",
	"04b98f714066fe92d6b3c946ec6451518b014cec20bd63f11de7e9a21b460ec2bf14c49d320b597c69a68120c0aef927f273629a463e65a81621bf72c2687a1cde",
	"ec3ad3bc39db263d931339490644c03a41ad201dfe2de0a4b8bc5561c53b71b6",
	"adbe262ccc4a2e99cc18187df9671ef929ffaa1be358c6dd4f50fd0e620db48efe0d5a06d56a61e9754e0fc38e0e69025b2af7f3d6c4d9003507acffde23c63d",
	"045338e6de186164909870abe0b8fb03755e06a6d18ad439fde84635ec0851542ab1c7c47dc38ae2ac620c0a25062b7d390c49699c52ec6f7b43c13264a8c94811",
	"2abd6b8373ad2d68c0b9b1e49797cf99180d8b6e07a5f01484fd594215dc30c9",
	"66a1cb72ddf903c5c1bee893da9639d06a15f3c536218a770698c0d04c576df0d060cc99f3c02f796cf1c1e4d4f558f78e00089425c5aadf8ab3259b3e271f86",
	"04001c9821773cca2ecabea9b7ffe8c27430915f2ab06d67193d6a689b1153480ac6996fd94054537a95e1aad6f493c1f2daf780468d84dcad8364e113cb326e8d",
	"d3afe65a5c4850f04399d0c81298783fbbe3e43a304575292bc21781c4f92e31",
	"9bc38da5d9f7811e46033a0ca9068dc8f84d1f476c820719020a3031eba9463303130bd2a72d38d82c2021485471283d47c8f052a14a86e83f028eebe267e16d",
	"04f95b5bb160786b6a8479388287625d9a647422892f8b003d4108225ed9edca82de2254892246a3a838ea732a10d9dde69a8e46f88c0fa2953bfc3fbe25dc56ec",
	"735a1bf37b2cc73c3c1a62cbd109aabdbbc6dd4a66517b7dbb3fc7dda8d5ec3d",
	"d70fe974273cae9190ea80792c735921166a57bb9f7dc6412fadc85b602191fdaed8f8a20f6712fd419488016eb7cc7c495dcb9e928fc5784cda409fcc3f1c8c",
	"0430a1d1e48cbcf06f0ca214f0632904566afc0434cf1026958380e3a214aac112dd5ed17830bd4ad6c379d8137be076b489f9b363180c68aa18a4b28db1906a42",
	"818dbe88d94cb61e517ea196ea9c6dfa258f40bd1b2fc546b40985fd048cf686",
	"c9ccf23da7d3661d98da57ad04253cf85e343a91f5e69dad2076c4ca7c0a60ac9df32aa1a788081c43cf81f4f99ac1e5dbbeb5b2e9de4c62d3ff6f1cafac6f93",
	"04ebeafdeef2d535a8b7ff003c204a056ee6e3c6ef97fce72330d4410617b8b911b669ff9a3ed1bdcdd0eab87a8c3cfca69411bd6a5c750caa404a5fcb3c1f3532",
	"b5afb10bad9ff7363717c45106be878d3b2951ac8b969f676972bb22ee370254",
	"306098d38613bbfbd45f9ea213805372f1981c4e44d8cf1e41686c378933e5d699f21219f1200294c6190aa6a141e9279206162ca43cb5c3eee574dd98fb49b6",
	"041f48d2b0e73aa73444958d328523460d7c87ad5d4e35157fba136c0632e1c97e90bfd0577eedd40af1f67368be331e4884d18640b29cfcf9a90d591ae342aabe",
	"4001ce32fbd232360b5a40802482a678951ecc67571a956276434ef66806456e",
	"9a2a09d5458f1d394b48f6975aa29389e5d89a6fe1be5f80dd8791bc7ef1795c65421bab4d7f84369dee4c88cc99f3832567234a828e0ae6010b2c4ba68e5e4c",
	"042d63128756a1458f29f1eba1516cab7fd126938d9ac70cb75c99df1768f3ca2beaa7945f5dc1df3b0116b78692bc48646bc5808fefe51f3f2369312f35576fac",
	"52e9ecda82f61fac70e0447ec9210a3d9af5174bb1ac7b9527ba6fe569ebe2cc",
	"31498d3ca67e940d23e674f4857cb0a07162adf9dc0115e2b981a7e98952671b8d1f22c9a9b80bd6d2a05798412529dbf831368f8257be54eb4b86db877ffa6a",
};

static void
bench_ecdsa_p256_verify(void)
{
#define NUM_KAT   ((sizeof(KAT_ECDSA_P256_BENCH) / sizeof(const char *)) / 3)
	uint8_t pub[NUM_KAT][65], mhv[NUM_KAT][32], sig[NUM_KAT][64];
	for (size_t i = 0; i < NUM_KAT; i ++) {
		HEXTOBIN(pub[i], KAT_ECDSA_P256_BENCH[3 * i + 0]);
		HEXTOBIN(mhv[i], KAT_ECDSA_P256_BENCH[3 * i + 1]);
		HEXTOBIN(sig[i], KAT_ECDSA_P256_BENCH[3 * i + 2]);
	}

	uint64_t tt[9];
	for (int i = 0; i < 20; i ++) {
		uint64_t begin = core_cycles();
		for (size_t j = 0; j < NUM_KAT; j ++) {
			if (!tv_ecdsa_p256_verify(sig[j], 64,
				pub[j], 65, mhv[j], 32))
			{
				fprintf(stderr, "ERR verify %zu\n", j);
				exit(EXIT_FAILURE);
			}
		}
		uint64_t end = core_cycles();
		if (i >= 11) {
			tt[i - 11] = end - begin;
		}
	}

	sort_tt(tt, 9);
	printf("speed ECDSA/P-256: %.2f  (%.2f .. %.2f)  (cycles per verify)\n",
		(double)tt[4] / NUM_KAT,
		(double)tt[0] / NUM_KAT,
		(double)tt[8] / NUM_KAT);
#undef NUM_KAT
}
#endif

int
main(int argc, char *argv[])
{
	(void)argc;
	(void)argv;
	test_sha256();
#if defined TV_ECDSA_P256_TEST
	test_gf_coordinates();
	test_gf_scalars();
	test_p256_basic();
#endif
	test_ecdsa_p256_verify();

#ifdef SPEED_BENCH_SUPPORTED
	if (argc > 1 && strcmp(argv[1], "-s") == 0) {
#if defined __linux || defined __linux__
		if (argc > 2) {
			/* Try to bind to a specific CPU/core, it makes
			   measurements more reliable. */
			cpu_set_t cs;
			int cpu = atoi(argv[2]);
			CPU_ZERO(&cs);
			CPU_SET(cpu, &cs);
			if (sched_setaffinity(getpid(), sizeof cs, &cs) != 0) {
				perror("sched_setaffinity");
			}
		}
#endif
		bench_ecdsa_p256_verify();
	}
#else
	(void)argc;
	(void)argv;
#endif
	return 0;
}
