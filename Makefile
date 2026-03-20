# Add '-DTV_ECDSA_P256_TEST' to enable some extra functions that allow unit
# test of internal functionalities; this of course enlarges the binary, and
# it is not necessary for normal operations.
CC = cc
CFLAGS = -W -Wextra -O # -DTV_ECDSA_P256_TEST
LD = cc
LDFLAGS =

default: test_ecdsa-p256-verify_stupid

test_ecdsa-p256-verify_stupid: ecdsa-p256-verify-tests.o ecdsa-p256-verify_stupid.o
	$(LD) $(LDFLAGS) -o test_ecdsa-p256-verify_stupid ecdsa-p256-verify-tests.o ecdsa-p256-verify_stupid.o

ecdsa-p256-verify_stupid.o: ecdsa-p256-verify_stupid.S
	$(CC) $(CFLAGS) -c -o ecdsa-p256-verify_stupid.o ecdsa-p256-verify_stupid.S

ecdsa-p256-verify-tests.o: ecdsa-p256-verify-tests.c ecdsa-p256-verify.h
	$(CC) $(CFLAGS) -c -o ecdsa-p256-verify-tests.o ecdsa-p256-verify-tests.c

clean:
	-rm -f test_ecdsa-p256-verify_stupid ecdsa-p256-verify-tests.o ecdsa-p256-verify_stupid.o
