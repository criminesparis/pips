ROOT = ../../../../../..

# files
F.c	= SIMD.c patterns.c
F.h	= 3dnow.h SIMD_types.h avx.h neon.h sse.h
F.mk	= Makefile.sse Makefile.3dn Makefile.avx Makefile.neon
DERIVED_HEADERS	= patterns.h

INSTALL_RTM	= $(F.c) $(F.h) $(F.mk) $(DERIVED_HEADERS)

%.h: %.c
	$(CPROTO) $< > $@

PROJECT	= pips
include $(ROOT)/makes/main.mk

# must be consistent with pypsconfig
RTM.d := $(SHR.d)/pyps/sac
