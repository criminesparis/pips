# $Id: Makefile 1655 2016-10-27 15:21:14Z ancourt $

LC3.inc	= ../../include
LC3.lib = ../../lib/LINUX_x86_64_LL

.PHONY: all
all: smith sc_proj sc_cmp

# testing...
CC		= gcc -std=c99
CFLAGS		= -O0 -Wall
CPPFLAGS	= -I $(LC3.inc) -DLINEAR_VALUE_IS_LONGLONG
LDFLAGS		= -L $(LC3.lib)

%: %.c
	$(CC) $(CPPFLAGS) $(CFLAGS) $< $(LDFLAGS) -o $@

F.c	= $(wildcard *.c)
F.o	= $(F.c:%.c=%.o)
F.exe	= $(F.c:%.c=%)

MX.lib	= -lmatrix -larithmetique
SC.lib	= -lsc -lcontrainte -lvecteur -larithmetique
PO.lib	= -lpolyedre -lsg
UN.lib = -lunion $(PO.lib) $(SC.lib)

smith: LDFLAGS += $(MX.lib)
feasability: LDFLAGS += $(SC.lib)
sc_proj: LDFLAGS += $(SC.lib)
sc_minmax: LDFLAGS += $(SC.lib)
sc_cmp: LDFLAGS += $(UN.lib)
#sc_env: LDFLAGS += $(PO.lib) $(SC.lib) $(MX.lib)

clean:
	$(RM) *~ $(F.o) $(F.exe)
