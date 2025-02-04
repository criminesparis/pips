#
# $Id: config.makefile 12279 2005-12-23 14:29:06Z coelho $
#

SOURCES =	linear.tex

all: linear.ps

linear.dvi: linear.tex;	frlatex $< ; frlatex $<;
linear.ps: linear.dvi; dvips $< -o

clean: lclean
lclean:; $(RM) linear.dvi linear.ps
