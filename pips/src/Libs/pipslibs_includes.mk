# it generates many warnings, with advices to use AM_CPPFLAGS instead...
# however the compilation fails if the advice is followed...
INCLUDES=\
	`cat ../pips_includes` \
	-I../../Documentation/pipsmake \
	-I../../Documentation/newgen \
	-I$(top_srcdir)/src/Documentation/constants \
	$(NEWGENLIBS_CFLAGS) $(LINEARLIBS_CFLAGS)
