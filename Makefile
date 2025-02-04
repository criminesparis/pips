# $Id: Makefile 23198 2016-10-14 14:35:33Z coelho $
# simplistic forward makefile
# useful targets include: tags clean build unbuild rebuild...

default: compile

# can generate a tar
VERSION=0.1

# testing simple sanity check
.PHONY: sanity_check
sanity_check:
	@[ ! "$$PIPS_ROOT" ] || { echo "remove PIPS_ROOT to compile" ;  exit 1 ; }
	@for dir in newgen linear pips ; do \
	  config="$$dir/makes/config.mk" ; \
	  [ -f "$$config" ] || { echo "missing file: $$config" ; exit 1 ; } \
	done

.DEFAULT: .sanity_check
	$(MAKE) -C newgen $@
	$(MAKE) -C linear $@
	$(MAKE) -C pips $@

