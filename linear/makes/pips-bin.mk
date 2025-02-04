# $Id: pips-bin.mk 1231 2016-03-02 08:16:46Z coelho $
#
# Copyright 1989-2016 MINES ParisTech
#
# This file is part of PIPS.
#
# PIPS is free software: you can redistribute it and/or modify it
# under the terms of the GNU Lesser General Public License as published by
# the Free Software Foundation, either version 3 of the License, or
# any later version.
#
# PIPS is distributed in the hope that it will be useful, but WITHOUT ANY
# WARRANTY; without even the implied warranty of MERCHANTABILITY or
# FITNESS FOR A PARTICULAR PURPOSE.
#
# See the GNU Lesser General Public License for more details.
#
# You should have received a copy of the GNU Lesser General Public License
# along with PIPS.  If not, see <http://www.gnu.org/licenses/>.
#

# build pips executables on request
main.dir =	./$(ARCH)

$(ARCH)/pips:
	$(MAKE) $(ARCH)
	$(LINK) $@ $(main.dir)/$(PIPS_MAIN) -lpips \
		-Wl,--start-group $(addprefix -l,$(pips.libs)) -Wl,--end-group

$(ARCH)/tpips:
	$(MAKE) $(ARCH)
	$(LINK) $@ $(TPIPS_LDFLAGS) $(main.dir)/$(TPIPS_MAIN) -ltpips \
		-Wl,--start-group $(addprefix -l,$(tpips.libs)) -Wl,--end-group

ifndef PIPS_NO_WPIPS
$(ARCH)/wpips:
	$(MAKE) $(ARCH)
	$(LINK) $@ $(WPIPS_LDFLAGS) $(main.dir)/$(WPIPS_MAIN) -lwpips \
		-Wl,--start-group $(addprefix -l,$(wpips.libs)) -Wl,--end-group
endif # PIPS_NO_WPIPS

ifndef PIPS_NO_GPIPS
$(ARCH)/gpips:
	$(MAKE) $(ARCH)
	$(LINK) $@ $(GPIPS_LDFLAGS) $(main.dir)/$(GPIPS_MAIN) -lgpips \
		-Wl,--start-group $(addprefix -l,$(gpips.libs)) -Wl,--end-group
endif # PIPS_NO_GPIPS

$(ARCH)/fpips:
	$(MAKE) $(ARCH)
	$(LINK) $@ $(FPIPS_LDFLAGS) $(main.dir)/$(FPIPS_MAIN) -lfpips \
		-Wl,--start-group $(addprefix -l,$(fpips.libs)) -Wl,--end-group

# all libraries as installed...

ifdef WITH_DYNAMIC_LIBRARIES
NEWGEN_LIBS	= \
	$(addsuffix .so, \
		$(addprefix $(NEWGEN_ROOT)/lib/$(ARCH)/lib,$(newgen.libs)))

LINEAR_LIBS	= \
	$(addsuffix .so, \
		$(addprefix $(LINEAR_ROOT)/lib/$(ARCH)/lib,$(linear.libs)))
PIPSLIBS_LIBS	= \
	$(addsuffix .so, \
		$(addprefix $(LIB.d)/lib,pipslibs))
else
NEWGEN_LIBS	= \
	$(addsuffix .a, \
		$(addprefix $(NEWGEN_ROOT)/lib/$(ARCH)/lib,$(newgen.libs)))

LINEAR_LIBS	= \
	$(addsuffix .a, \
		$(addprefix $(LINEAR_ROOT)/lib/$(ARCH)/lib,$(linear.libs)))
PIPSLIBS_LIBS	= \
	$(addsuffix .a, \
		$(addprefix $(LIB.d)/lib,$(pipslibs.libs)))
endif

# add other pips dependencies...
$(ARCH)/pips \
$(ARCH)/tpips \
$(ARCH)/wpips \
$(ARCH)/gpips \
$(ARCH)/fpips: \
	$(PIPSLIBS_LIBS) \
	$(NEWGEN_LIBS) \
	$(LINEAR_LIBS)

ifdef LIB_TARGET

# fix local library dependency
$(ARCH)/pips \
$(ARCH)/tpips \
$(ARCH)/wpips \
$(ARCH)/gpips \
$(ARCH)/fpips: \
	$(ARCH)/$(LIB_TARGET)

endif # LIB_TARGET
