# $Id: longlong.mk 1231 2016-03-02 08:16:46Z coelho $
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

# macros related to use of 64 bits arithmetic.

# hardwired integer division assumed.

CPPFLAGS += \
	-DLINEAR_VALUE_IS_LONGLONG \
	-DLINEAR_VALUE_PROTECT_MULTIPLY \
	-ULINEAR_VALUE_ASSUME_SOFTWARE_IDIV

