This library is a very low-level library dealing only with PIPS
"entity" names, without any knowledge of the data structure "entity",
which is dealt with by library ri-util.

Many kinds of entities are used in PIPS and, to increase flexibility
if not execution speed, it was decided to use their unique names to
encode their kinds.

An entity may be a function, a variable, a Fortran common, a constant,
a type, a C compilation unit...

Several libraries may deal with entity names only: pipsdbm, the PIPS
database manager library, pipsmake, the PIPS make mechanism. Library
naming is also used by library ri-util, which includes naming.h, to
make naming functions available to all libraries using ri-util.

Notes:

1. librairies "naming" and "constants" may have similar goals.

2. some string functions may still be scattered in different libraries.


