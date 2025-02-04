Library syntheses contains passes that add or remove modules such as:

 * initializer.c, which synthesizes Fortran or C missing source codes from their
signatures,

 * clone.c, which synthesizes specialized versions of a function assuming one parameter is a known constant,

Inling and outlining PIPS passes could also be moved into this library.

Unlike the transformations library, this library depends on the C parser.
