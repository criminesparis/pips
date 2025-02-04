# $Id: local.mk 1607 2015-07-19 19:09:54Z coelho $

#  arithmetique:
#  vecteur[arithmetique]: vectors
#  contrainte[vecteur]: constraints
#  sc[contrainte,vecteur]: systems (equalities and inequalities)
#  matrice: rational dense matrices
#  ray_dte:
#  sommet[ray_dte,vecteur]: for constraints, systems and functions (?)
#  plint[sommet,matrice,sc]: integer linear programming
#  sparse_sc[matrice,sc]: sparse systems
#  sg[sommet,ray_dte]: generating systems
#  polyedre[sg,sc]: polyhedrons

FWD_DIRS = \
	arithmetique \
	vecteur \
	contrainte \
	sc \
	matrice \
	matrix \
	ray_dte \
	sommet \
	sparse_sc \
	sg \
	polynome \
	union \
	polyedre \
	doxygen
##???	linearlibs # commented out FC 2015-07-19
#	plint
#	Tests

FWD_PARALLEL	= 1

# (re)build inter library header dependencies
deps.mk:
	{ \
	  ../makes/inc2deps.sh $(FWD_DIRS) | \
	    sed -e 's/:/:fwd-/;/^[^#]/s/^/fwd-/' | \
	    sed -e 's/^fwd-arith/#fwd-arith/' | sort ; \
	} > $@

# use deps when generating headers
ifeq ($(FWD_TARGET),phase0)
FWD_DEPS = 1
else ifeq ($(FWD_TARGET),phase2)
FWD_DEPS = 1
endif
