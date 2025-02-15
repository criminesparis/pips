! $Id: hpfc_specific_mpi.h 23065 2016-03-02 09:05:50Z coelho $
!
! Copyright 1989-2016 MINES ParisTech
!
! This file is part of PIPS.
!
! PIPS is free software: you can redistribute it and/or modify it
! under the terms of the GNU General Public License as published by
! the Free Software Foundation, either version 3 of the License, or
! any later version.
!
! PIPS is distributed in the hope that it will be useful, but WITHOUT ANY
! WARRANTY; without even the implied warranty of MERCHANTABILITY or
! FITNESS FOR A PARTICULAR PURPOSE.
!
! See the GNU General Public License for more details.
!
! You should have received a copy of the GNU General Public License
! along with PIPS.  If not, see <http://www.gnu.org/licenses/>.
!
! MPI commons 
!
     
      common /HPFC MPI COMMONS/
     $     HPFC TYPE MPI(8),
     $     HPFC REDFUNC MPI(4),
     $     HPFC COMMUNICATOR,
     $     HPFC COMM NODES,
     $     RECEIVED BY BROADCAST,
     $     BCAST LENGTH, 
     $     BUFFER ATTACHED
      integer HPFC TYPE MPI,
     $     HPFC REDFUNC MPI,
     $     HPFC COMMUNICATOR,
     $     HPFC COMM NODES,
     $     BCAST LENGTH 
      logical RECEIVED BY BROADCAST,
     $     BUFFER ATTACHED



!
! explicit manipulation of buffers
!

      common /HPFC MPI BUFFER/
     $     PACKING BUFFER POSITION,
     $     UNPACKING BUFFER POSITION
      integer
     $     PACKING BUFFER POSITION,
     $     UNPACKING BUFFER POSITION


!
! that's all 
!
