TARGET	= task_parallelization

LIB_CFILES=	\
		SDG.c\
		cost_model.c\
		BDSC.c\
		HBDSC.c\
		instrumentation.c\
		spire_generation.c\
		communication_generation.c\
		openmp_generation.c\
		mpi_generation.c \
		task_mapping.c \
		copy_value_of_write.c \
		variable_replication.c \
		eliminate_original_variables.c \
		mpi_conversion.c

INC_TARGET =    $(TARGET).h

LIB_TARGET =    lib$(TARGET).a

# common stuff
ROOT    = ../../..
PROJECT = pips
include $(ROOT)/makes/main.mk
