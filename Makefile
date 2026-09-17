#-----------------------------------------------------------------------
CAPD = $(HOME)/capd-5.3.0
INCLUDE = `$(CAPD)/bin/capd-config --cflags`
LIBS = `$(CAPD)/bin/capd-config --libs`
WARNINGS = -Wall -Wno-deprecated-declarations -Wno-overloaded-virtual \
		   -Wno-unused-variable -Wno-array-bounds
FLAGS += -O2 -ggdb $(WARNINGS)
#-----------------------------------------------------------------------

PROGRAMS = rt

#-----------------------------------------------------------------------

rt: rt.cpp tarjan.h svd.h
	g++ $(INCLUDE) $(FLAGS) $@.cpp -o $@ $(LIBS)

tidy:
	@ - rm -f *.o *~

clean:
	@ - rm -f *.o *~ $(PROGRAMS)

#-----------------------------------------------------------------------
