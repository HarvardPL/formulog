# Makefile
#
# You can build the generated Formulog executable by using the `make` tool,
# optionally passing in `make -j<threads>` to allow parallelism during the
# build process.
#
# The `SOUFFLE_INCLUDE`, `BOOST_INCLUDE`, and `BOOST_LIB` variables can be
# overwritten, and they will be resolved in the order of precedence:
#   1. Variables passed directly to `make`.
#   2. Properties defined with `-D` when running `formulog.jar`.
#   3. Environment variables currently on the system.
# You can also manually pass in flags to the C++ compiler by running
# `make FLAGS=<flags>`.

-include rules.mk

ifndef SOUFFLE_INCLUDE
$(error SOUFFLE_INCLUDE is not set)
endif

ifndef BOOST_INCLUDE
$(error BOOST_INCLUDE is not set)
endif

ifndef BOOST_LIB
$(error BOOST_LIB is not set)
endif

CXX = g++
CXXFLAGS = -std=c++17 -O3 -march=native -fopenmp \
	-Wall -Wno-unused-variable -Wno-unused-but-set-variable \
	-I$(SOUFFLE_INCLUDE) -I$(BOOST_INCLUDE) $(FLAGS)
LDFLAGS = -L$(BOOST_LIB)
LDLIBS = -lpthread -lgomp \
	-lboost_filesystem -lboost_system -lboost_program_options

OBJS = main.o parser.o Symbol.o Term.o

all: $(OUTPUT_EXEC)

$(OUTPUT_EXEC): $(OBJS)
	$(CXX) $(LDFLAGS) -o $@ $^ $(LDLIBS)

clean:
	rm -f $(OBJS) $(OUTPUT_EXEC)
