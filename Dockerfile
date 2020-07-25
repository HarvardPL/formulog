## Base configuration
FROM ubuntu:20.04 AS base
RUN apt-get update && \
  DEBIAN_FRONTEND=noninteractive \
  apt-get install -y build-essential wget openjdk-11-jre z3 python3

# Boost
# (adapted from https://github.com/pblischak/boost-docker-test)
WORKDIR /home
RUN cd /home && wget https://dl.bintray.com/boostorg/release/1.73.0/source/boost_1_73_0.tar.gz \
  && tar xzf boost_1_73_0.tar.gz \
  && rm boost_1_73_0.tar.gz \
  && cd boost_1_73_0 \
  && ./bootstrap.sh --prefix=/usr/local --with-libraries=program_options,system,filesystem \
  && ./b2 install \
  && cd /home \
  && rm -rf boost_1_73_0

# Souffle
# (adapted from https://souffle-lang.github.io/install)
RUN echo "deb https://dl.bintray.com/souffle-lang/deb-unstable focal main" >> /etc/apt/sources.list \
  && apt-key adv --keyserver hkp://keyserver.ubuntu.com:80 --recv-keys 379CE192D401AB61 \
  && apt-get update \
  && apt-get install -y souffle

# Environment variables for Makefile
ENV SOUFFLE_INCLUDE /usr/include
ENV BOOST_INCLUDE /usr/local/include
ENV BOOST_LIB /usr/local/lib
RUN useradd -ms /bin/bash formulog


## Development target (mount . as /home/formulog/dev)
FROM base AS dev
RUN apt-get install -y maven
USER formulog
WORKDIR /home/formulog/dev


## Run tests and build jar with dependencies
FROM maven:3.6.3-ibmjava-alpine AS build
RUN apk add --no-cache z3
COPY src /home/app/src
COPY pom.xml /home/app
RUN mvn -f /home/app/pom.xml clean package


## Production target
FROM base
ARG version=0.3.0-SNAPSHOT
USER formulog
WORKDIR /home/formulog
COPY --chown=formulog:formulog --from=build /home/app/target/formulog-${version}-jar-with-dependencies.jar formulog.jar
COPY --chown=formulog:formulog benchmarks benchmarks
