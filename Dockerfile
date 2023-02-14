FROM maven:3.8.6-openjdk-11 AS build
WORKDIR /root/formulog/
COPY src src
COPY pom.xml pom.xml 
RUN mvn package -DskipTests

FROM ubuntu:23.04
WORKDIR /root/formulog/
ARG version=0.7.0-SNAPSHOT
RUN apt-get update \
  && DEBIAN_FRONTEND=noninteractive \
  apt-get install -y \
  openjdk-11-jre \
  z3 \
  libboost1.81-all-dev \
  libtbb-dev \
  bison \
  build-essential \
  clang \
  cmake \
  doxygen \
  flex \
  g++ \
  git \
  libffi-dev \
  libncurses5-dev \
  libsqlite3-dev \
  make \
  mcpp \
  python3 \
  sqlite \
  zlib1g-dev
COPY --from=build /root/formulog/target/formulog-${version}-jar-with-dependencies.jar formulog.jar
COPY examples examples
RUN git clone https://github.com/souffle-lang/souffle.git \
  && cd souffle \
  && cmake -S . -B build \
  && cmake --build build --target install -j 4 \
  && cd .. \
  && rm -rf souffle
