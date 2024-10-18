# To upload the Docker images to Dockerhub, log into the Docker console, and then run
#
#   docker buildx build --push --platform linux/amd64,linux/arm64 -t aaronbembenek/formulog:vX.Y.Z .
#
# (with the appropriate version number substituted for X.Y.Z).

FROM maven:3.8.6-openjdk-11 AS build
WORKDIR /root/formulog/
COPY src src
COPY pom.xml pom.xml 
RUN mvn package -DskipTests

FROM ubuntu:23.04
ARG version=0.8.0-SNAPSHOT
WORKDIR /root/
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
  sqlite3 \
  zlib1g-dev \
  # Install modified Souffle
  && git clone --branch eager-eval https://github.com/aaronbembenek/souffle.git \
  && cd souffle \
  && cmake -S . -B build -DCMAKE_BUILD_TYPE=Release -DSOUFFLE_ENABLE_TESTING=OFF \
  && cmake --build build -j$(nproc) \
  && cmake --build build --target install \
  && cmake --build build --target clean
WORKDIR /root/formulog/
COPY --from=build /root/formulog/target/formulog-${version}-jar-with-dependencies.jar formulog.jar
COPY examples examples