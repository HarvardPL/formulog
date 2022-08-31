FROM maven:3.8.6-openjdk-11 AS build
WORKDIR /root/formulog/
COPY src src
COPY pom.xml pom.xml 
RUN mvn package -DskipTests

FROM ubuntu:22.04
ARG version=0.6.0-SNAPSHOT
RUN apt-get update \
  && DEBIAN_FRONTEND=noninteractive \
  apt-get install -y openjdk-11-jre z3
WORKDIR /root/formulog/
COPY --from=build /root/formulog/target/formulog-${version}-jar-with-dependencies.jar formulog.jar
COPY examples examples
