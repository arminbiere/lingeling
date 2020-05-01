FROM ubuntu:18.04
ARG DEBIAN_FRONTEND=noninteractive
RUN apt-get update && apt-get install -y git gcc make
ADD . lingeling
RUN cd lingeling && ./configure.sh && make plingeling
ENTRYPOINT ["lingeling/aws-run.sh"]
CMD []
