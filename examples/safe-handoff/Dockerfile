FROM netlib-replication-capture:1
RUN echo 'b39ac6a76f8299968408d3f2948ea59d9502b299d3e0c78c93658b65df3be5be  /tmp/iproute2.tar.gz' | sha256sum -c - \
    && make -C /tmp/iproute2-6.19.0 -j2 SUBDIRS='lib tc' \
    && install /tmp/iproute2-6.19.0/tc/tc /opt/netlib/sbin/tc
COPY exercise.py capture.sh /task/safe-handoff/
CMD ["sh", "/task/safe-handoff/capture.sh"]
