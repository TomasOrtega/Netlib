FROM netlib-conntrack-capture:1.4.9

RUN apk add --no-cache libcap-dev elfutils-dev \
    && wget -q https://www.kernel.org/pub/linux/utils/net/iproute2/iproute2-6.19.0.tar.gz -O /tmp/iproute2.tar.gz \
    && echo 'b39ac6a76f8299968408d3f2948ea59d9502b299d3e0c78c93658b65df3be5be  /tmp/iproute2.tar.gz' | sha256sum -c - \
    && tar -xzf /tmp/iproute2.tar.gz -C /tmp \
    && cd /tmp/iproute2-6.19.0 \
    && make -j2 SUBDIRS='lib ip' \
    && install ip/ip /opt/netlib/sbin/ip
