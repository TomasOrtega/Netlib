FROM alpine@sha256:ff7f0c727dd796aa36787bfcd9a64bf35a6ce72a73451b3359fde849b6703d63

RUN apk add --no-cache build-base bison flex pkgconf linux-headers libmnl-dev \
    libnfnetlink-dev libtirpc-dev libnftnl-dev jansson-dev readline-dev libedit-dev \
    gmp-dev iproute2 python3

ENV PKG_CONFIG_PATH=/opt/netlib/lib/pkgconfig
ENV LD_LIBRARY_PATH=/opt/netlib/lib
ENV PATH=/opt/netlib/sbin:/opt/netlib/bin:$PATH

RUN wget -q https://www.netfilter.org/projects/libnetfilter_conntrack/files/libnetfilter_conntrack-1.1.1.tar.xz -O /tmp/library.tar.xz \
    && echo '769d3eaf57fa4fbdb05dd12873b6cb9a5be7844d8937e222b647381d44284820  /tmp/library.tar.xz' | sha256sum -c - \
    && tar -xJf /tmp/library.tar.xz -C /tmp \
    && cd /tmp/libnetfilter_conntrack-1.1.1 \
    && ./configure --prefix=/opt/netlib \
    && make -j2 && make install

RUN wget -q https://www.netfilter.org/projects/conntrack-tools/files/conntrack-tools-1.4.9.tar.xz -O /tmp/tools.tar.xz \
    && echo 'c15afe488a8d408c9d6d61e97dbd19f3c591942f62c13df6453a961ca4231cae  /tmp/tools.tar.xz' | sha256sum -c - \
    && tar -xJf /tmp/tools.tar.xz -C /tmp \
    && cd /tmp/conntrack-tools-1.4.9 \
    && ./configure --prefix=/opt/netlib --disable-cthelper --disable-cttimeout \
    && make -j2 && make install

RUN wget -q https://netfilter.org/projects/nftables/files/nftables-1.1.3.tar.xz -O /tmp/nftables.tar.xz \
    && echo '9c8a64b59c90b0825e540a9b8fcb9d2d942c636f81ba50199f068fde44f34ed8  /tmp/nftables.tar.xz' | sha256sum -c - \
    && tar -xJf /tmp/nftables.tar.xz -C /tmp \
    && cd /tmp/nftables-1.1.3 \
    && ./configure --prefix=/opt/netlib --disable-man-doc --disable-python --with-json \
    && make -j2 && make install
