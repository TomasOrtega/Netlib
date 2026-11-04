FROM netlib-lifecycle-capture:6.19.0
RUN apk add --no-cache openssl=3.5.9-r0 openssl-dev=3.5.9-r0
COPY hostapd-2.12.tar.gz wpa_supplicant-2.12.tar.gz /tmp/
RUN cd /tmp && \
    echo 'f43502561c28ba47ab77e18e1a973d07361c68cc8b14178e619bd5796b70eabd  hostapd-2.12.tar.gz' | sha256sum -c - && \
    echo '08e23937e16d0155e55cab2b51f51fbe10d80a1aa91c4e15442645059b737ef6  wpa_supplicant-2.12.tar.gz' | sha256sum -c - && \
    tar -xzf hostapd-2.12.tar.gz && tar -xzf wpa_supplicant-2.12.tar.gz
COPY hostapd-build.config /tmp/hostapd-2.12/hostapd/.config
COPY supplicant-build.config /tmp/wpa_supplicant-2.12/wpa_supplicant/.config
RUN make -j2 -C /tmp/hostapd-2.12/hostapd && \
    make -j2 -C /tmp/wpa_supplicant-2.12/wpa_supplicant && \
    cp /tmp/hostapd-2.12/hostapd/hostapd /usr/local/bin/ && \
    cp /tmp/hostapd-2.12/hostapd/hostapd_cli /usr/local/bin/ && \
    cp /tmp/wpa_supplicant-2.12/wpa_supplicant/wpa_supplicant /usr/local/bin/ && \
    cp /tmp/wpa_supplicant-2.12/wpa_supplicant/wpa_cli /usr/local/bin/
COPY exercise.py capture.sh /task/
CMD ["sh", "/task/capture.sh"]
