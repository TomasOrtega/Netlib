FROM netlib-received-icmp-capture:1
COPY exercise.py nflog.py capture.sh /task/reassembly/
COPY requirements.json deny.json permit.json demo-credential.json /task/admission/input/
CMD ["sh", "/task/reassembly/capture.sh"]
