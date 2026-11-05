FROM netlib-mtu-capture:1
COPY exercise.py capture.sh /task/icmp/
COPY requirements.json deny.json permit.json demo-credential.json /task/admission/input/
CMD ["sh", "/task/icmp/capture.sh"]
