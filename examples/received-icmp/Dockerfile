FROM netlib-icmp-capture:1
COPY exercise.py capture.sh /task/received-icmp/
COPY requirements.json deny.json permit.json demo-credential.json /task/admission/input/
CMD ["sh", "/task/received-icmp/capture.sh"]
