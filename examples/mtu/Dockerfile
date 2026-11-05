FROM netlib-wire-nat-capture:1
COPY exercise.py capture.sh /task/mtu/
COPY requirements.json deny.json permit.json demo-credential.json /task/admission/input/
CMD ["sh", "/task/mtu/capture.sh"]
