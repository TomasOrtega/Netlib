FROM netlib-wire-capture:1
COPY exercise.py capture.sh /task/wire-nat/
COPY requirements.json deny.json permit.json demo-credential.json /task/admission/input/
CMD ["sh", "/task/wire-nat/capture.sh"]
