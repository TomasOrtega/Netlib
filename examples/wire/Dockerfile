FROM netlib-admission-capture:1
COPY exercise.py capture.sh /task/wire/
COPY requirements.json deny.json permit.json demo-credential.json /task/admission/input/
CMD ["sh", "/task/wire/capture.sh"]
