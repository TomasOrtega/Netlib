FROM netlib-eap-capture:2.12
COPY exercise.py capture.sh /task/admission/
COPY eap_exercise.py capture_conntrack.py /task/
COPY requirements.json deny.json permit.json demo-credential.json /task/admission/input/
CMD ["sh", "/task/admission/capture.sh"]
