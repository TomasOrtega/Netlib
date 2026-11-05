FROM netlib-safe-handoff-capture:1
COPY exercise.py capture.sh /task/campus/
COPY requirements.json demo-credential.json permit.json deny.json /task/campus/input/
CMD ["sh", "/task/campus/capture.sh"]
