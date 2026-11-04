# Documentation style

Use Simplified Technical English for Netlib documentation and comments.
The [ASD-STE100 standard](https://www.asd-ste100.org/assets/files/ASD-STE100_ISSUE9.pdf)
defines its writing rules and dictionary. The
[official FAQ](https://www.asd-ste100.org/STE_faq.html) explains technical terms
and their use. The
[overview](https://en.wikipedia.org/wiki/Simplified_Technical_English) gives
background.

## Write clear text

- Use active voice and simple verb forms.
- Put one instruction in each sentence.
- Use at most 20 words in an instruction and 25 words in a description.
- Keep one topic in each paragraph. Use no more than six sentences per paragraph.
- Put a necessary condition before its instruction.
- Use lists for parallel items or a sequence of steps.
- Use complete sentences. Do not remove necessary articles or verbs.
- Use a period in place of a semicolon.
- Use American English spelling.

## Use precise terms

Use the approved dictionary meaning and part of speech for general words.
Use the technical terms in the [glossary](../GLOSSARY.md) consistently.
Keep code identifiers, command syntax, quoted requirements, and official titles
exact. Define a new technical term when its meaning is necessary.

Comments must explain information that the code does not make clear.
State theorem assumptions and model limits without a larger claim.
Keep the mathematical meaning when you simplify a sentence.

## Automated checks

Run `uv run --locked python scripts/check_text.py` before a documentation export.
The script reads `README.md`, `GLOSSARY.md`, `docs/*.md`, library documentation
comments, and the Verso manual. It also reads prose in `docs/assets/index.html`.
It ignores other Lean source and fenced examples.

The checker applies these rules:

- Descriptive sentences have at most 25 words.
- Clear commands have at most 20 words.
- Prose contains no contractions.
- Prose avoids the alternatives in the table below.

Command detection uses an explicit list of initial verbs.
Other sentence forms use the descriptive limit.
Inline code and italic source titles each count as one word.
Link labels count as prose. Link targets and source blockquotes do not.
Glossary technical nouns are permitted.
HTML checks include visible text, image alternatives, accessibility labels, and
page descriptions. They exclude scripts, styles, hidden elements, and code
examples. Template fields and inline code each count as one word.

| Avoid | Use |
| --- | --- |
| `utilize` | `use` |
| `utilizes` | `uses` |
| `utilized` | `used` |
| `leverage` | `use` |
| `commence` | `start` |
| `aforementioned` | `specified` |
| `prior to` | `before` |
| `in order to` | `to` |

This checker does not certify full ASD-STE100 compliance.
Human review must assess grammar, active voice, dictionary meanings, technical
terms, and preservation of meaning.

Use the locked environment for every project Python command.
Use `uv run --locked prek -a --quiet` for the default hook stage.
Compiler and compiled CLI checks require the explicit manual stage.
The saved-site check uses the pre-push stage and an explicit CI step.
CI must not run the manual stage or any Lean tool.

For standards text, distinguish model check IDs from source clause IDs.
State each assumption next to its result.
Keep missing evidence and unsupported scope visible.
An AP setting must not imply a claim about negotiated traffic or product approval.
An observed identity result must not imply a proof of the identity protocol.

## Software terms

The documentation uses CLI for command-line interface, API for application
programming interface, and CI for continuous integration.
Use these technical verbs with the specified meanings:

| Verb | Meaning |
| --- | --- |
| Compile | Translate source code into the artifacts that the toolchain uses. |
| Deploy | Copy a prepared artifact to its hosting service. |
| Evaluate | Compute a formula or observation value under an interpretation. |
| Infer | Derive information from supplied facts or rules. |
| Parse | Convert input text into a structured representation. |
| Prove | Establish a formal proposition with a proof that Lean accepts. |
| Render | Produce text or HTML from a structured representation. |
| Redact | Replace a secret value with a presence statement or a hidden-value marker. |
| Verify | Establish that data, a result, or a proof meets its formal conditions. |
