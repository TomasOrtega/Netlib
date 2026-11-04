"""Tests for prose extraction and the limited style rules."""

import unittest

import check_text


class MarkdownTests(unittest.TestCase):
    def test_sentence_limits(self):
        description = "The model " + "has " * 23 + "nodes."
        instruction = "Use " + "the " * 19 + "model."
        issues = check_text.check_markdown(description + "\n\n" + instruction)
        self.assertEqual(
            [(issue.line, issue.rule) for issue in issues], [(1, "length"), (3, "length")]
        )
        self.assertIn("25 words", issues[0].message)
        self.assertIn("20 words", issues[1].message)

    def test_exact_limit_and_possessive(self):
        text = "The model " + "has " * 22 + "nodes.\n\nLean's theorem holds."
        self.assertEqual(check_text.check_markdown(text), [])

    def test_fences_and_reference_targets_are_not_prose(self):
        text = """```lean
-- Don't utilize this text.
```
~~~text
Don't commence.
~~~
[Use the model](https://example.com/don't/utilize_(test)).
[reference]: https://example.com/don't
"""
        self.assertEqual(check_text.check_markdown(text), [])

    def test_literals_and_source_titles(self):
        text = "Use ``a `don't` utilize`` and `commence`. Read *Don't Utilize Prior to Flight*."
        self.assertEqual(check_text.check_markdown(text), [])

    def test_literal_counts_once(self):
        text = "The model " + "has " * 21 + "`a very long code literal` nodes."
        self.assertEqual(check_text.check_markdown(text), [])

    def test_link_labels_are_prose(self):
        issues = check_text.check_markdown("Read [Don't utilize this](https://example.com).")
        self.assertEqual({issue.rule for issue in issues}, {"contraction", "word"})

    def test_linked_badges_keep_labels_without_urls(self):
        text = (
            "[![CI](https://github.com/owner/repo/checks.yml/badge.svg?branch=main)]"
            "(https://github.com/owner/repo/actions) "
            "[![Ruff](https://img.shields.io/badge/code%20style-Ruff-green)]"
            "(https://docs.astral.sh/ruff/)"
        )
        extracted = check_text.inline_text(text)
        self.assertNotIn("https", extracted)
        self.assertIn("CI", extracted)
        self.assertIn("Ruff", extracted)
        self.assertEqual(check_text.check_markdown(text), [])

    def test_linked_image_labels_remain_prose(self):
        issues = check_text.check_markdown(
            "[![Don't utilize this](https://example.com/image.svg)](https://example.com)"
        )
        self.assertEqual({issue.rule for issue in issues}, {"contraction", "word"})

    def test_lists_tables_and_locations(self):
        text = """# Don't utilize this title

- Use the model.
- Don't commence.

| Name | Meaning |
| --- | --- |
| Code | `utilize|commence` |
| Rule | Utilize the model. |
"""
        issues = check_text.check_markdown(text)
        self.assertEqual({issue.line for issue in issues}, {4, 9})

    def test_line_after_wrapped_sentence(self):
        issues = check_text.check_markdown("The model holds.\n\nThe proof holds.\nDon't commence.")
        self.assertEqual({issue.line for issue in issues}, {4})

    def test_technical_noun_exemption(self):
        glossary = "**Leverage**:\nA project device name."
        terms = check_text.glossary_terms(glossary)
        self.assertEqual(check_text.check_markdown("The Leverage device exists.", terms), [])
        self.assertEqual(len(check_text.check_markdown("The device utilizes a link.", terms)), 1)

    def test_smart_apostrophes(self):
        issues = check_text.check_markdown(
            "It’s valid. Don’t commence. The device’s port exists. It could’ve failed."
        )
        self.assertEqual([issue.rule for issue in issues].count("contraction"), 3)

    def test_hidden_comment_and_setext_title(self):
        text = """Don't utilize this source title
==============================

<!-- Don't

utilize this comment. -->
Use the model.
"""
        self.assertEqual(check_text.check_markdown(text), [])


class LeanTests(unittest.TestCase):
    def test_only_documentation_comments(self):
        text = """def text := "/-- Don't utilize a fake comment. -/"
-- Don't commence.
/- Don't commence. /-- Don't utilize this nested comment. -/ -/
/-- Don't commence. -/
def valid := true
"""
        issues = check_text.check_lean(text)
        self.assertEqual({issue.line for issue in issues}, {4})
        self.assertEqual({issue.rule for issue in issues}, {"contraction", "word"})

    def test_nested_comments_and_module_docs(self):
        text = "/-!\n# Rules\n\nUse the model. /- Don't utilize this note. -/\nDon't commence.\n-/"
        issues = check_text.check_lean(text)
        self.assertEqual({issue.line for issue in issues}, {5})

    def test_unclosed_comment(self):
        with self.assertRaisesRegex(ValueError, "Close"):
            check_text.check_lean("/-- Use the model.")

    def test_character_and_quoted_identifiers(self):
        text = """def quote := '"'
def «/-- Don't utilize this name. -/» := true
/-- Don't commence. -/
"""
        issues = check_text.check_lean(text)
        self.assertEqual({issue.line for issue in issues}, {3})

    def test_verso_source_and_metadata(self):
        text = """import VersoManual
def text := "Don't utilize this source."
#doc (Manual) "Don't utilize this title" =>
%%%
tag := "Don't commence"
%%%
Use the model.
```lean
#eval "Don't commence"
```
Don't commence.
"""
        issues = check_text.check_manual(text)
        self.assertEqual({issue.line for issue in issues}, {11})
        self.assertEqual({issue.rule for issue in issues}, {"contraction", "word"})


class HTMLTests(unittest.TestCase):
    def test_visible_prose_and_labels(self):
        text = """<meta name="description" content="Don't commence.">
<p>Use <a href="https://example.com/don't">the model</a>.</p>
<img alt="Don't utilize this label." src="don't.png">
<script>Don't commence.</script><style>/* Don't commence. */</style>
<pre><code>Don't commence.</code></pre>
<span aria-hidden="true">Don't commence.</span>
"""
        issues = check_text.check_html(text)
        self.assertEqual({issue.line for issue in issues}, {1, 3})
        self.assertEqual(len(issues), 4)

    def test_inline_markup_keeps_one_sentence(self):
        text = "<p>The <em>model</em> " + "has " * 23 + "nodes.</p>"
        issues = check_text.check_html(text)
        self.assertEqual([issue.rule for issue in issues], ["length"])
        self.assertIn("26", issues[0].message)

    def test_templates_and_inline_code_count_once(self):
        text = (
            "<p>The model "
            + "has " * 20
            + "{{long_template_name}} <code>don't utilize</code> nodes.</p>"
        )
        self.assertEqual(check_text.check_html(text), [])


if __name__ == "__main__":
    unittest.main()
