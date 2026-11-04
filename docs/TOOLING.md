# Lean and documentation tools

The tool check date is 4 November 2026.

## Versions

Lean **4.35.0** is the latest stable release on the check date.
The release date is 12 October 2026.
Use `leanprover/lean4:v4.35.0` in `lean-toolchain`.
Newer release candidates do not have stable release status.
See the [official Lean release](https://github.com/leanprover/lean4/releases/tag/v4.35.0)
and the [Lean package registry](https://reservoir.lean-lang.org/).

Use the `v4.35.0` version of doc-gen4 with this Lean release.
Its exact commit is `0e1ffe2e4ba5ecfdfaf15c65b8d3805dbb7134ae`.
Its toolchain file specifies Lean 4.35.0.
See the [doc-gen4 version](https://api.github.com/repos/leanprover/doc-gen4/git/ref/tags/v4.35.0)
and its [toolchain file](https://github.com/leanprover/doc-gen4/blob/v4.35.0/lean-toolchain).

Verso also has a version for Lean 4.35.0.
Its exact commit is `304b8561790c50222551c937ce02928df0d5b445`.
Use this version for the Netlib manual and its checked Lean examples.
The `main` branch can require a release candidate.
See the [Verso version](https://api.github.com/repos/leanprover/verso/git/ref/tags/v4.35.0),
its [toolchain file](https://github.com/leanprover/verso/blob/v4.35.0/lean-toolchain),
and its [version rules](https://github.com/leanprover/verso#branches-and-tags).

## API documentation

Use doc-gen4 for the API pages.
Keep its Lake project in `docbuild/`.
The project needs two packages: doc-gen4 and the parent `netlib` package.
This keeps documentation tools separate from the library dependencies.
The official guide recommends this directory layout.
See the [doc-gen4 setup](https://github.com/leanprover/doc-gen4#usage).

Run these commands on a local computer:

```sh
cd docbuild
lake update doc-gen4
lake build netlib/Netlib:docs
```

Save `docbuild/lake-manifest.json` in Git after a dependency update.
The manifest records exact dependency commits.
The doc-gen4 release also supplies a
[dependency manifest](https://github.com/leanprover/doc-gen4/blob/v4.35.0/lake-manifest.json).

The generated site starts at `docbuild/.lake/build/doc/index.html`.
Doc-gen4 includes API pages for imported modules and the Lean core libraries.
Use an HTTP server for local review.
Some browser features do not work with direct file access.
See the [doc-gen4 output guide](https://github.com/leanprover/doc-gen4#usage).

```sh
python3 -m http.server --directory docbuild/.lake/build/doc 8000
```

Open `http://localhost:8000/` in a browser.
Save the website in `docs/site.tar.gz` before a push.
Save source hashes in `docs/site-manifest.json`.
The manifest connects the saved site to its input files.
CI checks these hashes before it publishes the site.

The standard doc-gen4 command includes imported modules.
Its `fromDb` command also follows imports from each requested root.
It has no option to exclude imported modules.
A smaller site needs a local export step after doc-gen4.
See the [doc-gen4 commands](https://github.com/leanprover/doc-gen4/blob/v4.35.0/Main.lean).

The export must preserve the project pages, CSS, JavaScript, and search data.
It must repair links before it removes dependency pages.
The `.bmp` search files contain JSON text.
The browser scripts use `declarations/declaration-data.bmp` for search, instances, and module links.
See the [search data format](https://github.com/leanprover/doc-gen4/blob/v4.35.0/DocGen4/Output/ToJson.lean)
and the [browser data code](https://github.com/leanprover/doc-gen4/blob/v4.35.0/static/declaration-data.js).

## Manual

The source manual is `docbuild/Manual.lean`.
The executable entry is `docbuild/ManualMain.lean`.
Verso checks the manual's Lean examples when it builds these modules.
The manual uses the official `VersoManual` import and `manualMain` entry.
See the [official manual template](https://github.com/leanprover/verso-templates/tree/main/basic-book).

Run this command in `docbuild/` for a separate manual preview:

```sh
lake exe manual --output ../.lake/manual
```

The HTML files start at `.lake/manual/html-multi/index.html` from the repository root.
The manual disables TeX output.
The combined site places the manual in `manual/` and the API in `api/`.
See the [Verso output command](https://github.com/leanprover/verso/blob/v4.35.0/src/verso-manual/VersoManual.lean).

## Local build and CI

Doc-gen4 needs Lean and a C compiler on macOS and Linux.
Its documentation target needs compiled library modules.
The tagged build file requests each module's `leanArts` build output.
Thus, a documentation build can compile Lean code.
See the [doc-gen4 requirements](https://github.com/leanprover/doc-gen4#requirements-to-run-doc-gen4)
and its [build targets](https://github.com/leanprover/doc-gen4/blob/v4.35.0/lakefile.lean).

Verso also uses Lean build commands for source pages.
It first builds the `literate` target.
It then runs `verso-html` to produce HTML.
These commands belong on the local computer.
See the [Verso source guide](https://github.com/leanprover/verso#rendering-lean-code).

The Netlib CI must never compile Lean code.
It must use saved website files.
It must not install Lean or run Lake, doc-gen4, or Verso.
A dependency cache does not remove this rule.
Keep all proof checks and API generation local.

Doc-gen4 has no GitHub release assets on the check date.
The Verso release supplies its manual as HTML and PDF files.
These releases do not supply a replacement API generator executable.
See the [doc-gen4 release list](https://api.github.com/repos/leanprover/doc-gen4/releases)
and the [Verso release assets](https://github.com/leanprover/verso/releases/tag/v4.35.0).

CI can check source files, verify site links, and publish the saved site.
Use the GitHub Pages actions to configure Pages, upload the site, and deploy it.
The deploy job needs `pages: write` and `id-token: write` permissions.
GitHub supplies a static deploy example with no build job.
See the [official Pages workflow guide](https://docs.github.com/en/pages/getting-started-with-github-pages/using-custom-workflows-with-github-pages).

## Save and deploy the site

Run the source checks on your computer.
Commit the checked Lean source before the documentation build.
Each API source link uses this commit.

Run the combined documentation command from the repository root:

    python3 scripts/build_docs.py

The command builds the Verso manual and doc-gen4 API pages.
It keeps only Netlib API pages and their required assets.
The API search index contains only Netlib declarations.
Links to Lean declarations use upstream source files or the official Lean API.

The command saves an archive and its source manifest in the docs directory.
The manifest contains hashes for all site inputs.
CI rejects the saved archive when these input hashes change.
Commit the archive and manifest after the build.

Extract a checked copy into an empty preview folder:

    python3 scripts/check_site.py --extract build/site
    python3 -m http.server --directory build/site 8000

Open http://localhost:8000/ to review the pages.
Then push the source and documentation commits.
The Check source workflow verifies source files, text, archive hashes, and links.
It does not run a compiler.

To deploy with GitHub Pages:

1. Open the repository Pages settings.
2. Select GitHub Actions as the source.
3. Open the Deploy docs workflow.
4. Run the workflow on the main branch.

This workflow deploys the checked static package.
It does not generate documentation or install a Lean toolchain.

## Upgrade procedure

1. Check the latest stable Lean release.
2. Select the matching doc-gen4 version.
3. Update both toolchain files.
4. Update the docbuild manifest locally.
5. Build the library locally.
6. Run the local tests.
7. Generate the API pages locally.
8. Review the saved site with an HTTP server.
9. Commit the source and documentation in separate groups.
10. Push the commits to start static CI checks.
11. Run the Deploy docs workflow when a site update is necessary.
