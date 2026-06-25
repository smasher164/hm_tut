# Type Inference (Part 1)

This is the companion repository to the blog post [Type Inference (Part 1)](https://blog.akhil.cc/type-inference-part-1).

## Structure

- [`lib/`](lib/): The OCaml source (`one.ml`, `two.ml`, ...) where each file corresponds to the features added in a section of the article. Depends on my [mini-ml-parser](https://github.com/smasher164/mini-ml-parser) project for parsing the expression language.
- [`hm_tutorial.md`](hm_tutorial.md): The article itself.
- [`bin/render.ml`](bin/render.ml): A small OCaml renderer that turns the Markdown into the published HTML, with KaTeX-rendered judgement rules, syntax-highlighted code blocks, and the interactive widgets spliced into where you see the `<widget>` comments.
- [`widgets/`](widgets/): interactive visualizations for let generalization and unification.

## A note on what was AI-assisted

The article text in [`hm_tutorial.md`](hm_tutorial.md) and the OCaml implementation in [`lib/`](lib/) are mine. The rendering pipeline in [`bin/`](bin/) and the interactive widgets in [`widgets/`](widgets/) were built with help from Claude.
