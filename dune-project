(lang dune 3.20)

(package
 (name hm_tut)
 (depends
  ocaml
  dune
  base
  stdio
  ppx_inline_test
  mini_ml_parser))

(pin
 (url "git+https://github.com/smasher164/mini-ml-parser.git")
 (package (name mini_ml_parser)))
