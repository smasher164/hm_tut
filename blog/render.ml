open! Base
open Stdio

let read_file path = In_channel.read_all path
let write_file path content = Out_channel.write_all path ~data:content

let ensure_dir d =
  if not (Stdlib.Sys.file_exists d) then Stdlib.Sys.mkdir d 0o755

let katex_css_inline () : string =
  let temp = Stdlib.Filename.temp_file "katex-bin" ".txt" in
  let _ =
    Stdlib.Sys.command
      (Printf.sprintf "command -v katex > %s 2>/dev/null"
         (Stdlib.Filename.quote temp))
  in
  let bin = String.strip (read_file temp) in
  Stdlib.Sys.remove temp;
  if String.is_empty bin then ""
  else
    let prefix = Stdlib.Filename.dirname (Stdlib.Filename.dirname bin) in
    let path = prefix ^ "/lib/node_modules/katex/dist/katex.min.css" in
    if Stdlib.Sys.file_exists path then
      let css = read_file path in
      String.substr_replace_all css
        ~pattern:"url(fonts/"
        ~with_:"url(https://cdn.jsdelivr.net/npm/katex@0.16/dist/fonts/"
    else ""

(* Longer prefixes must come first so prefix matches do not shadow each other. *)
let unicode_subs : (string * string) list = [
  "...", "\\dots ";
  "->", " \\to ";
  "=>", "\\Rightarrow ";
  "::", " :: ";
  "↦", " \\mapsto ";
  "⊢", " \\vdash ";
  "⊆", " \\subseteq ";
  "∀", "\\forall ";
  "∈", " \\in ";
  "∉", " \\notin ";
  "→", " \\to ";
  "Γ", "\\Gamma ";
  "Δ", "\\Delta ";
  "Σ", "\\Sigma ";
  "α", "\\alpha ";
  "β", "\\beta ";
  "λ", "\\lambda ";
  "μ", "\\mu ";
  "σ", "\\sigma ";
  "τ", "\\tau ";
  "ε", "\\varepsilon ";
  "ω", "\\omega ";
  "ρ", "\\rho ";
  "∅", " \\emptyset ";
  "∧", " \\land ";
  "∨", " \\lor ";
  "≤", " \\le ";
  "≥", " \\ge ";
  "≠", " \\ne ";
  "·", " \\cdot ";
  "\\", " \\setminus ";
]

let keywords =
  ["let"; "rec"; "in"; "fun"; "if"; "then"; "else"; "with"; "type"; "and";
   "for"; "each"]

let unicode_at s i =
  let n = String.length s in
  List.find_map unicode_subs ~f:(fun (pat, latex) ->
    let plen = String.length pat in
    if i + plen <= n
       && String.equal (String.sub s ~pos:i ~len:plen) pat
    then Some (latex, plen)
    else None)

let is_word_char c = Char.is_alphanum c || Char.equal c '_'

let has_digit s = String.exists s ~f:Char.is_digit

let to_latex (s : string) : string =
  let buf = Buffer.create (String.length s * 2) in
  let i = ref 0 in
  let n = String.length s in
  while !i < n do
    let c = s.[!i] in
    match unicode_at s !i with
    | Some (latex, len) ->
      Buffer.add_string buf latex;
      i := !i + len
    | None ->
      if Char.is_whitespace c then begin
        Buffer.add_string buf "\\ ";
        Int.incr i
      end else if Char.equal c '|' then begin
        Buffer.add_string buf " \\mathrel{|} ";
        Int.incr i
      end else if is_word_char c then begin
        let j = ref !i in
        while !j < n && is_word_char s.[!j] do Int.incr j done;
        let word = String.sub s ~pos:!i ~len:(!j - !i) in
        let format_part part =
          if String.is_empty part then ""
          else if List.mem keywords part ~equal:String.equal then
            "\\mathtt{" ^ part ^ "}"
          else if String.length part = 1 then part
          else if has_digit part then "\\mathit{" ^ part ^ "}"
          else "\\textit{" ^ part ^ "}"
        in
        if String.equal word "_" then
          Buffer.add_string buf "\\_"
        else if not (String.contains word '_') then
          Buffer.add_string buf (format_part word)
        else begin
          let parts = String.split word ~on:'_' in
          let first_empty = match parts with "" :: _ -> true | _ -> false in
          let last_single =
            match List.last parts with
            | Some s -> String.length s = 1
            | None -> false
          in
          if first_empty || last_single then
            let rec build = function
              | [] -> ""
              | [x] -> format_part x
              | hd :: tl -> format_part hd ^ "_{" ^ build tl ^ "}"
            in
            Buffer.add_string buf (build parts)
          else
            let escaped =
              String.substr_replace_all word ~pattern:"_" ~with_:"\\_"
            in
            if has_digit word then
              Buffer.add_string buf ("\\mathit{" ^ escaped ^ "}")
            else
              Buffer.add_string buf ("\\textit{" ^ escaped ^ "}")
        end;
        i := !j
      end else begin
        Buffer.add_char buf c;
        Int.incr i
      end
  done;
  Buffer.contents buf

type rule = { name : string; premise_tiers : string list; conclusion : string }

let divider_with_name_re = Re.Perl.compile_pat {|^([A-Za-z][A-Za-z0-9-]*):-{3,}\s*$|}
let divider_only_re = Re.Perl.compile_pat {|^-{3,}\s*$|}
let labeled_content_re = Re.Perl.compile_pat {|^([A-Za-z][A-Za-z0-9-]*):\s+(.+)$|}

let classify_line (line : string) =
  let stripped = String.strip line in
  match Re.exec_opt divider_with_name_re stripped with
  | Some g -> `Named_div (Re.Group.get g 1)
  | None ->
    if Re.execp divider_only_re stripped then `Div
    else
      match Re.exec_opt labeled_content_re stripped with
      | Some g -> `Labeled_content (Re.Group.get g 1, Re.Group.get g 2)
      | None -> `Content line

let rec split_on_dividers groups current = function
  | [] -> List.rev (List.rev current :: groups)
  | `Content line :: rest ->
    split_on_dividers groups (line :: current) rest
  | `Labeled_content (_, content) :: rest ->
    split_on_dividers groups (content :: current) rest
  | (`Div | `Named_div _) :: rest ->
    split_on_dividers (List.rev current :: groups) [] rest

let parse_rule (lines : string list) : rule option =
  let tokens = List.map lines ~f:classify_line in
  let has_div =
    List.exists tokens ~f:(function `Div | `Named_div _ -> true | _ -> false)
  in
  let name =
    List.find_map tokens ~f:(function
      | `Named_div n -> Some n
      | `Labeled_content (n, _) -> Some n
      | _ -> None)
  in
  let groups = split_on_dividers [] [] tokens in
  match name, has_div, List.rev groups with
  | Some name, true, conclusion_group :: premise_groups_rev ->
    let conclusion_lines =
      List.filter conclusion_group ~f:(fun s ->
        not (String.is_empty (String.strip s)))
    in
    (match conclusion_lines with
     | [conclusion] ->
       let premise_groups = List.rev premise_groups_rev in
       let premise_tiers =
         List.map premise_groups ~f:(fun group ->
           List.filter group ~f:(fun s -> not (String.is_empty (String.strip s)))
           |> List.map ~f:String.strip
           |> String.concat ~sep:"  ")
         |> List.filter ~f:(fun s -> not (String.is_empty s))
       in
       Some { name; premise_tiers; conclusion = String.strip conclusion }
     | _ -> None)
  | _ -> None

let tier_to_latex (tier : string) : string =
  let parts =
    Re.split (Re.Perl.compile_pat {|\s{2,}|}) tier
    |> List.filter ~f:(fun s -> not (String.is_empty (String.strip s)))
    |> List.map ~f:to_latex
  in
  String.concat ~sep:" \\quad " parts

let build_dfrac (rule : rule) : string =
  let conclusion_tex = to_latex rule.conclusion in
  let tier_texs = List.map rule.premise_tiers ~f:tier_to_latex in
  let numerator =
    match tier_texs with
    | [] -> "\\;"  (* axiom: thin space stands in for the empty premise *)
    | [t] -> t
    | first :: rest ->
      List.fold rest ~init:first ~f:(fun acc tier ->
        "\\dfrac{" ^ acc ^ "}{" ^ tier ^ "}")
  in
  "\\dfrac{" ^ numerator ^ "}{" ^ conclusion_tex ^ "}"

let katex_cache : (string, string) Hashtbl.t = Hashtbl.create (module String)

let katex_render (tex : string) : string =
  match Hashtbl.find katex_cache tex with
  | Some s -> s
  | None ->
    let temp_in = Stdlib.Filename.temp_file "render-tex-in" ".tex" in
    let temp_out = Stdlib.Filename.temp_file "render-tex-out" ".html" in
    write_file temp_in tex;
    let cmd =
      Printf.sprintf "katex < %s > %s"
        (Stdlib.Filename.quote temp_in) (Stdlib.Filename.quote temp_out)
    in
    let rc = Stdlib.Sys.command cmd in
    let html = if rc = 0 then read_file temp_out else "[katex render failed]" in
    Stdlib.Sys.remove temp_in;
    Stdlib.Sys.remove temp_out;
    Hashtbl.set katex_cache ~key:tex ~data:html;
    html

let render_rule_html (rule : rule) : string =
  let id = "rule-" ^ rule.name in
  let math = build_dfrac rule in
  let math_html = katex_render math in
  let name_html = katex_render (Printf.sprintf "\\text{%s}" rule.name) in
  Printf.sprintf
    "<figure class=\"rule\" id=\"%s\"><span class=\"rule-name\">%s</span>\
     <span class=\"rule-math\">%s</span></figure>"
    id name_html math_html

let chroma_style = "github"

let highlight_ocaml (code : string) : string =
  let temp_in = Stdlib.Filename.temp_file "render-in" ".ml" in
  let temp_out = Stdlib.Filename.temp_file "render-out" ".html" in
  write_file temp_in code;
  let cmd =
    Printf.sprintf
      "chroma --lexer=ocaml --formatter=html --html-only \
       --html-prevent-surrounding-pre --style=%s %s > %s"
      chroma_style
      (Stdlib.Filename.quote temp_in) (Stdlib.Filename.quote temp_out)
  in
  let rc = Stdlib.Sys.command cmd in
  let highlighted = if rc = 0 then read_file temp_out else code in
  Stdlib.Sys.remove temp_in;
  Stdlib.Sys.remove temp_out;
  highlighted

let chroma_css () : string =
  let temp_out = Stdlib.Filename.temp_file "render-css" ".css" in
  let cmd =
    Printf.sprintf
      "chroma --lexer=ocaml --formatter=html --html-styles --style=%s > %s"
      chroma_style (Stdlib.Filename.quote temp_out)
  in
  let rc = Stdlib.Sys.command cmd in
  let css = if rc = 0 then read_file temp_out else "" in
  Stdlib.Sys.remove temp_out;
  css

let block_lines_to_string (lines : Cmarkit.Block_line.t list) : string =
  List.map lines ~f:(fun (line, _meta) -> line)
  |> String.concat ~sep:"\n"

let block_lines_of_string (s : string) : Cmarkit.Block_line.t list =
  Cmarkit.Block_line.list_of_string s

let rec inline_text_first (inline : Cmarkit.Inline.t) : string =
  let open Cmarkit in
  match inline with
  | Inline.Text (s, _) -> s
  | Inline.Inlines ([], _) -> ""
  | Inline.Inlines (x :: _, _) -> inline_text_first x
  | Inline.Emphasis (e, _) -> inline_text_first (Inline.Emphasis.inline e)
  | Inline.Strong_emphasis (e, _) -> inline_text_first (Inline.Emphasis.inline e)
  | Inline.Link (l, _) -> inline_text_first (Inline.Link.text l)
  | _ -> ""

let starts_with_aside (block : Cmarkit.Block.t) : bool =
  let open Cmarkit in
  let first_para_text =
    let rec aux = function
      | Block.Paragraph (p, _) ->
        Some (inline_text_first (Block.Paragraph.inline p))
      | Block.Blocks (xs, _) ->
        (match xs with
         | x :: _ -> aux x
         | [] -> None)
      | _ -> None
    in
    aux block
  in
  match first_para_text with
  | Some s -> String.is_prefix (String.lstrip s) ~prefix:"Aside:"
  | None -> false

let strip_aside_inline (inline : Cmarkit.Inline.t) : Cmarkit.Inline.t =
  let open Cmarkit in
  let done_ = ref false in
  let rec aux inline =
    if !done_ then inline
    else match inline with
    | Inline.Text (s, meta) ->
      let trimmed = String.lstrip s in
      if String.is_prefix trimmed ~prefix:"Aside:" then begin
        done_ := true;
        let after = String.drop_prefix trimmed (String.length "Aside:") |> String.lstrip in
        Inline.Text (after, meta)
      end else inline
    | Inline.Inlines (xs, meta) ->
      let new_xs = List.map xs ~f:aux in
      Inline.Inlines (new_xs, meta)
    | _ -> inline
  in
  aux inline

let strip_aside_block (block : Cmarkit.Block.t) : Cmarkit.Block.t =
  let open Cmarkit in
  let rec aux block =
    if not (starts_with_aside block) then block
    else match block with
    | Block.Paragraph (p, meta) ->
      let new_inline = strip_aside_inline (Block.Paragraph.inline p) in
      Block.Paragraph (Block.Paragraph.make new_inline, meta)
    | Block.Blocks (xs, meta) ->
      let new_xs = match xs with
        | x :: rest -> aux x :: rest
        | [] -> []
      in
      Block.Blocks (new_xs, meta)
    | other -> other
  in
  aux block

let render_aside (mapper : Cmarkit.Mapper.t) (inner_block : Cmarkit.Block.t) : string =
  let stripped = strip_aside_block inner_block in
  let inner_doc = Cmarkit.Doc.make stripped in
  let transformed = Cmarkit.Mapper.map_doc mapper inner_doc in
  let inner_html = Cmarkit_html.of_doc ~safe:false transformed in
  "<details class=\"aside\"><summary>Aside</summary><div class=\"aside-body\">" ^ inner_html ^ "</div></details>"

let widget_re = Re.Perl.compile_pat {|<!--\s*widget:\s*([a-z0-9-]+)\s*-->|}

let widget_marker_of_html_block (lines : Cmarkit.Block_line.t list) : string option =
  let raw = block_lines_to_string lines |> String.strip in
  match Re.exec_opt widget_re raw with
  | Some g -> Some (Re.Group.get g 1)
  | None -> None

let read_widget_file name suffix =
  let path = Printf.sprintf "blog/widgets/%s/widget.%s" name suffix in
  if Stdlib.Sys.file_exists path then Some (read_file path) else None

let widget_css : string list ref = ref []
let widget_js : string list ref = ref []

let render_widget name : string =
  let html =
    match read_widget_file name "html" with
    | Some s -> s
    | None ->
      Printf.sprintf
        "<div data-widget=\"%s\">[widget %s: stub, not yet implemented]</div>"
        name name
  in
  (match read_widget_file name "css" with
   | Some s -> widget_css := s :: !widget_css
   | None -> ());
  (match read_widget_file name "js" with
   | Some s -> widget_js := s :: !widget_js
   | None -> ());
  html

let reset_widgets () =
  widget_css := [];
  widget_js := []

let slug_re = Re.Perl.compile_pat {|[^a-z0-9]+|}

let slugify (s : string) : string =
  let lower = String.lowercase s in
  let with_dashes = Re.replace slug_re ~f:(fun _ -> "-") lower in
  let trimmed =
    let len = String.length with_dashes in
    let start = ref 0 in
    while !start < len && Char.equal with_dashes.[!start] '-' do Int.incr start done;
    let stop = ref (len - 1) in
    while !stop >= !start && Char.equal with_dashes.[!stop] '-' do Int.decr stop done;
    if !stop < !start then ""
    else String.sub with_dashes ~pos:!start ~len:(!stop - !start + 1)
  in
  trimmed

let rec inline_text (inline : Cmarkit.Inline.t) : string =
  let open Cmarkit in
  match inline with
  | Inline.Text (s, _) -> s
  | Inline.Inlines (xs, _) -> String.concat ~sep:"" (List.map xs ~f:inline_text)
  | Inline.Code_span (cs, _) ->
    let lines = Inline.Code_span.code cs in
    lines
  | Inline.Emphasis (e, _) -> inline_text (Inline.Emphasis.inline e)
  | Inline.Strong_emphasis (e, _) -> inline_text (Inline.Emphasis.inline e)
  | Inline.Link (l, _) -> inline_text (Inline.Link.text l)
  | Inline.Image (l, _) -> inline_text (Inline.Link.text l)
  | Inline.Break _ -> " "
  | Inline.Raw_html _ -> ""
  | Inline.Autolink _ -> ""
  | _ -> ""

let toc_entries : (int * string * string) list ref = ref []
let seen_slugs : (string, int) Hashtbl.t = Hashtbl.create (module String)

let reset_toc () =
  toc_entries := [];
  Hashtbl.clear seen_slugs

let unique_slug base =
  match Hashtbl.find seen_slugs base with
  | None -> Hashtbl.set seen_slugs ~key:base ~data:1; base
  | Some n ->
    Hashtbl.set seen_slugs ~key:base ~data:(n + 1);
    base ^ "-" ^ Int.to_string (n + 1)

let push_toc ~level ~text ~slug =
  toc_entries := (level, text, slug) :: !toc_entries

let render_toc () : string =
  let entries = List.rev !toc_entries in
  let buf = Buffer.create 1024 in
  Buffer.add_string buf
    "<nav class=\"toc\" aria-label=\"Table of contents\"><details><summary>Contents</summary>";
  let min_level =
    List.fold entries ~init:Int.max_value ~f:(fun acc (lvl, _, _) ->
      Int.min acc lvl)
  in
  let entries =
    List.filter entries ~f:(fun (lvl, _, _) -> lvl <> min_level)
  in
  let min_level =
    List.fold entries ~init:Int.max_value ~f:(fun acc (lvl, _, _) ->
      Int.min acc lvl)
  in
  let entries =
    List.map entries ~f:(fun (lvl, t, s) ->
      (lvl - min_level + 1, t, s))
  in
  let escape_text text =
    let b = Buffer.create (String.length text) in
    Cmarkit_html.buffer_add_html_escaped_string b text;
    Buffer.contents b
  in
  let stack = ref [] in
  List.iter entries ~f:(fun (level, text, slug) ->
    while (match !stack with (top, _) :: _ -> top > level | [] -> false) do
      let (_, tag) = List.hd_exn !stack in
      Buffer.add_string buf ("</li></" ^ tag ^ ">");
      stack := List.tl_exn !stack
    done;
    (match !stack with
     | (top, _) :: _ when top = level -> Buffer.add_string buf "</li>"
     | _ ->
       let tag = "ul" in
       Buffer.add_string buf ("<" ^ tag ^ ">");
       stack := (level, tag) :: !stack);
    Buffer.add_string buf
      (Printf.sprintf "<li><a href=\"#%s\">%s</a>" slug (escape_text text)));
  List.iter !stack ~f:(fun (_, tag) -> Buffer.add_string buf ("</li></" ^ tag ^ ">"));
  Buffer.add_string buf "</details></nav>";
  Buffer.contents buf

let block_mapper mapper block =
  let open Cmarkit in
  match block with
  | Block.Block_quote (bq, meta)
    when starts_with_aside (Block.Block_quote.block bq) ->
    let html = render_aside mapper (Block.Block_quote.block bq) in
    Mapper.ret (Block.Html_block (block_lines_of_string html, meta))
  | Block.Html_block (lines, meta) ->
    (match widget_marker_of_html_block lines with
     | Some name ->
       let html = render_widget name in
       Mapper.ret (Block.Html_block (block_lines_of_string html, meta))
     | None -> Mapper.default)
  | Block.Heading (h, meta) ->
    let level = Block.Heading.level h in
    let text = inline_text (Block.Heading.inline h) in
    let slug = unique_slug (slugify text) in
    push_toc ~level ~text ~slug;
    (* cmarkit's HTML renderer has no hook for emitting id attributes. *)
    let escaped =
      let buf = Buffer.create (String.length text) in
      Cmarkit_html.buffer_add_html_escaped_string buf text;
      Buffer.contents buf
    in
    let html =
      if level = 1 then
        Printf.sprintf "<h%d id=\"%s\">%s</h%d>" level slug escaped level
      else
        Printf.sprintf
          "<h%d id=\"%s\"><a class=\"heading-anchor\" href=\"#%s\">%s</a></h%d>"
          level slug slug escaped level
    in
    Mapper.ret (Block.Html_block (block_lines_of_string html, meta))
  | Block.Code_block (cb, meta) ->
    let info_string =
      Option.map (Block.Code_block.info_string cb) ~f:(fun (s, _meta) -> s)
    in
    let raw = block_lines_to_string (Block.Code_block.code cb) in
    (match info_string with
     | None | Some "" ->
       let lines = String.split_lines raw in
       (match parse_rule lines with
        | Some rule ->
          let html = render_rule_html rule in
          Mapper.ret (Block.Html_block (block_lines_of_string html, meta))
        | None -> Mapper.default)
     | Some "ocaml" ->
       let highlighted = highlight_ocaml raw in
       (* chroma v2.26+ scopes its selectors under .chroma.light / .chroma.dark. *)
       let html =
         "<pre class=\"chroma light\"><code class=\"language-ocaml\">"
         ^ highlighted ^ "</code></pre>"
       in
       Mapper.ret (Block.Html_block (block_lines_of_string html, meta))
     | Some _ -> Mapper.default)
  | _ -> Mapper.default

let url_re =
  Re.Perl.compile_pat
    {|https?://[A-Za-z0-9._~:/?#@!$&'*+,;=%-]+|}

(* Strip trailing sentence punctuation so "see https://x.org." does not link the dot. *)
let trim_url_trailing_punct (url : string) : int =
  let trailing = Set.of_list (module Char) ['.'; ','; ';'; ':'; '!'; '?'; ')'; ']'] in
  let len = String.length url in
  let i = ref (len - 1) in
  while !i >= 0 && Set.mem trailing url.[!i] do Int.decr i done;
  !i + 1

let autolink_text (text : string) (meta : Cmarkit.Meta.t)
    : Cmarkit.Inline.t list =
  let open Cmarkit in
  let matches = Re.all url_re text in
  if List.is_empty matches then [Inline.Text (text, meta)]
  else begin
    let parts = ref [] in
    let prev_end = ref 0 in
    List.iter matches ~f:(fun m ->
      let s = Re.Group.start m 0 in
      let e = Re.Group.stop m 0 in
      let raw = String.sub text ~pos:s ~len:(e - s) in
      let url_len = trim_url_trailing_punct raw in
      let url = String.sub raw ~pos:0 ~len:url_len in
      let actual_end = s + url_len in
      if s > !prev_end then
        parts :=
          Inline.Text
            ( String.sub text ~pos:!prev_end ~len:(s - !prev_end), meta )
          :: !parts;
      let autolink = Inline.Autolink.make (url, meta) in
      parts := Inline.Autolink (autolink, meta) :: !parts;
      prev_end := actual_end);
    if !prev_end < String.length text then
      parts :=
        Inline.Text
          ( String.sub text ~pos:!prev_end
              ~len:(String.length text - !prev_end), meta )
        :: !parts;
    List.rev !parts
  end

let inline_mapper _mapper inline =
  let open Cmarkit in
  match inline with
  | Inline.Text (s, meta) ->
    let parts = autolink_text s meta in
    (match parts with
     | [Inline.Text _] -> Mapper.default
     | _ -> Mapper.ret (Inline.Inlines (parts, meta)))
  | Inline.Break (b, meta) ->
    (match Inline.Break.type' b with
     | `Soft -> Mapper.ret (Inline.Break (Inline.Break.make `Hard, meta))
     | `Hard -> Mapper.default)
  | _ -> Mapper.default

let transform (doc : Cmarkit.Doc.t) : Cmarkit.Doc.t =
  let m =
    Cmarkit.Mapper.make ~block:block_mapper ~inline:inline_mapper ()
  in
  Cmarkit.Mapper.map_doc m doc

let baseline_css = {|
@font-face { font-family: 'Century Schoolbook'; src: url('/static/CenturySchL-Roma.woff2') format('woff2'), url('/static/CenturySchL-Roma.woff') format('woff'), url('/static/CenturySchL-Roma.ttf') format('truetype'); font-weight: normal; font-style: normal; }
@font-face { font-family: 'Century Schoolbook'; src: url('/static/CenturySchL-Bold.woff2') format('woff2'), url('/static/CenturySchL-Bold.woff') format('woff'), url('/static/CenturySchL-Bold.ttf') format('truetype'); font-weight: bold; font-style: normal; }
@font-face { font-family: 'Century Schoolbook'; src: url('/static/CenturySchL-Ital.woff2') format('woff2'), url('/static/CenturySchL-Ital.woff') format('woff'), url('/static/CenturySchL-Ital.ttf') format('truetype'); font-weight: normal; font-style: italic; }
@font-face { font-family: 'Century Schoolbook'; src: url('/static/CenturySchL-BoldItal.woff2') format('woff2'), url('/static/CenturySchL-BoldItal.woff') format('woff'), url('/static/CenturySchL-BoldItal.ttf') format('truetype'); font-weight: bold; font-style: italic; }
@font-face { font-family: 'DejaVu Sans Mono'; src: url('/static/DejaVuSansMono.woff2') format('woff2'), url('/static/DejaVuSansMono.woff') format('woff'), url('/static/DejaVuSansMono.ttf') format('truetype'); font-weight: normal; font-style: normal; }
@font-face { font-family: 'DejaVu Sans Mono'; src: url('/static/DejaVuSansMono-Bold.woff2') format('woff2'), url('/static/DejaVuSansMono-Bold.woff') format('woff'), url('/static/DejaVuSansMono-Bold.ttf') format('truetype'); font-weight: bold; font-style: normal; }
body { max-width: 40em; margin: 2em auto; padding: 0 1em; font-family: 'Century Schoolbook', 'Century Schoolbook L', 'Times New Roman', Times, serif; color: #0f172a; }
@media screen and (max-width: 720px) { body { width: 80%; max-width: none; } }
h1 { text-align: center; }
h1, h2, h3, h4 { font-weight: 100; line-height: 1.2; }
pre, code { font-family: 'DejaVu Sans Mono', ui-monospace, monospace; font-size: 0.9em; }
pre code { font-size: 1em; }
pre { padding: 0; overflow-x: auto; background: transparent; }
pre.chroma.light { background: transparent; }
a:link { color: #9c27b0; text-decoration: none; }
a:visited { color: #610071; }
a:hover, a:active { color: #1565C0; text-decoration: underline; }
details.aside { margin: 1em 0; color: #334155; }
details.aside summary { cursor: pointer; font-style: italic; color: #334155; list-style: none; padding-left: 16px; padding-bottom: 0.3em; position: relative; }
details.aside summary::after { content: ''; position: absolute; left: 14px; right: 16px; bottom: 0; height: 2px; background: #cbd5e1; transition: background 0.15s; }
details.aside summary:hover { color: #1565C0; }
details.aside summary:hover::after { background: #1565C0; }
details.aside summary:hover::before { border-left-color: #1565C0; }
details.aside[open] summary:hover::before { border-left-color: transparent; border-top-color: #1565C0; }
details.aside summary::-webkit-details-marker { display: none; }
details.aside summary::before { content: ''; position: absolute; left: 1px; top: 0.45em; width: 0; height: 0; border-top: 4px solid transparent; border-bottom: 4px solid transparent; border-left: 5px solid #64748b; transition: border-color 0.15s; }
details.aside[open] summary::before { left: 0; top: 0.6em; border-top: 5px solid #64748b; border-bottom: none; border-left: 4px solid transparent; border-right: 4px solid transparent; }
details.aside[open] summary { margin-bottom: 0.4em; }
details.aside .aside-body { padding-left: 1em; margin: 0; }
figure.rule { margin: 1.5em 0; display: flex; align-items: center; gap: 1.5em; padding: 0.5em 0; max-width: 100%; }
figure.rule .rule-name { color: #334155; font-size: 0.9em; white-space: nowrap; flex-shrink: 0; }
figure.rule .rule-math { font-size: 1.05em; flex: 1; overflow-x: auto; min-width: 0; }
.heading-anchor:link, .heading-anchor:visited { color: inherit; text-decoration: none; }
.heading-anchor:hover { color: inherit; text-decoration: underline; text-decoration-color: #94a3b8; text-underline-offset: 4px; }
nav.toc { margin-bottom: 2em; line-height: 1.3; }
nav.toc details summary { cursor: pointer; font-weight: 100; font-size: 1.1em; list-style: none; padding-left: 1em; padding-bottom: 0.3em; position: relative; }
nav.toc details summary::after { content: ''; position: absolute; left: 1em; right: 1em; bottom: 0; height: 2px; background: #cbd5e1; transition: background 0.15s; }
nav.toc details summary:hover { color: #1565C0; }
nav.toc details summary:hover::after { background: #1565C0; }
nav.toc details summary:hover::before { border-left-color: #1565C0; }
nav.toc details[open] summary:hover::before { border-left-color: transparent; border-top-color: #1565C0; }
nav.toc details summary::-webkit-details-marker { display: none; }
nav.toc details summary::before { content: ''; position: absolute; left: 1px; top: 0.55em; width: 0; height: 0; border-top: 4px solid transparent; border-bottom: 4px solid transparent; border-left: 5px solid #64748b; transition: border-color 0.15s; }
nav.toc details[open] summary::before { left: 0; top: 0.7em; border-top: 5px solid #64748b; border-bottom: none; border-left: 4px solid transparent; border-right: 4px solid transparent; }
nav.toc details[open] summary { margin-bottom: 0.4em; }
nav.toc ol, nav.toc ul { margin: 0; padding-left: 1.5em; list-style: none; }
nav.toc > details > ul { padding-left: 1em; margin: 0; }
nav.toc li { margin: 0.1em 0; }
|}

let html_shell ~title ~body ~css ~katex_css ~js =
  Printf.sprintf
    {|<!doctype html>
<html lang="en">
<head>
<meta charset="utf-8">
<meta name="viewport" content="width=device-width, initial-scale=1">
<meta name="description" content="A tutorial on Hindley Milner type inference.">
<title>%s</title>
<style>%s</style>
<style>%s</style>
</head>
<body>
<main>
%s
</main>
<script>%s</script>
</body>
</html>
|}
    title katex_css css body js

let () =
  let src_path =
    if Array.length (Sys.get_argv ()) >= 2 then (Sys.get_argv ()).(1)
    else "hm_tutorial.md"
  in
  let out_dir = "dist" in
  let out_path = out_dir ^ "/hm_tutorial.html" in
  ensure_dir out_dir;
  let src = read_file src_path in
  let doc = Cmarkit.Doc.of_string src in
  reset_toc ();
  reset_widgets ();
  let doc = transform doc in
  let toc = render_toc () in
  let body = toc ^ "\n" ^ Cmarkit_html.of_doc ~safe:false doc in
  let widget_base_css =
    if Stdlib.Sys.file_exists "blog/widgets/_base.css" then read_file "blog/widgets/_base.css" else ""
  in
  let css =
    baseline_css ^ chroma_css () ^ widget_base_css ^ String.concat ~sep:"\n" (List.rev !widget_css)
  in
  let js = String.concat ~sep:"\n" (List.rev !widget_js) in
  let html =
    html_shell ~title:"Type Inference (Part 1)" ~body ~css ~katex_css:(katex_css_inline ()) ~js
  in
  write_file out_path html;
  print_endline ("wrote " ^ out_path)
