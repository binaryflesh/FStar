
open Prims
# 47 "FStar.Syntax.Print.fst"
let lid_to_string : FStar_Ident.lid  ->  Prims.string = (fun l -> l.FStar_Ident.str)

# 49 "FStar.Syntax.Print.fst"
let fv_to_string : FStar_Syntax_Syntax.fv  ->  Prims.string = (fun fv -> (lid_to_string fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v))

# 51 "FStar.Syntax.Print.fst"
let bv_to_string : FStar_Syntax_Syntax.bv  ->  Prims.string = (fun bv -> (let _119_7 = (FStar_Util.string_of_int bv.FStar_Syntax_Syntax.index)
in (Prims.strcat (Prims.strcat bv.FStar_Syntax_Syntax.ppname.FStar_Ident.idText "#") _119_7)))

# 53 "FStar.Syntax.Print.fst"
let nm_to_string : FStar_Syntax_Syntax.bv  ->  Prims.string = (fun bv -> if (FStar_ST.read FStar_Options.print_real_names) then begin
(bv_to_string bv)
end else begin
bv.FStar_Syntax_Syntax.ppname.FStar_Ident.idText
end)

# 58 "FStar.Syntax.Print.fst"
let db_to_string : FStar_Syntax_Syntax.bv  ->  Prims.string = (fun bv -> (let _119_12 = (FStar_Util.string_of_int bv.FStar_Syntax_Syntax.index)
in (Prims.strcat (Prims.strcat bv.FStar_Syntax_Syntax.ppname.FStar_Ident.idText "@") _119_12)))

# 61 "FStar.Syntax.Print.fst"
let infix_prim_ops : (FStar_Ident.lident * Prims.string) Prims.list = ((FStar_Syntax_Const.op_Addition, "+"))::((FStar_Syntax_Const.op_Subtraction, "-"))::((FStar_Syntax_Const.op_Multiply, "*"))::((FStar_Syntax_Const.op_Division, "/"))::((FStar_Syntax_Const.op_Eq, "="))::((FStar_Syntax_Const.op_ColonEq, ":="))::((FStar_Syntax_Const.op_notEq, "<>"))::((FStar_Syntax_Const.op_And, "&&"))::((FStar_Syntax_Const.op_Or, "||"))::((FStar_Syntax_Const.op_LTE, "<="))::((FStar_Syntax_Const.op_GTE, ">="))::((FStar_Syntax_Const.op_LT, "<"))::((FStar_Syntax_Const.op_GT, ">"))::((FStar_Syntax_Const.op_Modulus, "mod"))::((FStar_Syntax_Const.and_lid, "/\\"))::((FStar_Syntax_Const.or_lid, "\\/"))::((FStar_Syntax_Const.imp_lid, "==>"))::((FStar_Syntax_Const.iff_lid, "<==>"))::((FStar_Syntax_Const.precedes_lid, "<<"))::((FStar_Syntax_Const.eq2_lid, "=="))::[]

# 84 "FStar.Syntax.Print.fst"
let unary_prim_ops : (FStar_Ident.lident * Prims.string) Prims.list = ((FStar_Syntax_Const.op_Negation, "not"))::((FStar_Syntax_Const.op_Minus, "-"))::((FStar_Syntax_Const.not_lid, "~"))::[]

# 90 "FStar.Syntax.Print.fst"
let is_prim_op = (fun ps f -> (match (f.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_fvar (fv) -> begin
(FStar_All.pipe_right ps (FStar_Util.for_some (FStar_Syntax_Syntax.fv_eq_lid fv)))
end
| _35_22 -> begin
false
end))

# 94 "FStar.Syntax.Print.fst"
let get_lid = (fun f -> (match (f.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_fvar (fv) -> begin
fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v
end
| _35_27 -> begin
(FStar_All.failwith "get_lid")
end))

# 98 "FStar.Syntax.Print.fst"
let is_infix_prim_op : FStar_Syntax_Syntax.term  ->  Prims.bool = (fun e -> (is_prim_op (Prims.fst (FStar_List.split infix_prim_ops)) e))

# 99 "FStar.Syntax.Print.fst"
let is_unary_prim_op : FStar_Syntax_Syntax.term  ->  Prims.bool = (fun e -> (is_prim_op (Prims.fst (FStar_List.split unary_prim_ops)) e))

# 101 "FStar.Syntax.Print.fst"
let quants : (FStar_Ident.lident * Prims.string) Prims.list = ((FStar_Syntax_Const.forall_lid, "forall"))::((FStar_Syntax_Const.exists_lid, "exists"))::[]

# 105 "FStar.Syntax.Print.fst"
type exp =
FStar_Syntax_Syntax.term

# 107 "FStar.Syntax.Print.fst"
let is_b2t : FStar_Syntax_Syntax.typ  ->  Prims.bool = (fun t -> (is_prim_op ((FStar_Syntax_Const.b2t_lid)::[]) t))

# 108 "FStar.Syntax.Print.fst"
let is_quant : FStar_Syntax_Syntax.typ  ->  Prims.bool = (fun t -> (is_prim_op (Prims.fst (FStar_List.split quants)) t))

# 109 "FStar.Syntax.Print.fst"
let is_ite : FStar_Syntax_Syntax.typ  ->  Prims.bool = (fun t -> (is_prim_op ((FStar_Syntax_Const.ite_lid)::[]) t))

# 111 "FStar.Syntax.Print.fst"
let is_lex_cons : exp  ->  Prims.bool = (fun f -> (is_prim_op ((FStar_Syntax_Const.lexcons_lid)::[]) f))

# 112 "FStar.Syntax.Print.fst"
let is_lex_top : exp  ->  Prims.bool = (fun f -> (is_prim_op ((FStar_Syntax_Const.lextop_lid)::[]) f))

# 113 "FStar.Syntax.Print.fst"
let is_inr = (fun _35_1 -> (match (_35_1) with
| FStar_Util.Inl (_35_37) -> begin
false
end
| FStar_Util.Inr (_35_40) -> begin
true
end))

# 114 "FStar.Syntax.Print.fst"
let filter_imp = (fun a -> (FStar_All.pipe_right a (FStar_List.filter (fun _35_2 -> (match (_35_2) with
| (_35_45, Some (FStar_Syntax_Syntax.Implicit (_35_47))) -> begin
false
end
| _35_52 -> begin
true
end)))))

# 115 "FStar.Syntax.Print.fst"
let rec reconstruct_lex : exp  ->  (FStar_Syntax_Syntax.term', FStar_Syntax_Syntax.term') FStar_Syntax_Syntax.syntax Prims.list Prims.option = (fun e -> (match ((let _119_35 = (FStar_Syntax_Subst.compress e)
in _119_35.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_app (f, args) -> begin
(
# 118 "FStar.Syntax.Print.fst"
let args = (filter_imp args)
in (
# 119 "FStar.Syntax.Print.fst"
let exps = (FStar_List.map Prims.fst args)
in if ((is_lex_cons f) && ((FStar_List.length exps) = 2)) then begin
(match ((let _119_36 = (FStar_List.nth exps 1)
in (reconstruct_lex _119_36))) with
| Some (xs) -> begin
(let _119_38 = (let _119_37 = (FStar_List.nth exps 0)
in (_119_37)::xs)
in Some (_119_38))
end
| None -> begin
None
end)
end else begin
None
end))
end
| _35_64 -> begin
if (is_lex_top e) then begin
Some ([])
end else begin
None
end
end))

# 128 "FStar.Syntax.Print.fst"
let rec find = (fun f l -> (match (l) with
| [] -> begin
(FStar_All.failwith "blah")
end
| hd::tl -> begin
if (f hd) then begin
hd
end else begin
(find f tl)
end
end))

# 132 "FStar.Syntax.Print.fst"
let find_lid : FStar_Ident.lident  ->  (FStar_Ident.lident * Prims.string) Prims.list  ->  Prims.string = (fun x xs -> (let _119_52 = (find (fun p -> (FStar_Ident.lid_equals x (Prims.fst p))) xs)
in (Prims.snd _119_52)))

# 135 "FStar.Syntax.Print.fst"
let infix_prim_op_to_string = (fun e -> (let _119_54 = (get_lid e)
in (find_lid _119_54 infix_prim_ops)))

# 136 "FStar.Syntax.Print.fst"
let unary_prim_op_to_string = (fun e -> (let _119_56 = (get_lid e)
in (find_lid _119_56 unary_prim_ops)))

# 137 "FStar.Syntax.Print.fst"
let quant_to_string = (fun t -> (let _119_58 = (get_lid t)
in (find_lid _119_58 quants)))

# 139 "FStar.Syntax.Print.fst"
let rec sli : FStar_Ident.lident  ->  Prims.string = (fun l -> if (FStar_ST.read FStar_Options.print_real_names) then begin
l.FStar_Ident.str
end else begin
l.FStar_Ident.ident.FStar_Ident.idText
end)

# 145 "FStar.Syntax.Print.fst"
let const_to_string : FStar_Const.sconst  ->  Prims.string = (fun x -> (match (x) with
| FStar_Const.Const_effect -> begin
"Effect"
end
| FStar_Const.Const_unit -> begin
"()"
end
| FStar_Const.Const_bool (b) -> begin
if b then begin
"true"
end else begin
"false"
end
end
| FStar_Const.Const_int32 (x) -> begin
(FStar_Util.string_of_int32 x)
end
| FStar_Const.Const_float (x) -> begin
(FStar_Util.string_of_float x)
end
| FStar_Const.Const_char (x) -> begin
(Prims.strcat (Prims.strcat "\'" (FStar_Util.string_of_char x)) "\'")
end
| FStar_Const.Const_string (bytes, _35_92) -> begin
(FStar_Util.format1 "\"%s\"" (FStar_Util.string_of_bytes bytes))
end
| FStar_Const.Const_bytearray (_35_96) -> begin
"<bytearray>"
end
| FStar_Const.Const_int (x) -> begin
x
end
| FStar_Const.Const_int64 (_35_101) -> begin
"<int64>"
end
| FStar_Const.Const_uint8 (_35_104) -> begin
"<uint8>"
end
| FStar_Const.Const_range (r) -> begin
(FStar_Range.string_of_range r)
end))

# 159 "FStar.Syntax.Print.fst"
let lbname_to_string : FStar_Syntax_Syntax.lbname  ->  Prims.string = (fun _35_3 -> (match (_35_3) with
| FStar_Util.Inl (l) -> begin
(bv_to_string l)
end
| FStar_Util.Inr (l) -> begin
(lid_to_string l.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v)
end))

# 163 "FStar.Syntax.Print.fst"
let tag_of_term : FStar_Syntax_Syntax.term  ->  Prims.string = (fun t -> (match (t.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_bvar (x) -> begin
(let _119_67 = (db_to_string x)
in (Prims.strcat "Tm_bvar: " _119_67))
end
| FStar_Syntax_Syntax.Tm_name (x) -> begin
(let _119_68 = (nm_to_string x)
in (Prims.strcat "Tm_name: " _119_68))
end
| FStar_Syntax_Syntax.Tm_fvar (x) -> begin
(let _119_69 = (lid_to_string x.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v)
in (Prims.strcat "Tm_fvar: " _119_69))
end
| FStar_Syntax_Syntax.Tm_uinst (_35_121) -> begin
"Tm_uinst"
end
| FStar_Syntax_Syntax.Tm_constant (_35_124) -> begin
"Tm_constant"
end
| FStar_Syntax_Syntax.Tm_type (_35_127) -> begin
"Tm_type"
end
| FStar_Syntax_Syntax.Tm_abs (_35_130) -> begin
"Tm_abs"
end
| FStar_Syntax_Syntax.Tm_arrow (_35_133) -> begin
"Tm_arrow"
end
| FStar_Syntax_Syntax.Tm_refine (_35_136) -> begin
"Tm_refine"
end
| FStar_Syntax_Syntax.Tm_app (_35_139) -> begin
"Tm_app"
end
| FStar_Syntax_Syntax.Tm_match (_35_142) -> begin
"Tm_match"
end
| FStar_Syntax_Syntax.Tm_ascribed (_35_145) -> begin
"Tm_ascribed"
end
| FStar_Syntax_Syntax.Tm_let (_35_148) -> begin
"Tm_let"
end
| FStar_Syntax_Syntax.Tm_uvar (_35_151) -> begin
"Tm_uvar"
end
| FStar_Syntax_Syntax.Tm_delayed (_35_154, m) -> begin
(match ((FStar_ST.read m)) with
| None -> begin
"Tm_delayed"
end
| Some (_35_160) -> begin
"Tm_delayed-resolved"
end)
end
| FStar_Syntax_Syntax.Tm_meta (_35_163) -> begin
"Tm_meta"
end
| FStar_Syntax_Syntax.Tm_unknown -> begin
"Tm_unknown"
end))

# 186 "FStar.Syntax.Print.fst"
let uvar_to_string = (fun u -> if (FStar_ST.read FStar_Options.hide_uvar_nums) then begin
"?"
end else begin
(let _119_74 = (let _119_73 = (FStar_Unionfind.uvar_id u)
in (FStar_All.pipe_right _119_73 FStar_Util.string_of_int))
in (Prims.strcat "?" _119_74))
end)

# 188 "FStar.Syntax.Print.fst"
let rec univ_to_string : FStar_Syntax_Syntax.universe  ->  Prims.string = (fun u -> (match ((FStar_Syntax_Subst.compress_univ u)) with
| FStar_Syntax_Syntax.U_unif (u) -> begin
(uvar_to_string u)
end
| FStar_Syntax_Syntax.U_name (x) -> begin
x.FStar_Ident.idText
end
| FStar_Syntax_Syntax.U_bvar (x) -> begin
(let _119_77 = (FStar_Util.string_of_int x)
in (Prims.strcat "@" _119_77))
end
| FStar_Syntax_Syntax.U_zero -> begin
"0"
end
| FStar_Syntax_Syntax.U_succ (u) -> begin
(let _119_78 = (univ_to_string u)
in (FStar_Util.format1 "(S %s)" _119_78))
end
| FStar_Syntax_Syntax.U_max (us) -> begin
(let _119_80 = (let _119_79 = (FStar_List.map univ_to_string us)
in (FStar_All.pipe_right _119_79 (FStar_String.concat ", ")))
in (FStar_Util.format1 "(max %s)" _119_80))
end
| FStar_Syntax_Syntax.U_unknown -> begin
"unknown"
end))

# 197 "FStar.Syntax.Print.fst"
let univs_to_string : FStar_Syntax_Syntax.universe Prims.list  ->  Prims.string = (fun us -> (let _119_83 = (FStar_List.map univ_to_string us)
in (FStar_All.pipe_right _119_83 (FStar_String.concat ", "))))

# 199 "FStar.Syntax.Print.fst"
let univ_names_to_string : FStar_Ident.ident Prims.list  ->  Prims.string = (fun us -> (let _119_87 = (FStar_List.map (fun x -> x.FStar_Ident.idText) us)
in (FStar_All.pipe_right _119_87 (FStar_String.concat ", "))))

# 201 "FStar.Syntax.Print.fst"
let qual_to_string : FStar_Syntax_Syntax.qualifier  ->  Prims.string = (fun _35_4 -> (match (_35_4) with
| FStar_Syntax_Syntax.Assumption -> begin
"assume"
end
| FStar_Syntax_Syntax.New -> begin
"new"
end
| FStar_Syntax_Syntax.Private -> begin
"private"
end
| FStar_Syntax_Syntax.Inline -> begin
"inline"
end
| FStar_Syntax_Syntax.Unfoldable -> begin
"unfoldable"
end
| FStar_Syntax_Syntax.Irreducible -> begin
"irreducible"
end
| FStar_Syntax_Syntax.Abstract -> begin
"abstract"
end
| FStar_Syntax_Syntax.Logic -> begin
"logic"
end
| FStar_Syntax_Syntax.TotalEffect -> begin
"total"
end
| FStar_Syntax_Syntax.DefaultEffect (None) -> begin
"no default"
end
| FStar_Syntax_Syntax.DefaultEffect (Some (l)) -> begin
(let _119_90 = (lid_to_string l)
in (FStar_Util.format1 "default %s" _119_90))
end
| FStar_Syntax_Syntax.Discriminator (l) -> begin
(let _119_91 = (lid_to_string l)
in (FStar_Util.format1 "(Discriminator %s)" _119_91))
end
| FStar_Syntax_Syntax.Projector (l, x) -> begin
(let _119_92 = (lid_to_string l)
in (FStar_Util.format2 "(Projector %s %s)" _119_92 x.FStar_Ident.idText))
end
| FStar_Syntax_Syntax.RecordType (fns) -> begin
(let _119_94 = (let _119_93 = (FStar_All.pipe_right fns (FStar_List.map lid_to_string))
in (FStar_All.pipe_right _119_93 (FStar_String.concat ", ")))
in (FStar_Util.format1 "(RecordType %s)" _119_94))
end
| FStar_Syntax_Syntax.RecordConstructor (fns) -> begin
(let _119_96 = (let _119_95 = (FStar_All.pipe_right fns (FStar_List.map lid_to_string))
in (FStar_All.pipe_right _119_95 (FStar_String.concat ", ")))
in (FStar_Util.format1 "(RecordConstructor %s)" _119_96))
end
| FStar_Syntax_Syntax.ExceptionConstructor -> begin
"ExceptionConstructor"
end
| FStar_Syntax_Syntax.HasMaskedEffect -> begin
"HasMaskedEffect"
end
| FStar_Syntax_Syntax.Effect -> begin
"Effect"
end))

# 220 "FStar.Syntax.Print.fst"
let quals_to_string : FStar_Syntax_Syntax.qualifier Prims.list  ->  Prims.string = (fun quals -> (match (quals) with
| [] -> begin
""
end
| _35_214 -> begin
(let _119_100 = (let _119_99 = (FStar_All.pipe_right quals (FStar_List.map qual_to_string))
in (FStar_All.pipe_right _119_99 (FStar_String.concat " ")))
in (Prims.strcat _119_100 " "))
end))

# 229 "FStar.Syntax.Print.fst"
let rec term_to_string : FStar_Syntax_Syntax.term  ->  Prims.string = (fun x -> (
# 230 "FStar.Syntax.Print.fst"
let x = (FStar_Syntax_Subst.compress x)
in (match (x.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_delayed (_35_218) -> begin
(FStar_All.failwith "impossible")
end
| FStar_Syntax_Syntax.Tm_app (_35_221, []) -> begin
(FStar_All.failwith "Empty args!")
end
| FStar_Syntax_Syntax.Tm_meta (t, FStar_Syntax_Syntax.Meta_pattern (ps)) -> begin
(
# 236 "FStar.Syntax.Print.fst"
let pats = (let _119_125 = (FStar_All.pipe_right ps (FStar_List.map (fun args -> (let _119_124 = (FStar_All.pipe_right args (FStar_List.map (fun _35_234 -> (match (_35_234) with
| (t, _35_233) -> begin
(term_to_string t)
end))))
in (FStar_All.pipe_right _119_124 (FStar_String.concat "; "))))))
in (FStar_All.pipe_right _119_125 (FStar_String.concat "\\/")))
in (let _119_126 = (term_to_string t)
in (FStar_Util.format2 "{:pattern %s} %s" pats _119_126)))
end
| FStar_Syntax_Syntax.Tm_meta (t, _35_238) -> begin
(term_to_string t)
end
| FStar_Syntax_Syntax.Tm_bvar (x) -> begin
(db_to_string x)
end
| FStar_Syntax_Syntax.Tm_name (x) -> begin
(nm_to_string x)
end
| FStar_Syntax_Syntax.Tm_fvar (f) -> begin
(fv_to_string f)
end
| FStar_Syntax_Syntax.Tm_uvar (u, _35_249) -> begin
(uvar_to_string u)
end
| FStar_Syntax_Syntax.Tm_constant (c) -> begin
(const_to_string c)
end
| FStar_Syntax_Syntax.Tm_type (u) -> begin
if (FStar_ST.read FStar_Options.print_universes) then begin
(let _119_127 = (univ_to_string u)
in (FStar_Util.format1 "Type(%s)" _119_127))
end else begin
"Type"
end
end
| FStar_Syntax_Syntax.Tm_arrow (bs, c) -> begin
(let _119_129 = (binders_to_string " -> " bs)
in (let _119_128 = (comp_to_string c)
in (FStar_Util.format2 "(%s -> %s)" _119_129 _119_128)))
end
| FStar_Syntax_Syntax.Tm_abs (bs, t2, lc) -> begin
(match (lc) with
| Some (l) when (FStar_ST.read FStar_Options.print_implicits) -> begin
(let _119_133 = (binders_to_string " " bs)
in (let _119_132 = (term_to_string t2)
in (let _119_131 = (let _119_130 = (l.FStar_Syntax_Syntax.comp ())
in (FStar_All.pipe_left comp_to_string _119_130))
in (FStar_Util.format3 "(fun %s -> (%s $$ %s))" _119_133 _119_132 _119_131))))
end
| _35_268 -> begin
(let _119_135 = (binders_to_string " " bs)
in (let _119_134 = (term_to_string t2)
in (FStar_Util.format2 "(fun %s -> %s)" _119_135 _119_134)))
end)
end
| FStar_Syntax_Syntax.Tm_refine (xt, f) -> begin
(let _119_138 = (bv_to_string xt)
in (let _119_137 = (FStar_All.pipe_right xt.FStar_Syntax_Syntax.sort term_to_string)
in (let _119_136 = (FStar_All.pipe_right f formula_to_string)
in (FStar_Util.format3 "(%s:%s{%s})" _119_138 _119_137 _119_136))))
end
| FStar_Syntax_Syntax.Tm_app (t, args) -> begin
(let _119_140 = (term_to_string t)
in (let _119_139 = (args_to_string args)
in (FStar_Util.format2 "(%s %s)" _119_140 _119_139)))
end
| FStar_Syntax_Syntax.Tm_let (lbs, e) -> begin
(let _119_142 = (lbs_to_string [] lbs)
in (let _119_141 = (term_to_string e)
in (FStar_Util.format2 "%s\nin\n%s" _119_142 _119_141)))
end
| FStar_Syntax_Syntax.Tm_ascribed (e, t, _35_284) -> begin
(let _119_144 = (term_to_string e)
in (let _119_143 = (term_to_string t)
in (FStar_Util.format2 "(%s : %s)" _119_144 _119_143)))
end
| FStar_Syntax_Syntax.Tm_match (head, branches) -> begin
(let _119_152 = (term_to_string head)
in (let _119_151 = (let _119_150 = (FStar_All.pipe_right branches (FStar_List.map (fun _35_294 -> (match (_35_294) with
| (p, wopt, e) -> begin
(let _119_149 = (FStar_All.pipe_right p pat_to_string)
in (let _119_148 = (match (wopt) with
| None -> begin
""
end
| Some (w) -> begin
(let _119_146 = (FStar_All.pipe_right w term_to_string)
in (FStar_Util.format1 "when %s" _119_146))
end)
in (let _119_147 = (FStar_All.pipe_right e term_to_string)
in (FStar_Util.format3 "%s %s -> %s" _119_149 _119_148 _119_147))))
end))))
in (FStar_Util.concat_l "\n\t|" _119_150))
in (FStar_Util.format2 "(match %s with\n\t| %s)" _119_152 _119_151)))
end
| FStar_Syntax_Syntax.Tm_uinst (t, us) -> begin
if (FStar_ST.read FStar_Options.print_universes) then begin
(let _119_154 = (term_to_string t)
in (let _119_153 = (univs_to_string us)
in (FStar_Util.format2 "%s<%s>" _119_154 _119_153)))
end else begin
(term_to_string t)
end
end
| _35_303 -> begin
(tag_of_term x)
end)))
and pat_to_string : FStar_Syntax_Syntax.pat  ->  Prims.string = (fun x -> (match (x.FStar_Syntax_Syntax.v) with
| FStar_Syntax_Syntax.Pat_cons (l, pats) -> begin
(let _119_159 = (fv_to_string l)
in (let _119_158 = (let _119_157 = (FStar_List.map (fun _35_311 -> (match (_35_311) with
| (x, b) -> begin
(
# 274 "FStar.Syntax.Print.fst"
let p = (pat_to_string x)
in if b then begin
(Prims.strcat "#" p)
end else begin
p
end)
end)) pats)
in (FStar_All.pipe_right _119_157 (FStar_String.concat " ")))
in (FStar_Util.format2 "(%s %s)" _119_159 _119_158)))
end
| FStar_Syntax_Syntax.Pat_dot_term (x, _35_315) -> begin
(let _119_160 = (bv_to_string x)
in (FStar_Util.format1 ".%s" _119_160))
end
| FStar_Syntax_Syntax.Pat_var (x) -> begin
(bv_to_string x)
end
| FStar_Syntax_Syntax.Pat_constant (c) -> begin
(const_to_string c)
end
| FStar_Syntax_Syntax.Pat_wild (x) -> begin
if (FStar_ST.read FStar_Options.print_real_names) then begin
(let _119_161 = (bv_to_string x)
in (Prims.strcat "Pat_wild " _119_161))
end else begin
"_"
end
end
| FStar_Syntax_Syntax.Pat_disj (ps) -> begin
(let _119_162 = (FStar_List.map pat_to_string ps)
in (FStar_Util.concat_l " | " _119_162))
end))
and lbs_to_string : FStar_Syntax_Syntax.qualifier Prims.list  ->  FStar_Syntax_Syntax.letbindings  ->  Prims.string = (fun quals lbs -> (
# 283 "FStar.Syntax.Print.fst"
let lbs = if (FStar_ST.read FStar_Options.print_universes) then begin
(let _119_168 = (FStar_All.pipe_right (Prims.snd lbs) (FStar_List.map (fun lb -> (
# 285 "FStar.Syntax.Print.fst"
let _35_331 = (let _119_166 = (FStar_Syntax_Util.mk_conj lb.FStar_Syntax_Syntax.lbtyp lb.FStar_Syntax_Syntax.lbdef)
in (FStar_Syntax_Subst.open_univ_vars lb.FStar_Syntax_Syntax.lbunivs _119_166))
in (match (_35_331) with
| (us, td) -> begin
(
# 286 "FStar.Syntax.Print.fst"
let _35_349 = (match ((let _119_167 = (FStar_Syntax_Subst.compress td)
in _119_167.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_app (_35_333, (t, _35_340)::(d, _35_336)::[]) -> begin
(t, d)
end
| _35_346 -> begin
(FStar_All.failwith "Impossibe")
end)
in (match (_35_349) with
| (t, d) -> begin
(
# 289 "FStar.Syntax.Print.fst"
let _35_350 = lb
in {FStar_Syntax_Syntax.lbname = _35_350.FStar_Syntax_Syntax.lbname; FStar_Syntax_Syntax.lbunivs = us; FStar_Syntax_Syntax.lbtyp = t; FStar_Syntax_Syntax.lbeff = _35_350.FStar_Syntax_Syntax.lbeff; FStar_Syntax_Syntax.lbdef = d})
end))
end)))))
in ((Prims.fst lbs), _119_168))
end else begin
lbs
end
in (let _119_178 = (quals_to_string quals)
in (let _119_177 = (let _119_176 = (FStar_All.pipe_right (Prims.snd lbs) (FStar_List.map (fun lb -> (let _119_175 = (lbname_to_string lb.FStar_Syntax_Syntax.lbname)
in (let _119_174 = if (FStar_ST.read FStar_Options.print_universes) then begin
(let _119_171 = (let _119_170 = (univ_names_to_string lb.FStar_Syntax_Syntax.lbunivs)
in (Prims.strcat "<" _119_170))
in (Prims.strcat _119_171 ">"))
end else begin
""
end
in (let _119_173 = (term_to_string lb.FStar_Syntax_Syntax.lbtyp)
in (let _119_172 = (FStar_All.pipe_right lb.FStar_Syntax_Syntax.lbdef term_to_string)
in (FStar_Util.format4 "%s %s : %s = %s" _119_175 _119_174 _119_173 _119_172))))))))
in (FStar_Util.concat_l "\n and " _119_176))
in (FStar_Util.format3 "%slet %s %s" _119_178 (if (Prims.fst lbs) then begin
"rec"
end else begin
""
end) _119_177)))))
and lcomp_to_string : FStar_Syntax_Syntax.lcomp  ->  Prims.string = (fun lc -> (let _119_181 = (sli lc.FStar_Syntax_Syntax.eff_name)
in (let _119_180 = (term_to_string lc.FStar_Syntax_Syntax.res_typ)
in (FStar_Util.format2 "%s %s" _119_181 _119_180))))
and imp_to_string : Prims.string  ->  FStar_Syntax_Syntax.arg_qualifier Prims.option  ->  Prims.string = (fun s _35_5 -> (match (_35_5) with
| Some (FStar_Syntax_Syntax.Implicit (false)) -> begin
(Prims.strcat "#" s)
end
| Some (FStar_Syntax_Syntax.Implicit (true)) -> begin
(Prims.strcat "#." s)
end
| Some (FStar_Syntax_Syntax.Equality) -> begin
(Prims.strcat "=" s)
end
| _35_366 -> begin
s
end))
and binder_to_string' : Prims.bool  ->  (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.arg_qualifier Prims.option)  ->  Prims.string = (fun is_arrow b -> (
# 321 "FStar.Syntax.Print.fst"
let _35_371 = b
in (match (_35_371) with
| (a, imp) -> begin
if (FStar_Syntax_Syntax.is_null_binder b) then begin
(term_to_string a.FStar_Syntax_Syntax.sort)
end else begin
if ((not (is_arrow)) && (not ((FStar_ST.read FStar_Options.print_bound_var_types)))) then begin
(let _119_186 = (nm_to_string a)
in (imp_to_string _119_186 imp))
end else begin
(let _119_190 = (let _119_189 = (let _119_187 = (nm_to_string a)
in (Prims.strcat _119_187 ":"))
in (let _119_188 = (term_to_string a.FStar_Syntax_Syntax.sort)
in (Prims.strcat _119_189 _119_188)))
in (imp_to_string _119_190 imp))
end
end
end)))
and binder_to_string : (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.arg_qualifier Prims.option)  ->  Prims.string = (fun b -> (binder_to_string' false b))
and arrow_binder_to_string : (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.arg_qualifier Prims.option)  ->  Prims.string = (fun b -> (binder_to_string' true b))
and binders_to_string : Prims.string  ->  FStar_Syntax_Syntax.binders  ->  Prims.string = (fun sep bs -> (
# 332 "FStar.Syntax.Print.fst"
let bs = if (FStar_ST.read FStar_Options.print_implicits) then begin
bs
end else begin
(filter_imp bs)
end
in if (sep = " -> ") then begin
(let _119_195 = (FStar_All.pipe_right bs (FStar_List.map arrow_binder_to_string))
in (FStar_All.pipe_right _119_195 (FStar_String.concat sep)))
end else begin
(let _119_196 = (FStar_All.pipe_right bs (FStar_List.map binder_to_string))
in (FStar_All.pipe_right _119_196 (FStar_String.concat sep)))
end))
and arg_to_string : (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.arg_qualifier Prims.option)  ->  Prims.string = (fun _35_6 -> (match (_35_6) with
| (a, imp) -> begin
(let _119_198 = (term_to_string a)
in (imp_to_string _119_198 imp))
end))
and args_to_string : FStar_Syntax_Syntax.args  ->  Prims.string = (fun args -> (
# 341 "FStar.Syntax.Print.fst"
let args = if (FStar_ST.read FStar_Options.print_implicits) then begin
args
end else begin
(filter_imp args)
end
in (let _119_200 = (FStar_All.pipe_right args (FStar_List.map arg_to_string))
in (FStar_All.pipe_right _119_200 (FStar_String.concat " ")))))
and comp_to_string : FStar_Syntax_Syntax.comp  ->  Prims.string = (fun c -> (match (c.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Total (t) -> begin
(match ((let _119_202 = (FStar_Syntax_Subst.compress t)
in _119_202.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_type (_35_387) when (not ((FStar_ST.read FStar_Options.print_implicits))) -> begin
(term_to_string t)
end
| _35_390 -> begin
(let _119_203 = (term_to_string t)
in (FStar_Util.format1 "Tot %s" _119_203))
end)
end
| FStar_Syntax_Syntax.GTotal (t) -> begin
(match ((let _119_204 = (FStar_Syntax_Subst.compress t)
in _119_204.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_type (_35_394) when (not ((FStar_ST.read FStar_Options.print_implicits))) -> begin
(term_to_string t)
end
| _35_397 -> begin
(let _119_205 = (term_to_string t)
in (FStar_Util.format1 "GTot %s" _119_205))
end)
end
| FStar_Syntax_Syntax.Comp (c) -> begin
(
# 357 "FStar.Syntax.Print.fst"
let basic = if ((FStar_All.pipe_right c.FStar_Syntax_Syntax.flags (FStar_Util.for_some (fun _35_7 -> (match (_35_7) with
| FStar_Syntax_Syntax.TOTAL -> begin
true
end
| _35_403 -> begin
false
end)))) && (not ((FStar_ST.read FStar_Options.print_effect_args)))) then begin
(let _119_207 = (term_to_string c.FStar_Syntax_Syntax.result_typ)
in (FStar_Util.format1 "Tot %s" _119_207))
end else begin
if (((not ((FStar_ST.read FStar_Options.print_effect_args))) && (not ((FStar_ST.read FStar_Options.print_implicits)))) && (FStar_Ident.lid_equals c.FStar_Syntax_Syntax.effect_name FStar_Syntax_Const.effect_ML_lid)) then begin
(term_to_string c.FStar_Syntax_Syntax.result_typ)
end else begin
if ((not ((FStar_ST.read FStar_Options.print_effect_args))) && (FStar_All.pipe_right c.FStar_Syntax_Syntax.flags (FStar_Util.for_some (fun _35_8 -> (match (_35_8) with
| FStar_Syntax_Syntax.MLEFFECT -> begin
true
end
| _35_407 -> begin
false
end))))) then begin
(let _119_209 = (term_to_string c.FStar_Syntax_Syntax.result_typ)
in (FStar_Util.format1 "ALL %s" _119_209))
end else begin
if (FStar_ST.read FStar_Options.print_effect_args) then begin
(let _119_213 = (sli c.FStar_Syntax_Syntax.effect_name)
in (let _119_212 = (term_to_string c.FStar_Syntax_Syntax.result_typ)
in (let _119_211 = (let _119_210 = (FStar_All.pipe_right c.FStar_Syntax_Syntax.effect_args (FStar_List.map arg_to_string))
in (FStar_All.pipe_right _119_210 (FStar_String.concat ", ")))
in (FStar_Util.format3 "%s (%s) %s" _119_213 _119_212 _119_211))))
end else begin
(let _119_215 = (sli c.FStar_Syntax_Syntax.effect_name)
in (let _119_214 = (term_to_string c.FStar_Syntax_Syntax.result_typ)
in (FStar_Util.format2 "%s (%s)" _119_215 _119_214)))
end
end
end
end
in (
# 370 "FStar.Syntax.Print.fst"
let dec = (let _119_219 = (FStar_All.pipe_right c.FStar_Syntax_Syntax.flags (FStar_List.collect (fun _35_9 -> (match (_35_9) with
| FStar_Syntax_Syntax.DECREASES (e) -> begin
(let _119_218 = (let _119_217 = (term_to_string e)
in (FStar_Util.format1 " (decreases %s)" _119_217))
in (_119_218)::[])
end
| _35_413 -> begin
[]
end))))
in (FStar_All.pipe_right _119_219 (FStar_String.concat " ")))
in (FStar_Util.format2 "%s%s" basic dec)))
end))
and formula_to_string : FStar_Syntax_Syntax.term  ->  Prims.string = (fun phi -> (term_to_string phi))

# 389 "FStar.Syntax.Print.fst"
let tscheme_to_string : (FStar_Ident.ident Prims.list * FStar_Syntax_Syntax.term)  ->  Prims.string = (fun _35_418 -> (match (_35_418) with
| (us, t) -> begin
(let _119_224 = (univ_names_to_string us)
in (let _119_223 = (term_to_string t)
in (FStar_Util.format2 "<%s> %s" _119_224 _119_223)))
end))

# 391 "FStar.Syntax.Print.fst"
let eff_decl_to_string : FStar_Syntax_Syntax.eff_decl  ->  Prims.string = (fun ed -> (let _119_260 = (let _119_259 = (lid_to_string ed.FStar_Syntax_Syntax.mname)
in (let _119_258 = (let _119_257 = (univ_names_to_string ed.FStar_Syntax_Syntax.univs)
in (let _119_256 = (let _119_255 = (binders_to_string " " ed.FStar_Syntax_Syntax.binders)
in (let _119_254 = (let _119_253 = (term_to_string ed.FStar_Syntax_Syntax.signature)
in (let _119_252 = (let _119_251 = (tscheme_to_string ed.FStar_Syntax_Syntax.ret)
in (let _119_250 = (let _119_249 = (tscheme_to_string ed.FStar_Syntax_Syntax.bind_wp)
in (let _119_248 = (let _119_247 = (tscheme_to_string ed.FStar_Syntax_Syntax.bind_wlp)
in (let _119_246 = (let _119_245 = (tscheme_to_string ed.FStar_Syntax_Syntax.if_then_else)
in (let _119_244 = (let _119_243 = (tscheme_to_string ed.FStar_Syntax_Syntax.ite_wp)
in (let _119_242 = (let _119_241 = (tscheme_to_string ed.FStar_Syntax_Syntax.ite_wlp)
in (let _119_240 = (let _119_239 = (tscheme_to_string ed.FStar_Syntax_Syntax.wp_binop)
in (let _119_238 = (let _119_237 = (tscheme_to_string ed.FStar_Syntax_Syntax.wp_as_type)
in (let _119_236 = (let _119_235 = (tscheme_to_string ed.FStar_Syntax_Syntax.close_wp)
in (let _119_234 = (let _119_233 = (tscheme_to_string ed.FStar_Syntax_Syntax.assert_p)
in (let _119_232 = (let _119_231 = (tscheme_to_string ed.FStar_Syntax_Syntax.assume_p)
in (let _119_230 = (let _119_229 = (tscheme_to_string ed.FStar_Syntax_Syntax.null_wp)
in (let _119_228 = (let _119_227 = (tscheme_to_string ed.FStar_Syntax_Syntax.trivial)
in (_119_227)::[])
in (_119_229)::_119_228))
in (_119_231)::_119_230))
in (_119_233)::_119_232))
in (_119_235)::_119_234))
in (_119_237)::_119_236))
in (_119_239)::_119_238))
in (_119_241)::_119_240))
in (_119_243)::_119_242))
in (_119_245)::_119_244))
in (_119_247)::_119_246))
in (_119_249)::_119_248))
in (_119_251)::_119_250))
in (_119_253)::_119_252))
in (_119_255)::_119_254))
in (_119_257)::_119_256))
in (_119_259)::_119_258))
in (FStar_Util.format "new_effect { %s<%s> %s : %s \n\tret         = %s\n; bind_wp     = %s\n; bind_wlp    = %s\n; if_then_else= %s\n; ite_wp      = %s\n; ite_wlp     = %s\n; wp_binop    = %s\n; wp_as_type  = %s\n; close_wp    = %s\n; assert_p    = %s\n; assume_p    = %s\n; null_wp     = %s\n; trivial     = %s}\n" _119_260)))

# 424 "FStar.Syntax.Print.fst"
let rec sigelt_to_string : FStar_Syntax_Syntax.sigelt  ->  Prims.string = (fun x -> (match (x) with
| FStar_Syntax_Syntax.Sig_pragma (FStar_Syntax_Syntax.ResetOptions, _35_423) -> begin
"#reset-options"
end
| FStar_Syntax_Syntax.Sig_pragma (FStar_Syntax_Syntax.SetOptions (s), _35_429) -> begin
(FStar_Util.format1 "#set-options \"%s\"" s)
end
| FStar_Syntax_Syntax.Sig_inductive_typ (lid, univs, tps, k, _35_437, _35_439, quals, _35_442) -> begin
(let _119_265 = (quals_to_string quals)
in (let _119_264 = (binders_to_string " " tps)
in (let _119_263 = (term_to_string k)
in (FStar_Util.format4 "%s type %s %s : %s" _119_265 lid.FStar_Ident.str _119_264 _119_263))))
end
| FStar_Syntax_Syntax.Sig_datacon (lid, univs, t, _35_449, _35_451, _35_453, _35_455, _35_457) -> begin
if (FStar_ST.read FStar_Options.print_universes) then begin
(
# 435 "FStar.Syntax.Print.fst"
let _35_462 = (FStar_Syntax_Subst.open_univ_vars univs t)
in (match (_35_462) with
| (univs, t) -> begin
(let _119_267 = (univ_names_to_string univs)
in (let _119_266 = (term_to_string t)
in (FStar_Util.format3 "datacon<%s> %s : %s" _119_267 lid.FStar_Ident.str _119_266)))
end))
end else begin
(let _119_268 = (term_to_string t)
in (FStar_Util.format2 "datacon %s : %s" lid.FStar_Ident.str _119_268))
end
end
| FStar_Syntax_Syntax.Sig_declare_typ (lid, univs, t, quals, _35_468) -> begin
(
# 439 "FStar.Syntax.Print.fst"
let _35_473 = (FStar_Syntax_Subst.open_univ_vars univs t)
in (match (_35_473) with
| (univs, t) -> begin
(let _119_272 = (quals_to_string quals)
in (let _119_271 = if (FStar_ST.read FStar_Options.print_universes) then begin
(let _119_269 = (univ_names_to_string univs)
in (FStar_Util.format1 "<%s>" _119_269))
end else begin
""
end
in (let _119_270 = (term_to_string t)
in (FStar_Util.format4 "%s val %s %s : %s" _119_272 lid.FStar_Ident.str _119_271 _119_270))))
end))
end
| FStar_Syntax_Syntax.Sig_assume (lid, f, _35_477, _35_479) -> begin
(let _119_273 = (term_to_string f)
in (FStar_Util.format2 "val %s : %s" lid.FStar_Ident.str _119_273))
end
| FStar_Syntax_Syntax.Sig_let (lbs, _35_484, _35_486, qs) -> begin
(lbs_to_string qs lbs)
end
| FStar_Syntax_Syntax.Sig_main (e, _35_492) -> begin
(let _119_274 = (term_to_string e)
in (FStar_Util.format1 "let _ = %s" _119_274))
end
| FStar_Syntax_Syntax.Sig_bundle (ses, _35_497, _35_499, _35_501) -> begin
(let _119_275 = (FStar_List.map sigelt_to_string ses)
in (FStar_All.pipe_right _119_275 (FStar_String.concat "\n")))
end
| FStar_Syntax_Syntax.Sig_new_effect (ed, _35_506) -> begin
(eff_decl_to_string ed)
end
| FStar_Syntax_Syntax.Sig_sub_effect (se, r) -> begin
(
# 451 "FStar.Syntax.Print.fst"
let _35_515 = (FStar_Syntax_Subst.open_univ_vars (Prims.fst se.FStar_Syntax_Syntax.lift) (Prims.snd se.FStar_Syntax_Syntax.lift))
in (match (_35_515) with
| (us, t) -> begin
(let _119_279 = (lid_to_string se.FStar_Syntax_Syntax.source)
in (let _119_278 = (lid_to_string se.FStar_Syntax_Syntax.target)
in (let _119_277 = (univ_names_to_string us)
in (let _119_276 = (term_to_string t)
in (FStar_Util.format4 "sub_effect %s ~> %s : <%s> %s" _119_279 _119_278 _119_277 _119_276)))))
end))
end
| FStar_Syntax_Syntax.Sig_effect_abbrev (l, univs, tps, c, _35_521, _35_523) -> begin
if (FStar_ST.read FStar_Options.print_universes) then begin
(
# 457 "FStar.Syntax.Print.fst"
let _35_528 = (let _119_280 = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_arrow ((tps, c))) None FStar_Range.dummyRange)
in (FStar_Syntax_Subst.open_univ_vars univs _119_280))
in (match (_35_528) with
| (univs, t) -> begin
(
# 458 "FStar.Syntax.Print.fst"
let _35_537 = (match ((let _119_281 = (FStar_Syntax_Subst.compress t)
in _119_281.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_arrow (bs, c) -> begin
(bs, c)
end
| _35_534 -> begin
(FStar_All.failwith "impossible")
end)
in (match (_35_537) with
| (tps, c) -> begin
(let _119_285 = (sli l)
in (let _119_284 = (univ_names_to_string univs)
in (let _119_283 = (binders_to_string " " tps)
in (let _119_282 = (comp_to_string c)
in (FStar_Util.format4 "effect %s<%s> %s = %s" _119_285 _119_284 _119_283 _119_282)))))
end))
end))
end else begin
(let _119_288 = (sli l)
in (let _119_287 = (binders_to_string " " tps)
in (let _119_286 = (comp_to_string c)
in (FStar_Util.format3 "effect %s %s = %s" _119_288 _119_287 _119_286))))
end
end))

# 464 "FStar.Syntax.Print.fst"
let format_error : FStar_Range.range  ->  Prims.string  ->  Prims.string = (fun r msg -> (let _119_293 = (FStar_Range.string_of_range r)
in (FStar_Util.format2 "%s: %s\n" _119_293 msg)))

# 466 "FStar.Syntax.Print.fst"
let rec sigelt_to_string_short : FStar_Syntax_Syntax.sigelt  ->  Prims.string = (fun x -> (match (x) with
| FStar_Syntax_Syntax.Sig_let ((_35_542, {FStar_Syntax_Syntax.lbname = lb; FStar_Syntax_Syntax.lbunivs = _35_549; FStar_Syntax_Syntax.lbtyp = t; FStar_Syntax_Syntax.lbeff = _35_546; FStar_Syntax_Syntax.lbdef = _35_544}::[]), _35_555, _35_557, _35_559) -> begin
(let _119_297 = (lbname_to_string lb)
in (let _119_296 = (term_to_string t)
in (FStar_Util.format2 "let %s : %s" _119_297 _119_296)))
end
| _35_563 -> begin
(let _119_300 = (let _119_299 = (FStar_Syntax_Util.lids_of_sigelt x)
in (FStar_All.pipe_right _119_299 (FStar_List.map (fun l -> l.FStar_Ident.str))))
in (FStar_All.pipe_right _119_300 (FStar_String.concat ", ")))
end))

# 470 "FStar.Syntax.Print.fst"
let rec modul_to_string : FStar_Syntax_Syntax.modul  ->  Prims.string = (fun m -> (let _119_305 = (sli m.FStar_Syntax_Syntax.name)
in (let _119_304 = (let _119_303 = (FStar_List.map sigelt_to_string m.FStar_Syntax_Syntax.declarations)
in (FStar_All.pipe_right _119_303 (FStar_String.concat "\n")))
in (FStar_Util.format2 "module %s\n%s" _119_305 _119_304))))

# 473 "FStar.Syntax.Print.fst"
let subst_elt_to_string : FStar_Syntax_Syntax.subst_elt  ->  Prims.string = (fun _35_10 -> (match (_35_10) with
| FStar_Syntax_Syntax.DB (i, x) -> begin
(let _119_309 = (FStar_Util.string_of_int i)
in (let _119_308 = (bv_to_string x)
in (FStar_Util.format2 "DB (%s, %s)" _119_309 _119_308)))
end
| FStar_Syntax_Syntax.NM (x, i) -> begin
(let _119_311 = (bv_to_string x)
in (let _119_310 = (FStar_Util.string_of_int i)
in (FStar_Util.format2 "NM (%s, %s)" _119_311 _119_310)))
end
| FStar_Syntax_Syntax.NT (x, t) -> begin
(let _119_313 = (bv_to_string x)
in (let _119_312 = (term_to_string t)
in (FStar_Util.format2 "DB (%s, %s)" _119_313 _119_312)))
end
| FStar_Syntax_Syntax.UN (i, u) -> begin
(let _119_315 = (FStar_Util.string_of_int i)
in (let _119_314 = (univ_to_string u)
in (FStar_Util.format2 "UN (%s, %s)" _119_315 _119_314)))
end
| FStar_Syntax_Syntax.UD (u, i) -> begin
(let _119_316 = (FStar_Util.string_of_int i)
in (FStar_Util.format2 "UD (%s, %s)" u.FStar_Ident.idText _119_316))
end))

# 480 "FStar.Syntax.Print.fst"
let subst_to_string : FStar_Syntax_Syntax.subst_t  ->  Prims.string = (fun s -> (let _119_319 = (FStar_All.pipe_right s (FStar_List.map subst_elt_to_string))
in (FStar_All.pipe_right _119_319 (FStar_String.concat "; "))))




