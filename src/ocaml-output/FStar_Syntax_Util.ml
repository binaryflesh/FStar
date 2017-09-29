
open Prims
open FStar_Pervasives

let qual_id : FStar_Ident.lident  ->  FStar_Ident.ident  ->  FStar_Ident.lident = (fun lid id -> (

let uu____9 = (FStar_Ident.lid_of_ids (FStar_List.append lid.FStar_Ident.ns ((lid.FStar_Ident.ident)::(id)::[])))
in (FStar_Ident.set_lid_range uu____9 id.FStar_Ident.idRange)))


let mk_discriminator : FStar_Ident.lident  ->  FStar_Ident.lident = (fun lid -> (FStar_Ident.lid_of_ids (FStar_List.append lid.FStar_Ident.ns (((FStar_Ident.mk_ident (((Prims.strcat FStar_Ident.reserved_prefix (Prims.strcat "is_" lid.FStar_Ident.ident.FStar_Ident.idText))), (lid.FStar_Ident.ident.FStar_Ident.idRange))))::[]))))


let is_name : FStar_Ident.lident  ->  Prims.bool = (fun lid -> (

let c = (FStar_Util.char_at lid.FStar_Ident.ident.FStar_Ident.idText (Prims.parse_int "0"))
in (FStar_Util.is_upper c)))


let arg_of_non_null_binder : 'Auu____23 . (FStar_Syntax_Syntax.bv * 'Auu____23)  ->  (FStar_Syntax_Syntax.term * 'Auu____23) = (fun uu____35 -> (match (uu____35) with
| (b, imp) -> begin
(

let uu____42 = (FStar_Syntax_Syntax.bv_to_name b)
in ((uu____42), (imp)))
end))


let args_of_non_null_binders : FStar_Syntax_Syntax.binders  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.aqual) Prims.list = (fun binders -> (FStar_All.pipe_right binders (FStar_List.collect (fun b -> (

let uu____66 = (FStar_Syntax_Syntax.is_null_binder b)
in (match (uu____66) with
| true -> begin
[]
end
| uu____77 -> begin
(

let uu____78 = (arg_of_non_null_binder b)
in (uu____78)::[])
end))))))


let args_of_binders : FStar_Syntax_Syntax.binders  ->  (FStar_Syntax_Syntax.binders * FStar_Syntax_Syntax.args) = (fun binders -> (

let uu____103 = (FStar_All.pipe_right binders (FStar_List.map (fun b -> (

let uu____149 = (FStar_Syntax_Syntax.is_null_binder b)
in (match (uu____149) with
| true -> begin
(

let b1 = (

let uu____167 = (FStar_Syntax_Syntax.new_bv FStar_Pervasives_Native.None (FStar_Pervasives_Native.fst b).FStar_Syntax_Syntax.sort)
in ((uu____167), ((FStar_Pervasives_Native.snd b))))
in (

let uu____168 = (arg_of_non_null_binder b1)
in ((b1), (uu____168))))
end
| uu____181 -> begin
(

let uu____182 = (arg_of_non_null_binder b)
in ((b), (uu____182)))
end)))))
in (FStar_All.pipe_right uu____103 FStar_List.unzip)))


let name_binders : FStar_Syntax_Syntax.binder Prims.list  ->  (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.aqual) Prims.list = (fun binders -> (FStar_All.pipe_right binders (FStar_List.mapi (fun i b -> (

let uu____265 = (FStar_Syntax_Syntax.is_null_binder b)
in (match (uu____265) with
| true -> begin
(

let uu____270 = b
in (match (uu____270) with
| (a, imp) -> begin
(

let b1 = (

let uu____278 = (

let uu____279 = (FStar_Util.string_of_int i)
in (Prims.strcat "_" uu____279))
in (FStar_Ident.id_of_text uu____278))
in (

let b2 = {FStar_Syntax_Syntax.ppname = b1; FStar_Syntax_Syntax.index = (Prims.parse_int "0"); FStar_Syntax_Syntax.sort = a.FStar_Syntax_Syntax.sort}
in ((b2), (imp))))
end))
end
| uu____281 -> begin
b
end))))))


let name_function_binders : FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax  ->  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax = (fun t -> (match (t.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_arrow (binders, comp) -> begin
(

let uu____312 = (

let uu____315 = (

let uu____316 = (

let uu____329 = (name_binders binders)
in ((uu____329), (comp)))
in FStar_Syntax_Syntax.Tm_arrow (uu____316))
in (FStar_Syntax_Syntax.mk uu____315))
in (uu____312 FStar_Pervasives_Native.None t.FStar_Syntax_Syntax.pos))
end
| uu____347 -> begin
t
end))


let null_binders_of_tks : (FStar_Syntax_Syntax.typ * FStar_Syntax_Syntax.aqual) Prims.list  ->  FStar_Syntax_Syntax.binders = (fun tks -> (FStar_All.pipe_right tks (FStar_List.map (fun uu____388 -> (match (uu____388) with
| (t, imp) -> begin
(

let uu____399 = (

let uu____400 = (FStar_Syntax_Syntax.null_binder t)
in (FStar_All.pipe_left FStar_Pervasives_Native.fst uu____400))
in ((uu____399), (imp)))
end)))))


let binders_of_tks : (FStar_Syntax_Syntax.typ * FStar_Syntax_Syntax.aqual) Prims.list  ->  FStar_Syntax_Syntax.binders = (fun tks -> (FStar_All.pipe_right tks (FStar_List.map (fun uu____451 -> (match (uu____451) with
| (t, imp) -> begin
(

let uu____468 = (FStar_Syntax_Syntax.new_bv (FStar_Pervasives_Native.Some (t.FStar_Syntax_Syntax.pos)) t)
in ((uu____468), (imp)))
end)))))


let binders_of_freevars : FStar_Syntax_Syntax.bv FStar_Util.set  ->  FStar_Syntax_Syntax.binder Prims.list = (fun fvs -> (

let uu____479 = (FStar_Util.set_elements fvs)
in (FStar_All.pipe_right uu____479 (FStar_List.map FStar_Syntax_Syntax.mk_binder))))


let mk_subst : 'Auu____490 . 'Auu____490  ->  'Auu____490 Prims.list = (fun s -> (s)::[])


let subst_of_list : FStar_Syntax_Syntax.binders  ->  FStar_Syntax_Syntax.args  ->  FStar_Syntax_Syntax.subst_t = (fun formals actuals -> (match ((Prims.op_Equality (FStar_List.length formals) (FStar_List.length actuals))) with
| true -> begin
(FStar_List.fold_right2 (fun f a out -> (FStar_Syntax_Syntax.NT ((((FStar_Pervasives_Native.fst f)), ((FStar_Pervasives_Native.fst a)))))::out) formals actuals [])
end
| uu____549 -> begin
(failwith "Ill-formed substitution")
end))


let rename_binders : FStar_Syntax_Syntax.binders  ->  FStar_Syntax_Syntax.binders  ->  FStar_Syntax_Syntax.subst_t = (fun replace_xs with_ys -> (match ((Prims.op_Equality (FStar_List.length replace_xs) (FStar_List.length with_ys))) with
| true -> begin
(FStar_List.map2 (fun uu____581 uu____582 -> (match (((uu____581), (uu____582))) with
| ((x, uu____600), (y, uu____602)) -> begin
(

let uu____611 = (

let uu____618 = (FStar_Syntax_Syntax.bv_to_name y)
in ((x), (uu____618)))
in FStar_Syntax_Syntax.NT (uu____611))
end)) replace_xs with_ys)
end
| uu____619 -> begin
(failwith "Ill-formed substitution")
end))


let rec unmeta : FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term = (fun e -> (

let e1 = (FStar_Syntax_Subst.compress e)
in (match (e1.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_meta (e2, uu____626) -> begin
(unmeta e2)
end
| FStar_Syntax_Syntax.Tm_ascribed (e2, uu____632, uu____633) -> begin
(unmeta e2)
end
| uu____674 -> begin
e1
end)))


let rec unmeta_safe : FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term = (fun e -> (

let e1 = (FStar_Syntax_Subst.compress e)
in (match (e1.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_meta (e', m) -> begin
(match (m) with
| FStar_Syntax_Syntax.Meta_monadic (uu____686) -> begin
e1
end
| FStar_Syntax_Syntax.Meta_monadic_lift (uu____693) -> begin
e1
end
| uu____702 -> begin
(unmeta_safe e')
end)
end
| FStar_Syntax_Syntax.Tm_ascribed (e2, uu____704, uu____705) -> begin
(unmeta_safe e2)
end
| uu____746 -> begin
e1
end)))


let rec univ_kernel : FStar_Syntax_Syntax.universe  ->  (FStar_Syntax_Syntax.universe * Prims.int) = (fun u -> (match (u) with
| FStar_Syntax_Syntax.U_unknown -> begin
((u), ((Prims.parse_int "0")))
end
| FStar_Syntax_Syntax.U_name (uu____759) -> begin
((u), ((Prims.parse_int "0")))
end
| FStar_Syntax_Syntax.U_unif (uu____760) -> begin
((u), ((Prims.parse_int "0")))
end
| FStar_Syntax_Syntax.U_zero -> begin
((u), ((Prims.parse_int "0")))
end
| FStar_Syntax_Syntax.U_succ (u1) -> begin
(

let uu____770 = (univ_kernel u1)
in (match (uu____770) with
| (k, n1) -> begin
((k), ((n1 + (Prims.parse_int "1"))))
end))
end
| FStar_Syntax_Syntax.U_max (uu____781) -> begin
(failwith "Imposible: univ_kernel (U_max _)")
end
| FStar_Syntax_Syntax.U_bvar (uu____788) -> begin
(failwith "Imposible: univ_kernel (U_bvar _)")
end))


let constant_univ_as_nat : FStar_Syntax_Syntax.universe  ->  Prims.int = (fun u -> (

let uu____797 = (univ_kernel u)
in (FStar_Pervasives_Native.snd uu____797)))


let rec compare_univs : FStar_Syntax_Syntax.universe  ->  FStar_Syntax_Syntax.universe  ->  Prims.int = (fun u1 u2 -> (match (((u1), (u2))) with
| (FStar_Syntax_Syntax.U_bvar (uu____810), uu____811) -> begin
(failwith "Impossible: compare_univs")
end
| (uu____812, FStar_Syntax_Syntax.U_bvar (uu____813)) -> begin
(failwith "Impossible: compare_univs")
end
| (FStar_Syntax_Syntax.U_unknown, FStar_Syntax_Syntax.U_unknown) -> begin
(Prims.parse_int "0")
end
| (FStar_Syntax_Syntax.U_unknown, uu____814) -> begin
(~- ((Prims.parse_int "1")))
end
| (uu____815, FStar_Syntax_Syntax.U_unknown) -> begin
(Prims.parse_int "1")
end
| (FStar_Syntax_Syntax.U_zero, FStar_Syntax_Syntax.U_zero) -> begin
(Prims.parse_int "0")
end
| (FStar_Syntax_Syntax.U_zero, uu____816) -> begin
(~- ((Prims.parse_int "1")))
end
| (uu____817, FStar_Syntax_Syntax.U_zero) -> begin
(Prims.parse_int "1")
end
| (FStar_Syntax_Syntax.U_name (u11), FStar_Syntax_Syntax.U_name (u21)) -> begin
(FStar_String.compare u11.FStar_Ident.idText u21.FStar_Ident.idText)
end
| (FStar_Syntax_Syntax.U_name (uu____820), FStar_Syntax_Syntax.U_unif (uu____821)) -> begin
(~- ((Prims.parse_int "1")))
end
| (FStar_Syntax_Syntax.U_unif (uu____830), FStar_Syntax_Syntax.U_name (uu____831)) -> begin
(Prims.parse_int "1")
end
| (FStar_Syntax_Syntax.U_unif (u11), FStar_Syntax_Syntax.U_unif (u21)) -> begin
(

let uu____858 = (FStar_Syntax_Unionfind.univ_uvar_id u11)
in (

let uu____859 = (FStar_Syntax_Unionfind.univ_uvar_id u21)
in (uu____858 - uu____859)))
end
| (FStar_Syntax_Syntax.U_max (us1), FStar_Syntax_Syntax.U_max (us2)) -> begin
(

let n1 = (FStar_List.length us1)
in (

let n2 = (FStar_List.length us2)
in (match ((Prims.op_disEquality n1 n2)) with
| true -> begin
(n1 - n2)
end
| uu____886 -> begin
(

let copt = (

let uu____890 = (FStar_List.zip us1 us2)
in (FStar_Util.find_map uu____890 (fun uu____905 -> (match (uu____905) with
| (u11, u21) -> begin
(

let c = (compare_univs u11 u21)
in (match ((Prims.op_disEquality c (Prims.parse_int "0"))) with
| true -> begin
FStar_Pervasives_Native.Some (c)
end
| uu____917 -> begin
FStar_Pervasives_Native.None
end))
end))))
in (match (copt) with
| FStar_Pervasives_Native.None -> begin
(Prims.parse_int "0")
end
| FStar_Pervasives_Native.Some (c) -> begin
c
end))
end)))
end
| (FStar_Syntax_Syntax.U_max (uu____919), uu____920) -> begin
(~- ((Prims.parse_int "1")))
end
| (uu____923, FStar_Syntax_Syntax.U_max (uu____924)) -> begin
(Prims.parse_int "1")
end
| uu____927 -> begin
(

let uu____932 = (univ_kernel u1)
in (match (uu____932) with
| (k1, n1) -> begin
(

let uu____939 = (univ_kernel u2)
in (match (uu____939) with
| (k2, n2) -> begin
(

let r = (compare_univs k1 k2)
in (match ((Prims.op_Equality r (Prims.parse_int "0"))) with
| true -> begin
(n1 - n2)
end
| uu____947 -> begin
r
end))
end))
end))
end))


let eq_univs : FStar_Syntax_Syntax.universe  ->  FStar_Syntax_Syntax.universe  ->  Prims.bool = (fun u1 u2 -> (

let uu____956 = (compare_univs u1 u2)
in (Prims.op_Equality uu____956 (Prims.parse_int "0"))))


let ml_comp : FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax  ->  FStar_Range.range  ->  FStar_Syntax_Syntax.comp = (fun t r -> (FStar_Syntax_Syntax.mk_Comp {FStar_Syntax_Syntax.comp_univs = (FStar_Syntax_Syntax.U_zero)::[]; FStar_Syntax_Syntax.effect_name = (FStar_Ident.set_lid_range FStar_Parser_Const.effect_ML_lid r); FStar_Syntax_Syntax.result_typ = t; FStar_Syntax_Syntax.effect_args = []; FStar_Syntax_Syntax.flags = (FStar_Syntax_Syntax.MLEFFECT)::[]}))


let comp_effect_name : FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax  ->  FStar_Ident.lident = (fun c -> (match (c.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Comp (c1) -> begin
c1.FStar_Syntax_Syntax.effect_name
end
| FStar_Syntax_Syntax.Total (uu____984) -> begin
FStar_Parser_Const.effect_Tot_lid
end
| FStar_Syntax_Syntax.GTotal (uu____993) -> begin
FStar_Parser_Const.effect_GTot_lid
end))


let comp_flags : FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax  ->  FStar_Syntax_Syntax.cflags Prims.list = (fun c -> (match (c.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Total (uu____1014) -> begin
(FStar_Syntax_Syntax.TOTAL)::[]
end
| FStar_Syntax_Syntax.GTotal (uu____1023) -> begin
(FStar_Syntax_Syntax.SOMETRIVIAL)::[]
end
| FStar_Syntax_Syntax.Comp (ct) -> begin
ct.FStar_Syntax_Syntax.flags
end))


let comp_set_flags : FStar_Syntax_Syntax.comp  ->  FStar_Syntax_Syntax.cflags Prims.list  ->  FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax = (fun c f -> (

let comp_to_comp_typ = (fun c1 -> (match (c1.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Comp (c2) -> begin
c2
end
| FStar_Syntax_Syntax.Total (t, u_opt) -> begin
(

let uu____1062 = (

let uu____1063 = (FStar_Util.map_opt u_opt (fun x -> (x)::[]))
in (FStar_Util.dflt [] uu____1063))
in {FStar_Syntax_Syntax.comp_univs = uu____1062; FStar_Syntax_Syntax.effect_name = (comp_effect_name c1); FStar_Syntax_Syntax.result_typ = t; FStar_Syntax_Syntax.effect_args = []; FStar_Syntax_Syntax.flags = (comp_flags c1)})
end
| FStar_Syntax_Syntax.GTotal (t, u_opt) -> begin
(

let uu____1090 = (

let uu____1091 = (FStar_Util.map_opt u_opt (fun x -> (x)::[]))
in (FStar_Util.dflt [] uu____1091))
in {FStar_Syntax_Syntax.comp_univs = uu____1090; FStar_Syntax_Syntax.effect_name = (comp_effect_name c1); FStar_Syntax_Syntax.result_typ = t; FStar_Syntax_Syntax.effect_args = []; FStar_Syntax_Syntax.flags = (comp_flags c1)})
end))
in (

let uu___169_1108 = c
in (

let uu____1109 = (

let uu____1110 = (

let uu___170_1111 = (comp_to_comp_typ c)
in {FStar_Syntax_Syntax.comp_univs = uu___170_1111.FStar_Syntax_Syntax.comp_univs; FStar_Syntax_Syntax.effect_name = uu___170_1111.FStar_Syntax_Syntax.effect_name; FStar_Syntax_Syntax.result_typ = uu___170_1111.FStar_Syntax_Syntax.result_typ; FStar_Syntax_Syntax.effect_args = uu___170_1111.FStar_Syntax_Syntax.effect_args; FStar_Syntax_Syntax.flags = f})
in FStar_Syntax_Syntax.Comp (uu____1110))
in {FStar_Syntax_Syntax.n = uu____1109; FStar_Syntax_Syntax.pos = uu___169_1108.FStar_Syntax_Syntax.pos; FStar_Syntax_Syntax.vars = uu___169_1108.FStar_Syntax_Syntax.vars}))))


let comp_to_comp_typ : FStar_Syntax_Syntax.comp  ->  FStar_Syntax_Syntax.comp_typ = (fun c -> (match (c.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Comp (c1) -> begin
c1
end
| FStar_Syntax_Syntax.Total (t, FStar_Pervasives_Native.Some (u)) -> begin
{FStar_Syntax_Syntax.comp_univs = (u)::[]; FStar_Syntax_Syntax.effect_name = (comp_effect_name c); FStar_Syntax_Syntax.result_typ = t; FStar_Syntax_Syntax.effect_args = []; FStar_Syntax_Syntax.flags = (comp_flags c)}
end
| FStar_Syntax_Syntax.GTotal (t, FStar_Pervasives_Native.Some (u)) -> begin
{FStar_Syntax_Syntax.comp_univs = (u)::[]; FStar_Syntax_Syntax.effect_name = (comp_effect_name c); FStar_Syntax_Syntax.result_typ = t; FStar_Syntax_Syntax.effect_args = []; FStar_Syntax_Syntax.flags = (comp_flags c)}
end
| uu____1145 -> begin
(failwith "Assertion failed: Computation type without universe")
end))


let is_named_tot : FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax  ->  Prims.bool = (fun c -> (match (c.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Comp (c1) -> begin
(FStar_Ident.lid_equals c1.FStar_Syntax_Syntax.effect_name FStar_Parser_Const.effect_Tot_lid)
end
| FStar_Syntax_Syntax.Total (uu____1155) -> begin
true
end
| FStar_Syntax_Syntax.GTotal (uu____1164) -> begin
false
end))


let is_total_comp : FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax  ->  Prims.bool = (fun c -> ((FStar_Ident.lid_equals (comp_effect_name c) FStar_Parser_Const.effect_Tot_lid) || (FStar_All.pipe_right (comp_flags c) (FStar_Util.for_some (fun uu___157_1184 -> (match (uu___157_1184) with
| FStar_Syntax_Syntax.TOTAL -> begin
true
end
| FStar_Syntax_Syntax.RETURN -> begin
true
end
| uu____1185 -> begin
false
end))))))


let is_total_lcomp : FStar_Syntax_Syntax.lcomp  ->  Prims.bool = (fun c -> ((FStar_Ident.lid_equals c.FStar_Syntax_Syntax.eff_name FStar_Parser_Const.effect_Tot_lid) || (FStar_All.pipe_right c.FStar_Syntax_Syntax.cflags (FStar_Util.for_some (fun uu___158_1193 -> (match (uu___158_1193) with
| FStar_Syntax_Syntax.TOTAL -> begin
true
end
| FStar_Syntax_Syntax.RETURN -> begin
true
end
| uu____1194 -> begin
false
end))))))


let is_tot_or_gtot_lcomp : FStar_Syntax_Syntax.lcomp  ->  Prims.bool = (fun c -> (((FStar_Ident.lid_equals c.FStar_Syntax_Syntax.eff_name FStar_Parser_Const.effect_Tot_lid) || (FStar_Ident.lid_equals c.FStar_Syntax_Syntax.eff_name FStar_Parser_Const.effect_GTot_lid)) || (FStar_All.pipe_right c.FStar_Syntax_Syntax.cflags (FStar_Util.for_some (fun uu___159_1202 -> (match (uu___159_1202) with
| FStar_Syntax_Syntax.TOTAL -> begin
true
end
| FStar_Syntax_Syntax.RETURN -> begin
true
end
| uu____1203 -> begin
false
end))))))


let is_partial_return : FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax  ->  Prims.bool = (fun c -> (FStar_All.pipe_right (comp_flags c) (FStar_Util.for_some (fun uu___160_1215 -> (match (uu___160_1215) with
| FStar_Syntax_Syntax.RETURN -> begin
true
end
| FStar_Syntax_Syntax.PARTIAL_RETURN -> begin
true
end
| uu____1216 -> begin
false
end)))))


let is_lcomp_partial_return : FStar_Syntax_Syntax.lcomp  ->  Prims.bool = (fun c -> (FStar_All.pipe_right c.FStar_Syntax_Syntax.cflags (FStar_Util.for_some (fun uu___161_1224 -> (match (uu___161_1224) with
| FStar_Syntax_Syntax.RETURN -> begin
true
end
| FStar_Syntax_Syntax.PARTIAL_RETURN -> begin
true
end
| uu____1225 -> begin
false
end)))))


let is_tot_or_gtot_comp : FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax  ->  Prims.bool = (fun c -> ((is_total_comp c) || (FStar_Ident.lid_equals FStar_Parser_Const.effect_GTot_lid (comp_effect_name c))))


let is_pure_effect : FStar_Ident.lident  ->  Prims.bool = (fun l -> (((FStar_Ident.lid_equals l FStar_Parser_Const.effect_Tot_lid) || (FStar_Ident.lid_equals l FStar_Parser_Const.effect_PURE_lid)) || (FStar_Ident.lid_equals l FStar_Parser_Const.effect_Pure_lid)))


let is_pure_comp : FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax  ->  Prims.bool = (fun c -> (match (c.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Total (uu____1246) -> begin
true
end
| FStar_Syntax_Syntax.GTotal (uu____1255) -> begin
false
end
| FStar_Syntax_Syntax.Comp (ct) -> begin
(((is_total_comp c) || (is_pure_effect ct.FStar_Syntax_Syntax.effect_name)) || (FStar_All.pipe_right ct.FStar_Syntax_Syntax.flags (FStar_Util.for_some (fun uu___162_1268 -> (match (uu___162_1268) with
| FStar_Syntax_Syntax.LEMMA -> begin
true
end
| uu____1269 -> begin
false
end)))))
end))


let is_ghost_effect : FStar_Ident.lident  ->  Prims.bool = (fun l -> (((FStar_Ident.lid_equals FStar_Parser_Const.effect_GTot_lid l) || (FStar_Ident.lid_equals FStar_Parser_Const.effect_GHOST_lid l)) || (FStar_Ident.lid_equals FStar_Parser_Const.effect_Ghost_lid l)))


let is_pure_or_ghost_comp : FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax  ->  Prims.bool = (fun c -> ((is_pure_comp c) || (is_ghost_effect (comp_effect_name c))))


let is_pure_lcomp : FStar_Syntax_Syntax.lcomp  ->  Prims.bool = (fun lc -> (((is_total_lcomp lc) || (is_pure_effect lc.FStar_Syntax_Syntax.eff_name)) || (FStar_All.pipe_right lc.FStar_Syntax_Syntax.cflags (FStar_Util.for_some (fun uu___163_1289 -> (match (uu___163_1289) with
| FStar_Syntax_Syntax.LEMMA -> begin
true
end
| uu____1290 -> begin
false
end))))))


let is_pure_or_ghost_lcomp : FStar_Syntax_Syntax.lcomp  ->  Prims.bool = (fun lc -> ((is_pure_lcomp lc) || (is_ghost_effect lc.FStar_Syntax_Syntax.eff_name)))


let is_pure_or_ghost_function : FStar_Syntax_Syntax.term  ->  Prims.bool = (fun t -> (

let uu____1299 = (

let uu____1300 = (FStar_Syntax_Subst.compress t)
in uu____1300.FStar_Syntax_Syntax.n)
in (match (uu____1299) with
| FStar_Syntax_Syntax.Tm_arrow (uu____1303, c) -> begin
(is_pure_or_ghost_comp c)
end
| uu____1321 -> begin
true
end)))


let is_lemma_comp : FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax  ->  Prims.bool = (fun c -> (match (c.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Comp (ct) -> begin
(FStar_Ident.lid_equals ct.FStar_Syntax_Syntax.effect_name FStar_Parser_Const.effect_Lemma_lid)
end
| uu____1331 -> begin
false
end))


let is_lemma : FStar_Syntax_Syntax.term  ->  Prims.bool = (fun t -> (

let uu____1336 = (

let uu____1337 = (FStar_Syntax_Subst.compress t)
in uu____1337.FStar_Syntax_Syntax.n)
in (match (uu____1336) with
| FStar_Syntax_Syntax.Tm_arrow (uu____1340, c) -> begin
(is_lemma_comp c)
end
| uu____1358 -> begin
false
end)))


let head_and_args : FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax * (FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax * FStar_Syntax_Syntax.aqual) Prims.list) = (fun t -> (

let t1 = (FStar_Syntax_Subst.compress t)
in (match (t1.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_app (head1, args) -> begin
((head1), (args))
end
| uu____1424 -> begin
((t1), ([]))
end)))


let rec head_and_args' : FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.term * (FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax * FStar_Syntax_Syntax.aqual) Prims.list) = (fun t -> (

let t1 = (FStar_Syntax_Subst.compress t)
in (match (t1.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_app (head1, args) -> begin
(

let uu____1490 = (head_and_args' head1)
in (match (uu____1490) with
| (head2, args') -> begin
((head2), ((FStar_List.append args' args)))
end))
end
| uu____1547 -> begin
((t1), ([]))
end)))


let un_uinst : FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term = (fun t -> (

let t1 = (FStar_Syntax_Subst.compress t)
in (match (t1.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_uinst (t2, uu____1568) -> begin
(FStar_Syntax_Subst.compress t2)
end
| uu____1573 -> begin
t1
end)))


let is_smt_lemma : FStar_Syntax_Syntax.term  ->  Prims.bool = (fun t -> (

let uu____1578 = (

let uu____1579 = (FStar_Syntax_Subst.compress t)
in uu____1579.FStar_Syntax_Syntax.n)
in (match (uu____1578) with
| FStar_Syntax_Syntax.Tm_arrow (uu____1582, c) -> begin
(match (c.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Comp (ct) when (FStar_Ident.lid_equals ct.FStar_Syntax_Syntax.effect_name FStar_Parser_Const.effect_Lemma_lid) -> begin
(match (ct.FStar_Syntax_Syntax.effect_args) with
| (_req)::(_ens)::((pats, uu____1604))::uu____1605 -> begin
(

let pats' = (unmeta pats)
in (

let uu____1649 = (head_and_args pats')
in (match (uu____1649) with
| (head1, uu____1665) -> begin
(

let uu____1686 = (

let uu____1687 = (un_uinst head1)
in uu____1687.FStar_Syntax_Syntax.n)
in (match (uu____1686) with
| FStar_Syntax_Syntax.Tm_fvar (fv) -> begin
(FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.cons_lid)
end
| uu____1691 -> begin
false
end))
end)))
end
| uu____1692 -> begin
false
end)
end
| uu____1701 -> begin
false
end)
end
| uu____1702 -> begin
false
end)))


let is_ml_comp : FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax  ->  Prims.bool = (fun c -> (match (c.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Comp (c1) -> begin
((FStar_Ident.lid_equals c1.FStar_Syntax_Syntax.effect_name FStar_Parser_Const.effect_ML_lid) || (FStar_All.pipe_right c1.FStar_Syntax_Syntax.flags (FStar_Util.for_some (fun uu___164_1715 -> (match (uu___164_1715) with
| FStar_Syntax_Syntax.MLEFFECT -> begin
true
end
| uu____1716 -> begin
false
end)))))
end
| uu____1717 -> begin
false
end))


let comp_result : FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax  ->  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax = (fun c -> (match (c.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Total (t, uu____1731) -> begin
t
end
| FStar_Syntax_Syntax.GTotal (t, uu____1741) -> begin
t
end
| FStar_Syntax_Syntax.Comp (ct) -> begin
ct.FStar_Syntax_Syntax.result_typ
end))


let set_result_typ : FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax  ->  FStar_Syntax_Syntax.typ  ->  FStar_Syntax_Syntax.comp = (fun c t -> (match (c.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Total (uu____1763) -> begin
(FStar_Syntax_Syntax.mk_Total t)
end
| FStar_Syntax_Syntax.GTotal (uu____1772) -> begin
(FStar_Syntax_Syntax.mk_GTotal t)
end
| FStar_Syntax_Syntax.Comp (ct) -> begin
(FStar_Syntax_Syntax.mk_Comp (

let uu___171_1784 = ct
in {FStar_Syntax_Syntax.comp_univs = uu___171_1784.FStar_Syntax_Syntax.comp_univs; FStar_Syntax_Syntax.effect_name = uu___171_1784.FStar_Syntax_Syntax.effect_name; FStar_Syntax_Syntax.result_typ = t; FStar_Syntax_Syntax.effect_args = uu___171_1784.FStar_Syntax_Syntax.effect_args; FStar_Syntax_Syntax.flags = uu___171_1784.FStar_Syntax_Syntax.flags}))
end))


let is_trivial_wp : FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax  ->  Prims.bool = (fun c -> (FStar_All.pipe_right (comp_flags c) (FStar_Util.for_some (fun uu___165_1796 -> (match (uu___165_1796) with
| FStar_Syntax_Syntax.TOTAL -> begin
true
end
| FStar_Syntax_Syntax.RETURN -> begin
true
end
| uu____1797 -> begin
false
end)))))


let primops : FStar_Ident.lident Prims.list = (FStar_Parser_Const.op_Eq)::(FStar_Parser_Const.op_notEq)::(FStar_Parser_Const.op_LT)::(FStar_Parser_Const.op_LTE)::(FStar_Parser_Const.op_GT)::(FStar_Parser_Const.op_GTE)::(FStar_Parser_Const.op_Subtraction)::(FStar_Parser_Const.op_Minus)::(FStar_Parser_Const.op_Addition)::(FStar_Parser_Const.op_Multiply)::(FStar_Parser_Const.op_Division)::(FStar_Parser_Const.op_Modulus)::(FStar_Parser_Const.op_And)::(FStar_Parser_Const.op_Or)::(FStar_Parser_Const.op_Negation)::[]


let is_primop_lid : FStar_Ident.lident  ->  Prims.bool = (fun l -> (FStar_All.pipe_right primops (FStar_Util.for_some (FStar_Ident.lid_equals l))))


let is_primop : FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax  ->  Prims.bool = (fun f -> (match (f.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_fvar (fv) -> begin
(is_primop_lid fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v)
end
| uu____1815 -> begin
false
end))


let rec unascribe : FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term = (fun e -> (

let e1 = (FStar_Syntax_Subst.compress e)
in (match (e1.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_ascribed (e2, uu____1822, uu____1823) -> begin
(unascribe e2)
end
| uu____1864 -> begin
e1
end)))


let rec ascribe : FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax  ->  ((FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax, FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax) FStar_Util.either * FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax FStar_Pervasives_Native.option)  ->  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax = (fun t k -> (match (t.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_ascribed (t', uu____1914, uu____1915) -> begin
(ascribe t' k)
end
| uu____1956 -> begin
(FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_ascribed (((t), (k), (FStar_Pervasives_Native.None)))) FStar_Pervasives_Native.None t.FStar_Syntax_Syntax.pos)
end))

type eq_result =
| Equal
| NotEqual
| Unknown


let uu___is_Equal : eq_result  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Equal -> begin
true
end
| uu____1981 -> begin
false
end))


let uu___is_NotEqual : eq_result  ->  Prims.bool = (fun projectee -> (match (projectee) with
| NotEqual -> begin
true
end
| uu____1986 -> begin
false
end))


let uu___is_Unknown : eq_result  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Unknown -> begin
true
end
| uu____1991 -> begin
false
end))


let rec eq_tm : FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term  ->  eq_result = (fun t1 t2 -> (

let canon_app = (fun t -> (

let uu____2012 = (

let uu____2025 = (unascribe t)
in (head_and_args' uu____2025))
in (match (uu____2012) with
| (hd1, args) -> begin
(FStar_Syntax_Syntax.mk_Tm_app hd1 args FStar_Pervasives_Native.None t.FStar_Syntax_Syntax.pos)
end)))
in (

let t11 = (canon_app t1)
in (

let t21 = (canon_app t2)
in (

let equal_if = (fun uu___166_2055 -> (match (uu___166_2055) with
| true -> begin
Equal
end
| uu____2056 -> begin
Unknown
end))
in (

let equal_iff = (fun uu___167_2060 -> (match (uu___167_2060) with
| true -> begin
Equal
end
| uu____2061 -> begin
NotEqual
end))
in (

let eq_and = (fun f g -> (match (f) with
| Equal -> begin
(g ())
end
| uu____2074 -> begin
Unknown
end))
in (

let eq_inj = (fun f g -> (match (((f), (g))) with
| (Equal, Equal) -> begin
Equal
end
| (NotEqual, uu____2082) -> begin
NotEqual
end
| (uu____2083, NotEqual) -> begin
NotEqual
end
| (Unknown, uu____2084) -> begin
Unknown
end
| (uu____2085, Unknown) -> begin
Unknown
end))
in (

let equal_data = (fun f1 args1 f2 args2 -> (

let uu____2123 = (FStar_Syntax_Syntax.fv_eq f1 f2)
in (match (uu____2123) with
| true -> begin
(

let uu____2127 = (FStar_List.zip args1 args2)
in (FStar_All.pipe_left (FStar_List.fold_left (fun acc uu____2185 -> (match (uu____2185) with
| ((a1, q1), (a2, q2)) -> begin
(

let uu____2213 = (eq_tm a1 a2)
in (eq_inj acc uu____2213))
end)) Equal) uu____2127))
end
| uu____2214 -> begin
NotEqual
end)))
in (match (((t11.FStar_Syntax_Syntax.n), (t21.FStar_Syntax_Syntax.n))) with
| (FStar_Syntax_Syntax.Tm_name (a), FStar_Syntax_Syntax.Tm_name (b)) -> begin
(equal_if (FStar_Syntax_Syntax.bv_eq a b))
end
| (FStar_Syntax_Syntax.Tm_fvar (f), FStar_Syntax_Syntax.Tm_fvar (g)) -> begin
(match (((Prims.op_Equality f.FStar_Syntax_Syntax.fv_qual (FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Data_ctor))) && (Prims.op_Equality g.FStar_Syntax_Syntax.fv_qual (FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Data_ctor))))) with
| true -> begin
(equal_data f [] g [])
end
| uu____2231 -> begin
(

let uu____2232 = (FStar_Syntax_Syntax.fv_eq f g)
in (equal_if uu____2232))
end)
end
| (FStar_Syntax_Syntax.Tm_uinst (f, us), FStar_Syntax_Syntax.Tm_uinst (g, vs)) -> begin
(

let uu____2245 = (eq_tm f g)
in (eq_and uu____2245 (fun uu____2248 -> (

let uu____2249 = (eq_univs_list us vs)
in (equal_if uu____2249)))))
end
| (FStar_Syntax_Syntax.Tm_constant (c), FStar_Syntax_Syntax.Tm_constant (d)) -> begin
(

let uu____2252 = (FStar_Const.eq_const c d)
in (equal_iff uu____2252))
end
| (FStar_Syntax_Syntax.Tm_uvar (u1, uu____2254), FStar_Syntax_Syntax.Tm_uvar (u2, uu____2256)) -> begin
(

let uu____2305 = (FStar_Syntax_Unionfind.equiv u1 u2)
in (equal_if uu____2305))
end
| (FStar_Syntax_Syntax.Tm_app (h1, args1), FStar_Syntax_Syntax.Tm_app (h2, args2)) -> begin
(

let uu____2350 = (

let uu____2355 = (

let uu____2356 = (un_uinst h1)
in uu____2356.FStar_Syntax_Syntax.n)
in (

let uu____2359 = (

let uu____2360 = (un_uinst h2)
in uu____2360.FStar_Syntax_Syntax.n)
in ((uu____2355), (uu____2359))))
in (match (uu____2350) with
| (FStar_Syntax_Syntax.Tm_fvar (f1), FStar_Syntax_Syntax.Tm_fvar (f2)) when ((Prims.op_Equality f1.FStar_Syntax_Syntax.fv_qual (FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Data_ctor))) && (Prims.op_Equality f2.FStar_Syntax_Syntax.fv_qual (FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Data_ctor)))) -> begin
(equal_data f1 args1 f2 args2)
end
| uu____2369 -> begin
(

let uu____2374 = (eq_tm h1 h2)
in (eq_and uu____2374 (fun uu____2376 -> (eq_args args1 args2))))
end))
end
| (FStar_Syntax_Syntax.Tm_type (u), FStar_Syntax_Syntax.Tm_type (v1)) -> begin
(

let uu____2379 = (eq_univs u v1)
in (equal_if uu____2379))
end
| (FStar_Syntax_Syntax.Tm_meta (t12, uu____2381), uu____2382) -> begin
(eq_tm t12 t21)
end
| (uu____2387, FStar_Syntax_Syntax.Tm_meta (t22, uu____2389)) -> begin
(eq_tm t11 t22)
end
| uu____2394 -> begin
Unknown
end))))))))))
and eq_args : FStar_Syntax_Syntax.args  ->  FStar_Syntax_Syntax.args  ->  eq_result = (fun a1 a2 -> (match (((a1), (a2))) with
| ([], []) -> begin
Equal
end
| (((a, uu____2430))::a11, ((b, uu____2433))::b1) -> begin
(

let uu____2487 = (eq_tm a b)
in (match (uu____2487) with
| Equal -> begin
(eq_args a11 b1)
end
| uu____2488 -> begin
Unknown
end))
end
| uu____2489 -> begin
Unknown
end))
and eq_univs_list : FStar_Syntax_Syntax.universes  ->  FStar_Syntax_Syntax.universes  ->  Prims.bool = (fun us vs -> ((Prims.op_Equality (FStar_List.length us) (FStar_List.length vs)) && (FStar_List.forall2 eq_univs us vs)))


let rec unrefine : FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term = (fun t -> (

let t1 = (FStar_Syntax_Subst.compress t)
in (match (t1.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_refine (x, uu____2502) -> begin
(unrefine x.FStar_Syntax_Syntax.sort)
end
| FStar_Syntax_Syntax.Tm_ascribed (t2, uu____2508, uu____2509) -> begin
(unrefine t2)
end
| uu____2550 -> begin
t1
end)))


let rec is_unit : FStar_Syntax_Syntax.term  ->  Prims.bool = (fun t -> (

let uu____2555 = (

let uu____2556 = (unrefine t)
in uu____2556.FStar_Syntax_Syntax.n)
in (match (uu____2555) with
| FStar_Syntax_Syntax.Tm_type (uu____2559) -> begin
true
end
| FStar_Syntax_Syntax.Tm_fvar (fv) -> begin
((FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.unit_lid) || (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.squash_lid))
end
| FStar_Syntax_Syntax.Tm_uinst (t1, uu____2562) -> begin
(is_unit t1)
end
| uu____2567 -> begin
false
end)))


let rec non_informative : FStar_Syntax_Syntax.term  ->  Prims.bool = (fun t -> (

let uu____2572 = (

let uu____2573 = (unrefine t)
in uu____2573.FStar_Syntax_Syntax.n)
in (match (uu____2572) with
| FStar_Syntax_Syntax.Tm_type (uu____2576) -> begin
true
end
| FStar_Syntax_Syntax.Tm_fvar (fv) -> begin
(((FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.unit_lid) || (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.squash_lid)) || (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.erased_lid))
end
| FStar_Syntax_Syntax.Tm_app (head1, uu____2579) -> begin
(non_informative head1)
end
| FStar_Syntax_Syntax.Tm_uinst (t1, uu____2601) -> begin
(non_informative t1)
end
| FStar_Syntax_Syntax.Tm_arrow (uu____2606, c) -> begin
((is_tot_or_gtot_comp c) && (non_informative (comp_result c)))
end
| uu____2624 -> begin
false
end)))


let is_fun : FStar_Syntax_Syntax.term  ->  Prims.bool = (fun e -> (

let uu____2629 = (

let uu____2630 = (FStar_Syntax_Subst.compress e)
in uu____2630.FStar_Syntax_Syntax.n)
in (match (uu____2629) with
| FStar_Syntax_Syntax.Tm_abs (uu____2633) -> begin
true
end
| uu____2650 -> begin
false
end)))


let is_function_typ : FStar_Syntax_Syntax.term  ->  Prims.bool = (fun t -> (

let uu____2655 = (

let uu____2656 = (FStar_Syntax_Subst.compress t)
in uu____2656.FStar_Syntax_Syntax.n)
in (match (uu____2655) with
| FStar_Syntax_Syntax.Tm_arrow (uu____2659) -> begin
true
end
| uu____2672 -> begin
false
end)))


let rec pre_typ : FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term = (fun t -> (

let t1 = (FStar_Syntax_Subst.compress t)
in (match (t1.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_refine (x, uu____2679) -> begin
(pre_typ x.FStar_Syntax_Syntax.sort)
end
| FStar_Syntax_Syntax.Tm_ascribed (t2, uu____2685, uu____2686) -> begin
(pre_typ t2)
end
| uu____2727 -> begin
t1
end)))


let destruct : FStar_Syntax_Syntax.term  ->  FStar_Ident.lident  ->  (FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax * FStar_Syntax_Syntax.aqual) Prims.list FStar_Pervasives_Native.option = (fun typ lid -> (

let typ1 = (FStar_Syntax_Subst.compress typ)
in (

let uu____2747 = (

let uu____2748 = (un_uinst typ1)
in uu____2748.FStar_Syntax_Syntax.n)
in (match (uu____2747) with
| FStar_Syntax_Syntax.Tm_app (head1, args) -> begin
(

let head2 = (un_uinst head1)
in (match (head2.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_fvar (tc) when (FStar_Syntax_Syntax.fv_eq_lid tc lid) -> begin
FStar_Pervasives_Native.Some (args)
end
| uu____2803 -> begin
FStar_Pervasives_Native.None
end))
end
| FStar_Syntax_Syntax.Tm_fvar (tc) when (FStar_Syntax_Syntax.fv_eq_lid tc lid) -> begin
FStar_Pervasives_Native.Some ([])
end
| uu____2827 -> begin
FStar_Pervasives_Native.None
end))))


let lids_of_sigelt : FStar_Syntax_Syntax.sigelt  ->  FStar_Ident.lident Prims.list = (fun se -> (match (se.FStar_Syntax_Syntax.sigel) with
| FStar_Syntax_Syntax.Sig_let (uu____2844, lids) -> begin
lids
end
| FStar_Syntax_Syntax.Sig_bundle (uu____2850, lids) -> begin
lids
end
| FStar_Syntax_Syntax.Sig_inductive_typ (lid, uu____2861, uu____2862, uu____2863, uu____2864, uu____2865) -> begin
(lid)::[]
end
| FStar_Syntax_Syntax.Sig_effect_abbrev (lid, uu____2875, uu____2876, uu____2877, uu____2878) -> begin
(lid)::[]
end
| FStar_Syntax_Syntax.Sig_datacon (lid, uu____2884, uu____2885, uu____2886, uu____2887, uu____2888) -> begin
(lid)::[]
end
| FStar_Syntax_Syntax.Sig_declare_typ (lid, uu____2894, uu____2895) -> begin
(lid)::[]
end
| FStar_Syntax_Syntax.Sig_assume (lid, uu____2897, uu____2898) -> begin
(lid)::[]
end
| FStar_Syntax_Syntax.Sig_new_effect_for_free (n1) -> begin
(n1.FStar_Syntax_Syntax.mname)::[]
end
| FStar_Syntax_Syntax.Sig_new_effect (n1) -> begin
(n1.FStar_Syntax_Syntax.mname)::[]
end
| FStar_Syntax_Syntax.Sig_sub_effect (uu____2901) -> begin
[]
end
| FStar_Syntax_Syntax.Sig_pragma (uu____2902) -> begin
[]
end
| FStar_Syntax_Syntax.Sig_main (uu____2903) -> begin
[]
end))


let lid_of_sigelt : FStar_Syntax_Syntax.sigelt  ->  FStar_Ident.lident FStar_Pervasives_Native.option = (fun se -> (match ((lids_of_sigelt se)) with
| (l)::[] -> begin
FStar_Pervasives_Native.Some (l)
end
| uu____2915 -> begin
FStar_Pervasives_Native.None
end))


let quals_of_sigelt : FStar_Syntax_Syntax.sigelt  ->  FStar_Syntax_Syntax.qualifier Prims.list = (fun x -> x.FStar_Syntax_Syntax.sigquals)


let range_of_sigelt : FStar_Syntax_Syntax.sigelt  ->  FStar_Range.range = (fun x -> x.FStar_Syntax_Syntax.sigrng)


let range_of_lb : 'Auu____2934 'Auu____2935 . ((FStar_Syntax_Syntax.bv, FStar_Ident.lid) FStar_Util.either * 'Auu____2935 * 'Auu____2934)  ->  FStar_Range.range = (fun uu___168_2949 -> (match (uu___168_2949) with
| (FStar_Util.Inl (x), uu____2961, uu____2962) -> begin
(FStar_Syntax_Syntax.range_of_bv x)
end
| (FStar_Util.Inr (l), uu____2968, uu____2969) -> begin
(FStar_Ident.range_of_lid l)
end))


let range_of_arg : 'Auu____2980 'Auu____2981 . ('Auu____2981 FStar_Syntax_Syntax.syntax * 'Auu____2980)  ->  FStar_Range.range = (fun uu____2991 -> (match (uu____2991) with
| (hd1, uu____2999) -> begin
hd1.FStar_Syntax_Syntax.pos
end))


let range_of_args : 'Auu____3012 'Auu____3013 . ('Auu____3013 FStar_Syntax_Syntax.syntax * 'Auu____3012) Prims.list  ->  FStar_Range.range  ->  FStar_Range.range = (fun args r -> (FStar_All.pipe_right args (FStar_List.fold_left (fun r1 a -> (FStar_Range.union_ranges r1 (range_of_arg a))) r)))


let mk_app : FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax  ->  (FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax * FStar_Syntax_Syntax.aqual) Prims.list  ->  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax = (fun f args -> (

let r = (range_of_args args f.FStar_Syntax_Syntax.pos)
in (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_app (((f), (args)))) FStar_Pervasives_Native.None r)))


let mk_data : FStar_Ident.lident  ->  (FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax * FStar_Syntax_Syntax.aqual) Prims.list  ->  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax = (fun l args -> (match (args) with
| [] -> begin
(

let uu____3137 = (

let uu____3140 = (

let uu____3141 = (

let uu____3148 = (FStar_Syntax_Syntax.fvar l FStar_Syntax_Syntax.Delta_constant (FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Data_ctor)))
in ((uu____3148), (FStar_Syntax_Syntax.Meta_desugared (FStar_Syntax_Syntax.Data_app))))
in FStar_Syntax_Syntax.Tm_meta (uu____3141))
in (FStar_Syntax_Syntax.mk uu____3140))
in (uu____3137 FStar_Pervasives_Native.None (FStar_Ident.range_of_lid l)))
end
| uu____3152 -> begin
(

let e = (

let uu____3164 = (FStar_Syntax_Syntax.fvar l FStar_Syntax_Syntax.Delta_constant (FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Data_ctor)))
in (mk_app uu____3164 args))
in (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_meta (((e), (FStar_Syntax_Syntax.Meta_desugared (FStar_Syntax_Syntax.Data_app))))) FStar_Pervasives_Native.None e.FStar_Syntax_Syntax.pos))
end))


let mangle_field_name : FStar_Ident.ident  ->  FStar_Ident.ident = (fun x -> (FStar_Ident.mk_ident (((Prims.strcat "__fname__" x.FStar_Ident.idText)), (x.FStar_Ident.idRange))))


let unmangle_field_name : FStar_Ident.ident  ->  FStar_Ident.ident = (fun x -> (match ((FStar_Util.starts_with x.FStar_Ident.idText "__fname__")) with
| true -> begin
(

let uu____3177 = (

let uu____3182 = (FStar_Util.substring_from x.FStar_Ident.idText (Prims.parse_int "9"))
in ((uu____3182), (x.FStar_Ident.idRange)))
in (FStar_Ident.mk_ident uu____3177))
end
| uu____3183 -> begin
x
end))


let field_projector_prefix : Prims.string = "__proj__"


let field_projector_sep : Prims.string = "__item__"


let field_projector_contains_constructor : Prims.string  ->  Prims.bool = (fun s -> (FStar_Util.starts_with s field_projector_prefix))


let mk_field_projector_name_from_string : Prims.string  ->  Prims.string  ->  Prims.string = (fun constr field -> (Prims.strcat field_projector_prefix (Prims.strcat constr (Prims.strcat field_projector_sep field))))


let mk_field_projector_name_from_ident : FStar_Ident.lident  ->  FStar_Ident.ident  ->  FStar_Ident.lident = (fun lid i -> (

let j = (unmangle_field_name i)
in (

let jtext = j.FStar_Ident.idText
in (

let newi = (match ((field_projector_contains_constructor jtext)) with
| true -> begin
j
end
| uu____3207 -> begin
(FStar_Ident.mk_ident (((mk_field_projector_name_from_string lid.FStar_Ident.ident.FStar_Ident.idText jtext)), (i.FStar_Ident.idRange)))
end)
in (FStar_Ident.lid_of_ids (FStar_List.append lid.FStar_Ident.ns ((newi)::[])))))))


let mk_field_projector_name : FStar_Ident.lident  ->  FStar_Syntax_Syntax.bv  ->  Prims.int  ->  (FStar_Ident.lident * FStar_Syntax_Syntax.bv) = (fun lid x i -> (

let nm = (

let uu____3225 = (FStar_Syntax_Syntax.is_null_bv x)
in (match (uu____3225) with
| true -> begin
(

let uu____3226 = (

let uu____3231 = (

let uu____3232 = (FStar_Util.string_of_int i)
in (Prims.strcat "_" uu____3232))
in (

let uu____3233 = (FStar_Syntax_Syntax.range_of_bv x)
in ((uu____3231), (uu____3233))))
in (FStar_Ident.mk_ident uu____3226))
end
| uu____3234 -> begin
x.FStar_Syntax_Syntax.ppname
end))
in (

let y = (

let uu___172_3236 = x
in {FStar_Syntax_Syntax.ppname = nm; FStar_Syntax_Syntax.index = uu___172_3236.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = uu___172_3236.FStar_Syntax_Syntax.sort})
in (

let uu____3237 = (mk_field_projector_name_from_ident lid nm)
in ((uu____3237), (y))))))


let set_uvar : FStar_Syntax_Syntax.uvar  ->  FStar_Syntax_Syntax.term  ->  Prims.unit = (fun uv t -> (

let uu____3246 = (FStar_Syntax_Unionfind.find uv)
in (match (uu____3246) with
| FStar_Pervasives_Native.Some (uu____3249) -> begin
(

let uu____3250 = (

let uu____3251 = (

let uu____3252 = (FStar_Syntax_Unionfind.uvar_id uv)
in (FStar_All.pipe_left FStar_Util.string_of_int uu____3252))
in (FStar_Util.format1 "Changing a fixed uvar! ?%s\n" uu____3251))
in (failwith uu____3250))
end
| uu____3253 -> begin
(FStar_Syntax_Unionfind.change uv t)
end)))


let qualifier_equal : FStar_Syntax_Syntax.qualifier  ->  FStar_Syntax_Syntax.qualifier  ->  Prims.bool = (fun q1 q2 -> (match (((q1), (q2))) with
| (FStar_Syntax_Syntax.Discriminator (l1), FStar_Syntax_Syntax.Discriminator (l2)) -> begin
(FStar_Ident.lid_equals l1 l2)
end
| (FStar_Syntax_Syntax.Projector (l1a, l1b), FStar_Syntax_Syntax.Projector (l2a, l2b)) -> begin
((FStar_Ident.lid_equals l1a l2a) && (Prims.op_Equality l1b.FStar_Ident.idText l2b.FStar_Ident.idText))
end
| (FStar_Syntax_Syntax.RecordType (ns1, f1), FStar_Syntax_Syntax.RecordType (ns2, f2)) -> begin
((((Prims.op_Equality (FStar_List.length ns1) (FStar_List.length ns2)) && (FStar_List.forall2 (fun x1 x2 -> (Prims.op_Equality x1.FStar_Ident.idText x2.FStar_Ident.idText)) f1 f2)) && (Prims.op_Equality (FStar_List.length f1) (FStar_List.length f2))) && (FStar_List.forall2 (fun x1 x2 -> (Prims.op_Equality x1.FStar_Ident.idText x2.FStar_Ident.idText)) f1 f2))
end
| (FStar_Syntax_Syntax.RecordConstructor (ns1, f1), FStar_Syntax_Syntax.RecordConstructor (ns2, f2)) -> begin
((((Prims.op_Equality (FStar_List.length ns1) (FStar_List.length ns2)) && (FStar_List.forall2 (fun x1 x2 -> (Prims.op_Equality x1.FStar_Ident.idText x2.FStar_Ident.idText)) f1 f2)) && (Prims.op_Equality (FStar_List.length f1) (FStar_List.length f2))) && (FStar_List.forall2 (fun x1 x2 -> (Prims.op_Equality x1.FStar_Ident.idText x2.FStar_Ident.idText)) f1 f2))
end
| uu____3326 -> begin
(Prims.op_Equality q1 q2)
end))


let abs : FStar_Syntax_Syntax.binders  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.residual_comp FStar_Pervasives_Native.option  ->  FStar_Syntax_Syntax.term = (fun bs t lopt -> (

let close_lopt = (fun lopt1 -> (match (lopt1) with
| FStar_Pervasives_Native.None -> begin
FStar_Pervasives_Native.None
end
| FStar_Pervasives_Native.Some (rc) -> begin
(

let uu____3360 = (

let uu___173_3361 = rc
in (

let uu____3362 = (FStar_Util.map_opt rc.FStar_Syntax_Syntax.residual_typ (FStar_Syntax_Subst.close bs))
in {FStar_Syntax_Syntax.residual_effect = uu___173_3361.FStar_Syntax_Syntax.residual_effect; FStar_Syntax_Syntax.residual_typ = uu____3362; FStar_Syntax_Syntax.residual_flags = uu___173_3361.FStar_Syntax_Syntax.residual_flags}))
in FStar_Pervasives_Native.Some (uu____3360))
end))
in (match (bs) with
| [] -> begin
t
end
| uu____3373 -> begin
(

let body = (

let uu____3375 = (FStar_Syntax_Subst.close bs t)
in (FStar_Syntax_Subst.compress uu____3375))
in (match (((body.FStar_Syntax_Syntax.n), (lopt))) with
| (FStar_Syntax_Syntax.Tm_abs (bs', t1, lopt'), FStar_Pervasives_Native.None) -> begin
(

let uu____3403 = (

let uu____3406 = (

let uu____3407 = (

let uu____3424 = (

let uu____3431 = (FStar_Syntax_Subst.close_binders bs)
in (FStar_List.append uu____3431 bs'))
in (

let uu____3442 = (close_lopt lopt')
in ((uu____3424), (t1), (uu____3442))))
in FStar_Syntax_Syntax.Tm_abs (uu____3407))
in (FStar_Syntax_Syntax.mk uu____3406))
in (uu____3403 FStar_Pervasives_Native.None t1.FStar_Syntax_Syntax.pos))
end
| uu____3458 -> begin
(

let uu____3465 = (

let uu____3468 = (

let uu____3469 = (

let uu____3486 = (FStar_Syntax_Subst.close_binders bs)
in (

let uu____3487 = (close_lopt lopt)
in ((uu____3486), (body), (uu____3487))))
in FStar_Syntax_Syntax.Tm_abs (uu____3469))
in (FStar_Syntax_Syntax.mk uu____3468))
in (uu____3465 FStar_Pervasives_Native.None t.FStar_Syntax_Syntax.pos))
end))
end)))


let arrow : (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.aqual) Prims.list  ->  FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax  ->  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax = (fun bs c -> (match (bs) with
| [] -> begin
(comp_result c)
end
| uu____3527 -> begin
(

let uu____3534 = (

let uu____3537 = (

let uu____3538 = (

let uu____3551 = (FStar_Syntax_Subst.close_binders bs)
in (

let uu____3552 = (FStar_Syntax_Subst.close_comp bs c)
in ((uu____3551), (uu____3552))))
in FStar_Syntax_Syntax.Tm_arrow (uu____3538))
in (FStar_Syntax_Syntax.mk uu____3537))
in (uu____3534 FStar_Pervasives_Native.None c.FStar_Syntax_Syntax.pos))
end))


let flat_arrow : (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.aqual) Prims.list  ->  FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax  ->  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax = (fun bs c -> (

let t = (arrow bs c)
in (

let uu____3585 = (

let uu____3586 = (FStar_Syntax_Subst.compress t)
in uu____3586.FStar_Syntax_Syntax.n)
in (match (uu____3585) with
| FStar_Syntax_Syntax.Tm_arrow (bs1, c1) -> begin
(match (c1.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Total (tres, uu____3612) -> begin
(

let uu____3621 = (

let uu____3622 = (FStar_Syntax_Subst.compress tres)
in uu____3622.FStar_Syntax_Syntax.n)
in (match (uu____3621) with
| FStar_Syntax_Syntax.Tm_arrow (bs', c') -> begin
(FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_arrow ((((FStar_List.append bs1 bs')), (c')))) FStar_Pervasives_Native.None t.FStar_Syntax_Syntax.pos)
end
| uu____3657 -> begin
t
end))
end
| uu____3658 -> begin
t
end)
end
| uu____3659 -> begin
t
end))))


let refine : FStar_Syntax_Syntax.bv  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax = (fun b t -> (

let uu____3670 = (

let uu____3671 = (FStar_Syntax_Syntax.range_of_bv b)
in (FStar_Range.union_ranges uu____3671 t.FStar_Syntax_Syntax.pos))
in (

let uu____3672 = (

let uu____3675 = (

let uu____3676 = (

let uu____3683 = (

let uu____3684 = (

let uu____3685 = (FStar_Syntax_Syntax.mk_binder b)
in (uu____3685)::[])
in (FStar_Syntax_Subst.close uu____3684 t))
in ((b), (uu____3683)))
in FStar_Syntax_Syntax.Tm_refine (uu____3676))
in (FStar_Syntax_Syntax.mk uu____3675))
in (uu____3672 FStar_Pervasives_Native.None uu____3670))))


let branch : FStar_Syntax_Syntax.branch  ->  FStar_Syntax_Syntax.branch = (fun b -> (FStar_Syntax_Subst.close_branch b))


let rec arrow_formals_comp : FStar_Syntax_Syntax.term  ->  ((FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.aqual) Prims.list * FStar_Syntax_Syntax.comp) = (fun k -> (

let k1 = (FStar_Syntax_Subst.compress k)
in (match (k1.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_arrow (bs, c) -> begin
(

let uu____3736 = (FStar_Syntax_Subst.open_comp bs c)
in (match (uu____3736) with
| (bs1, c1) -> begin
(

let uu____3753 = (is_tot_or_gtot_comp c1)
in (match (uu____3753) with
| true -> begin
(

let uu____3764 = (arrow_formals_comp (comp_result c1))
in (match (uu____3764) with
| (bs', k2) -> begin
(((FStar_List.append bs1 bs')), (k2))
end))
end
| uu____3809 -> begin
((bs1), (c1))
end))
end))
end
| uu____3810 -> begin
(

let uu____3811 = (FStar_Syntax_Syntax.mk_Total k1)
in (([]), (uu____3811)))
end)))


let rec arrow_formals : FStar_Syntax_Syntax.term  ->  ((FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.aqual) Prims.list * FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax) = (fun k -> (

let uu____3838 = (arrow_formals_comp k)
in (match (uu____3838) with
| (bs, c) -> begin
((bs), ((comp_result c)))
end)))


let abs_formals : FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.binders * FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.residual_comp FStar_Pervasives_Native.option) = (fun t -> (

let subst_lcomp_opt = (fun s l -> (match (l) with
| FStar_Pervasives_Native.Some (rc) -> begin
(

let uu____3915 = (

let uu___174_3916 = rc
in (

let uu____3917 = (FStar_Util.map_opt rc.FStar_Syntax_Syntax.residual_typ (FStar_Syntax_Subst.subst s))
in {FStar_Syntax_Syntax.residual_effect = uu___174_3916.FStar_Syntax_Syntax.residual_effect; FStar_Syntax_Syntax.residual_typ = uu____3917; FStar_Syntax_Syntax.residual_flags = uu___174_3916.FStar_Syntax_Syntax.residual_flags}))
in FStar_Pervasives_Native.Some (uu____3915))
end
| uu____3924 -> begin
l
end))
in (

let rec aux = (fun t1 abs_body_lcomp -> (

let uu____3952 = (

let uu____3953 = (

let uu____3956 = (FStar_Syntax_Subst.compress t1)
in (FStar_All.pipe_left unascribe uu____3956))
in uu____3953.FStar_Syntax_Syntax.n)
in (match (uu____3952) with
| FStar_Syntax_Syntax.Tm_abs (bs, t2, what) -> begin
(

let uu____3994 = (aux t2 what)
in (match (uu____3994) with
| (bs', t3, what1) -> begin
(((FStar_List.append bs bs')), (t3), (what1))
end))
end
| uu____4054 -> begin
(([]), (t1), (abs_body_lcomp))
end)))
in (

let uu____4067 = (aux t FStar_Pervasives_Native.None)
in (match (uu____4067) with
| (bs, t1, abs_body_lcomp) -> begin
(

let uu____4109 = (FStar_Syntax_Subst.open_term' bs t1)
in (match (uu____4109) with
| (bs1, t2, opening) -> begin
(

let abs_body_lcomp1 = (subst_lcomp_opt opening abs_body_lcomp)
in ((bs1), (t2), (abs_body_lcomp1)))
end))
end)))))


let mk_letbinding : (FStar_Syntax_Syntax.bv, FStar_Syntax_Syntax.fv) FStar_Util.either  ->  FStar_Syntax_Syntax.univ_name Prims.list  ->  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax  ->  FStar_Ident.lident  ->  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax  ->  FStar_Syntax_Syntax.letbinding = (fun lbname univ_vars typ eff def -> {FStar_Syntax_Syntax.lbname = lbname; FStar_Syntax_Syntax.lbunivs = univ_vars; FStar_Syntax_Syntax.lbtyp = typ; FStar_Syntax_Syntax.lbeff = eff; FStar_Syntax_Syntax.lbdef = def})


let close_univs_and_mk_letbinding : FStar_Syntax_Syntax.fv Prims.list FStar_Pervasives_Native.option  ->  (FStar_Syntax_Syntax.bv, FStar_Syntax_Syntax.fv) FStar_Util.either  ->  FStar_Ident.ident Prims.list  ->  FStar_Syntax_Syntax.term  ->  FStar_Ident.lident  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.letbinding = (fun recs lbname univ_vars typ eff def -> (

let def1 = (match (((recs), (univ_vars))) with
| (FStar_Pervasives_Native.None, uu____4223) -> begin
def
end
| (uu____4234, []) -> begin
def
end
| (FStar_Pervasives_Native.Some (fvs), uu____4246) -> begin
(

let universes = (FStar_All.pipe_right univ_vars (FStar_List.map (fun _0_28 -> FStar_Syntax_Syntax.U_name (_0_28))))
in (

let inst1 = (FStar_All.pipe_right fvs (FStar_List.map (fun fv -> ((fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v), (universes)))))
in (FStar_Syntax_InstFV.instantiate inst1 def)))
end)
in (

let typ1 = (FStar_Syntax_Subst.close_univ_vars univ_vars typ)
in (

let def2 = (FStar_Syntax_Subst.close_univ_vars univ_vars def1)
in (mk_letbinding lbname univ_vars typ1 eff def2)))))


let open_univ_vars_binders_and_comp : FStar_Syntax_Syntax.univ_names  ->  (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.aqual) Prims.list  ->  FStar_Syntax_Syntax.comp  ->  (FStar_Syntax_Syntax.univ_names * (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.aqual) Prims.list * FStar_Syntax_Syntax.comp) = (fun uvs binders c -> (match (binders) with
| [] -> begin
(

let uu____4349 = (FStar_Syntax_Subst.open_univ_vars_comp uvs c)
in (match (uu____4349) with
| (uvs1, c1) -> begin
((uvs1), ([]), (c1))
end))
end
| uu____4378 -> begin
(

let t' = (arrow binders c)
in (

let uu____4388 = (FStar_Syntax_Subst.open_univ_vars uvs t')
in (match (uu____4388) with
| (uvs1, t'1) -> begin
(

let uu____4407 = (

let uu____4408 = (FStar_Syntax_Subst.compress t'1)
in uu____4408.FStar_Syntax_Syntax.n)
in (match (uu____4407) with
| FStar_Syntax_Syntax.Tm_arrow (binders1, c1) -> begin
((uvs1), (binders1), (c1))
end
| uu____4449 -> begin
(failwith "Impossible")
end))
end)))
end))


let is_tuple_constructor : FStar_Syntax_Syntax.typ  ->  Prims.bool = (fun t -> (match (t.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_fvar (fv) -> begin
(FStar_Parser_Const.is_tuple_constructor_string fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v.FStar_Ident.str)
end
| uu____4467 -> begin
false
end))


let is_dtuple_constructor : FStar_Syntax_Syntax.typ  ->  Prims.bool = (fun t -> (match (t.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_fvar (fv) -> begin
(FStar_Parser_Const.is_dtuple_constructor_lid fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v)
end
| uu____4473 -> begin
false
end))


let is_lid_equality : FStar_Ident.lident  ->  Prims.bool = (fun x -> (FStar_Ident.lid_equals x FStar_Parser_Const.eq2_lid))


let is_forall : FStar_Ident.lident  ->  Prims.bool = (fun lid -> (FStar_Ident.lid_equals lid FStar_Parser_Const.forall_lid))


let is_exists : FStar_Ident.lident  ->  Prims.bool = (fun lid -> (FStar_Ident.lid_equals lid FStar_Parser_Const.exists_lid))


let is_qlid : FStar_Ident.lident  ->  Prims.bool = (fun lid -> ((is_forall lid) || (is_exists lid)))


let is_equality : FStar_Ident.lident FStar_Syntax_Syntax.withinfo_t  ->  Prims.bool = (fun x -> (is_lid_equality x.FStar_Syntax_Syntax.v))


let lid_is_connective : FStar_Ident.lident  ->  Prims.bool = (

let lst = (FStar_Parser_Const.and_lid)::(FStar_Parser_Const.or_lid)::(FStar_Parser_Const.not_lid)::(FStar_Parser_Const.iff_lid)::(FStar_Parser_Const.imp_lid)::[]
in (fun lid -> (FStar_Util.for_some (FStar_Ident.lid_equals lid) lst)))


let is_constructor : FStar_Syntax_Syntax.term  ->  FStar_Ident.lident  ->  Prims.bool = (fun t lid -> (

let uu____4513 = (

let uu____4514 = (pre_typ t)
in uu____4514.FStar_Syntax_Syntax.n)
in (match (uu____4513) with
| FStar_Syntax_Syntax.Tm_fvar (tc) -> begin
(FStar_Ident.lid_equals tc.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v lid)
end
| uu____4518 -> begin
false
end)))


let rec is_constructed_typ : FStar_Syntax_Syntax.term  ->  FStar_Ident.lident  ->  Prims.bool = (fun t lid -> (

let uu____4527 = (

let uu____4528 = (pre_typ t)
in uu____4528.FStar_Syntax_Syntax.n)
in (match (uu____4527) with
| FStar_Syntax_Syntax.Tm_fvar (uu____4531) -> begin
(is_constructor t lid)
end
| FStar_Syntax_Syntax.Tm_app (t1, uu____4533) -> begin
(is_constructed_typ t1 lid)
end
| uu____4554 -> begin
false
end)))


let rec get_tycon : FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term FStar_Pervasives_Native.option = (fun t -> (

let t1 = (pre_typ t)
in (match (t1.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_bvar (uu____4564) -> begin
FStar_Pervasives_Native.Some (t1)
end
| FStar_Syntax_Syntax.Tm_name (uu____4565) -> begin
FStar_Pervasives_Native.Some (t1)
end
| FStar_Syntax_Syntax.Tm_fvar (uu____4566) -> begin
FStar_Pervasives_Native.Some (t1)
end
| FStar_Syntax_Syntax.Tm_app (t2, uu____4568) -> begin
(get_tycon t2)
end
| uu____4589 -> begin
FStar_Pervasives_Native.None
end)))


let is_interpreted : FStar_Ident.lident  ->  Prims.bool = (fun l -> (

let theory_syms = (FStar_Parser_Const.op_Eq)::(FStar_Parser_Const.op_notEq)::(FStar_Parser_Const.op_LT)::(FStar_Parser_Const.op_LTE)::(FStar_Parser_Const.op_GT)::(FStar_Parser_Const.op_GTE)::(FStar_Parser_Const.op_Subtraction)::(FStar_Parser_Const.op_Minus)::(FStar_Parser_Const.op_Addition)::(FStar_Parser_Const.op_Multiply)::(FStar_Parser_Const.op_Division)::(FStar_Parser_Const.op_Modulus)::(FStar_Parser_Const.op_And)::(FStar_Parser_Const.op_Or)::(FStar_Parser_Const.op_Negation)::[]
in (FStar_Util.for_some (FStar_Ident.lid_equals l) theory_syms)))


let is_fstar_tactics_embed : FStar_Syntax_Syntax.term  ->  Prims.bool = (fun t -> (

let uu____4601 = (

let uu____4602 = (un_uinst t)
in uu____4602.FStar_Syntax_Syntax.n)
in (match (uu____4601) with
| FStar_Syntax_Syntax.Tm_fvar (fv) -> begin
(FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.fstar_refl_embed_lid)
end
| uu____4606 -> begin
false
end)))


let is_fstar_tactics_quote : FStar_Syntax_Syntax.term  ->  Prims.bool = (fun t -> (

let uu____4611 = (

let uu____4612 = (un_uinst t)
in uu____4612.FStar_Syntax_Syntax.n)
in (match (uu____4611) with
| FStar_Syntax_Syntax.Tm_fvar (fv) -> begin
(FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.quote_lid)
end
| uu____4616 -> begin
false
end)))


let is_fstar_tactics_by_tactic : FStar_Syntax_Syntax.term  ->  Prims.bool = (fun t -> (

let uu____4621 = (

let uu____4622 = (un_uinst t)
in uu____4622.FStar_Syntax_Syntax.n)
in (match (uu____4621) with
| FStar_Syntax_Syntax.Tm_fvar (fv) -> begin
(FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.by_tactic_lid)
end
| uu____4626 -> begin
false
end)))


let ktype : FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_type (FStar_Syntax_Syntax.U_unknown)) FStar_Pervasives_Native.None FStar_Range.dummyRange)


let ktype0 : FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_type (FStar_Syntax_Syntax.U_zero)) FStar_Pervasives_Native.None FStar_Range.dummyRange)


let type_u : Prims.unit  ->  (FStar_Syntax_Syntax.typ * FStar_Syntax_Syntax.universe) = (fun uu____4638 -> (

let u = (

let uu____4644 = (FStar_Syntax_Unionfind.univ_fresh ())
in (FStar_All.pipe_left (fun _0_29 -> FStar_Syntax_Syntax.U_unif (_0_29)) uu____4644))
in (

let uu____4661 = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_type (u)) FStar_Pervasives_Native.None FStar_Range.dummyRange)
in ((uu____4661), (u)))))


let attr_substitute : FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax = (

let uu____4668 = (

let uu____4671 = (

let uu____4672 = (

let uu____4673 = (FStar_Ident.lid_of_path (("FStar")::("Pervasives")::("Substitute")::[]) FStar_Range.dummyRange)
in (FStar_Syntax_Syntax.lid_as_fv uu____4673 FStar_Syntax_Syntax.Delta_constant FStar_Pervasives_Native.None))
in FStar_Syntax_Syntax.Tm_fvar (uu____4672))
in (FStar_Syntax_Syntax.mk uu____4671))
in (uu____4668 FStar_Pervasives_Native.None FStar_Range.dummyRange))


let exp_true_bool : FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_bool (true))) FStar_Pervasives_Native.None FStar_Range.dummyRange)


let exp_false_bool : FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_bool (false))) FStar_Pervasives_Native.None FStar_Range.dummyRange)


let exp_unit : FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_unit)) FStar_Pervasives_Native.None FStar_Range.dummyRange)


let exp_int : Prims.string  ->  FStar_Syntax_Syntax.term = (fun s -> (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_int (((s), (FStar_Pervasives_Native.None))))) FStar_Pervasives_Native.None FStar_Range.dummyRange))


let exp_string : Prims.string  ->  FStar_Syntax_Syntax.term = (fun s -> (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_string (((s), (FStar_Range.dummyRange))))) FStar_Pervasives_Native.None FStar_Range.dummyRange))


let fvar_const : FStar_Ident.lident  ->  FStar_Syntax_Syntax.term = (fun l -> (FStar_Syntax_Syntax.fvar l FStar_Syntax_Syntax.Delta_constant FStar_Pervasives_Native.None))


let tand : FStar_Syntax_Syntax.term = (fvar_const FStar_Parser_Const.and_lid)


let tor : FStar_Syntax_Syntax.term = (fvar_const FStar_Parser_Const.or_lid)


let timp : FStar_Syntax_Syntax.term = (FStar_Syntax_Syntax.fvar FStar_Parser_Const.imp_lid (FStar_Syntax_Syntax.Delta_defined_at_level ((Prims.parse_int "1"))) FStar_Pervasives_Native.None)


let tiff : FStar_Syntax_Syntax.term = (FStar_Syntax_Syntax.fvar FStar_Parser_Const.iff_lid (FStar_Syntax_Syntax.Delta_defined_at_level ((Prims.parse_int "2"))) FStar_Pervasives_Native.None)


let t_bool : FStar_Syntax_Syntax.term = (fvar_const FStar_Parser_Const.bool_lid)


let t_false : FStar_Syntax_Syntax.term = (fvar_const FStar_Parser_Const.false_lid)


let t_true : FStar_Syntax_Syntax.term = (fvar_const FStar_Parser_Const.true_lid)


let b2t_v : FStar_Syntax_Syntax.term = (fvar_const FStar_Parser_Const.b2t_lid)


let t_not : FStar_Syntax_Syntax.term = (fvar_const FStar_Parser_Const.not_lid)


let mk_conj_opt : FStar_Syntax_Syntax.term FStar_Pervasives_Native.option  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term FStar_Pervasives_Native.option = (fun phi1 phi2 -> (match (phi1) with
| FStar_Pervasives_Native.None -> begin
FStar_Pervasives_Native.Some (phi2)
end
| FStar_Pervasives_Native.Some (phi11) -> begin
(

let uu____4722 = (

let uu____4725 = (FStar_Range.union_ranges phi11.FStar_Syntax_Syntax.pos phi2.FStar_Syntax_Syntax.pos)
in (

let uu____4726 = (

let uu____4729 = (

let uu____4730 = (

let uu____4745 = (

let uu____4748 = (FStar_Syntax_Syntax.as_arg phi11)
in (

let uu____4749 = (

let uu____4752 = (FStar_Syntax_Syntax.as_arg phi2)
in (uu____4752)::[])
in (uu____4748)::uu____4749))
in ((tand), (uu____4745)))
in FStar_Syntax_Syntax.Tm_app (uu____4730))
in (FStar_Syntax_Syntax.mk uu____4729))
in (uu____4726 FStar_Pervasives_Native.None uu____4725)))
in FStar_Pervasives_Native.Some (uu____4722))
end))


let mk_binop : FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax = (fun op_t phi1 phi2 -> (

let uu____4778 = (FStar_Range.union_ranges phi1.FStar_Syntax_Syntax.pos phi2.FStar_Syntax_Syntax.pos)
in (

let uu____4779 = (

let uu____4782 = (

let uu____4783 = (

let uu____4798 = (

let uu____4801 = (FStar_Syntax_Syntax.as_arg phi1)
in (

let uu____4802 = (

let uu____4805 = (FStar_Syntax_Syntax.as_arg phi2)
in (uu____4805)::[])
in (uu____4801)::uu____4802))
in ((op_t), (uu____4798)))
in FStar_Syntax_Syntax.Tm_app (uu____4783))
in (FStar_Syntax_Syntax.mk uu____4782))
in (uu____4779 FStar_Pervasives_Native.None uu____4778))))


let mk_neg : FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax = (fun phi -> (

let uu____4819 = (

let uu____4822 = (

let uu____4823 = (

let uu____4838 = (

let uu____4841 = (FStar_Syntax_Syntax.as_arg phi)
in (uu____4841)::[])
in ((t_not), (uu____4838)))
in FStar_Syntax_Syntax.Tm_app (uu____4823))
in (FStar_Syntax_Syntax.mk uu____4822))
in (uu____4819 FStar_Pervasives_Native.None phi.FStar_Syntax_Syntax.pos)))


let mk_conj : FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax = (fun phi1 phi2 -> (mk_binop tand phi1 phi2))


let mk_conj_l : FStar_Syntax_Syntax.term Prims.list  ->  FStar_Syntax_Syntax.term = (fun phi -> (match (phi) with
| [] -> begin
(FStar_Syntax_Syntax.fvar FStar_Parser_Const.true_lid FStar_Syntax_Syntax.Delta_constant FStar_Pervasives_Native.None)
end
| (hd1)::tl1 -> begin
(FStar_List.fold_right mk_conj tl1 hd1)
end))


let mk_disj : FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax = (fun phi1 phi2 -> (mk_binop tor phi1 phi2))


let mk_disj_l : FStar_Syntax_Syntax.term Prims.list  ->  FStar_Syntax_Syntax.term = (fun phi -> (match (phi) with
| [] -> begin
t_false
end
| (hd1)::tl1 -> begin
(FStar_List.fold_right mk_disj tl1 hd1)
end))


let mk_imp : FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term = (fun phi1 phi2 -> (mk_binop timp phi1 phi2))


let mk_iff : FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term = (fun phi1 phi2 -> (mk_binop tiff phi1 phi2))


let b2t : FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax = (fun e -> (

let uu____4913 = (

let uu____4916 = (

let uu____4917 = (

let uu____4932 = (

let uu____4935 = (FStar_Syntax_Syntax.as_arg e)
in (uu____4935)::[])
in ((b2t_v), (uu____4932)))
in FStar_Syntax_Syntax.Tm_app (uu____4917))
in (FStar_Syntax_Syntax.mk uu____4916))
in (uu____4913 FStar_Pervasives_Native.None e.FStar_Syntax_Syntax.pos)))


let teq : FStar_Syntax_Syntax.term = (fvar_const FStar_Parser_Const.eq2_lid)


let mk_untyped_eq2 : FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax = (fun e1 e2 -> (

let uu____4951 = (FStar_Range.union_ranges e1.FStar_Syntax_Syntax.pos e2.FStar_Syntax_Syntax.pos)
in (

let uu____4952 = (

let uu____4955 = (

let uu____4956 = (

let uu____4971 = (

let uu____4974 = (FStar_Syntax_Syntax.as_arg e1)
in (

let uu____4975 = (

let uu____4978 = (FStar_Syntax_Syntax.as_arg e2)
in (uu____4978)::[])
in (uu____4974)::uu____4975))
in ((teq), (uu____4971)))
in FStar_Syntax_Syntax.Tm_app (uu____4956))
in (FStar_Syntax_Syntax.mk uu____4955))
in (uu____4952 FStar_Pervasives_Native.None uu____4951))))


let mk_eq2 : FStar_Syntax_Syntax.universe  ->  FStar_Syntax_Syntax.typ  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term = (fun u t e1 e2 -> (

let eq_inst = (FStar_Syntax_Syntax.mk_Tm_uinst teq ((u)::[]))
in (

let uu____5001 = (FStar_Range.union_ranges e1.FStar_Syntax_Syntax.pos e2.FStar_Syntax_Syntax.pos)
in (

let uu____5002 = (

let uu____5005 = (

let uu____5006 = (

let uu____5021 = (

let uu____5024 = (FStar_Syntax_Syntax.iarg t)
in (

let uu____5025 = (

let uu____5028 = (FStar_Syntax_Syntax.as_arg e1)
in (

let uu____5029 = (

let uu____5032 = (FStar_Syntax_Syntax.as_arg e2)
in (uu____5032)::[])
in (uu____5028)::uu____5029))
in (uu____5024)::uu____5025))
in ((eq_inst), (uu____5021)))
in FStar_Syntax_Syntax.Tm_app (uu____5006))
in (FStar_Syntax_Syntax.mk uu____5005))
in (uu____5002 FStar_Pervasives_Native.None uu____5001)))))


let mk_has_type : FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax = (fun t x t' -> (

let t_has_type = (fvar_const FStar_Parser_Const.has_type_lid)
in (

let t_has_type1 = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_uinst (((t_has_type), ((FStar_Syntax_Syntax.U_zero)::(FStar_Syntax_Syntax.U_zero)::[])))) FStar_Pervasives_Native.None FStar_Range.dummyRange)
in (

let uu____5058 = (

let uu____5061 = (

let uu____5062 = (

let uu____5077 = (

let uu____5080 = (FStar_Syntax_Syntax.iarg t)
in (

let uu____5081 = (

let uu____5084 = (FStar_Syntax_Syntax.as_arg x)
in (

let uu____5085 = (

let uu____5088 = (FStar_Syntax_Syntax.as_arg t')
in (uu____5088)::[])
in (uu____5084)::uu____5085))
in (uu____5080)::uu____5081))
in ((t_has_type1), (uu____5077)))
in FStar_Syntax_Syntax.Tm_app (uu____5062))
in (FStar_Syntax_Syntax.mk uu____5061))
in (uu____5058 FStar_Pervasives_Native.None FStar_Range.dummyRange)))))


let lex_t : FStar_Syntax_Syntax.term = (fvar_const FStar_Parser_Const.lex_t_lid)


let lex_top : FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax = (

let uu____5098 = (

let uu____5101 = (

let uu____5102 = (

let uu____5109 = (FStar_Syntax_Syntax.fvar FStar_Parser_Const.lextop_lid FStar_Syntax_Syntax.Delta_constant (FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Data_ctor)))
in ((uu____5109), ((FStar_Syntax_Syntax.U_zero)::[])))
in FStar_Syntax_Syntax.Tm_uinst (uu____5102))
in (FStar_Syntax_Syntax.mk uu____5101))
in (uu____5098 FStar_Pervasives_Native.None FStar_Range.dummyRange))


let lex_pair : FStar_Syntax_Syntax.term = (FStar_Syntax_Syntax.fvar FStar_Parser_Const.lexcons_lid FStar_Syntax_Syntax.Delta_constant (FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Data_ctor)))


let tforall : FStar_Syntax_Syntax.term = (FStar_Syntax_Syntax.fvar FStar_Parser_Const.forall_lid (FStar_Syntax_Syntax.Delta_defined_at_level ((Prims.parse_int "1"))) FStar_Pervasives_Native.None)


let t_haseq : FStar_Syntax_Syntax.term = (FStar_Syntax_Syntax.fvar FStar_Parser_Const.haseq_lid FStar_Syntax_Syntax.Delta_constant FStar_Pervasives_Native.None)


let lcomp_of_comp : FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax  ->  FStar_Syntax_Syntax.lcomp = (fun c0 -> (

let uu____5123 = (match (c0.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Total (uu____5136) -> begin
((FStar_Parser_Const.effect_Tot_lid), ((FStar_Syntax_Syntax.TOTAL)::[]))
end
| FStar_Syntax_Syntax.GTotal (uu____5147) -> begin
((FStar_Parser_Const.effect_GTot_lid), ((FStar_Syntax_Syntax.SOMETRIVIAL)::[]))
end
| FStar_Syntax_Syntax.Comp (c) -> begin
((c.FStar_Syntax_Syntax.effect_name), (c.FStar_Syntax_Syntax.flags))
end)
in (match (uu____5123) with
| (eff_name, flags) -> begin
{FStar_Syntax_Syntax.eff_name = eff_name; FStar_Syntax_Syntax.res_typ = (comp_result c0); FStar_Syntax_Syntax.cflags = flags; FStar_Syntax_Syntax.comp = (fun uu____5168 -> c0)}
end)))


let mk_residual_comp : FStar_Ident.lident  ->  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax FStar_Pervasives_Native.option  ->  FStar_Syntax_Syntax.cflags Prims.list  ->  FStar_Syntax_Syntax.residual_comp = (fun l t f -> {FStar_Syntax_Syntax.residual_effect = l; FStar_Syntax_Syntax.residual_typ = t; FStar_Syntax_Syntax.residual_flags = f})


let residual_tot : FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax  ->  FStar_Syntax_Syntax.residual_comp = (fun t -> {FStar_Syntax_Syntax.residual_effect = FStar_Parser_Const.effect_Tot_lid; FStar_Syntax_Syntax.residual_typ = FStar_Pervasives_Native.Some (t); FStar_Syntax_Syntax.residual_flags = (FStar_Syntax_Syntax.TOTAL)::[]})


let residual_comp_of_comp : FStar_Syntax_Syntax.comp  ->  FStar_Syntax_Syntax.residual_comp = (fun c -> {FStar_Syntax_Syntax.residual_effect = (comp_effect_name c); FStar_Syntax_Syntax.residual_typ = FStar_Pervasives_Native.Some ((comp_result c)); FStar_Syntax_Syntax.residual_flags = (comp_flags c)})


let residual_comp_of_lcomp : FStar_Syntax_Syntax.lcomp  ->  FStar_Syntax_Syntax.residual_comp = (fun lc -> {FStar_Syntax_Syntax.residual_effect = lc.FStar_Syntax_Syntax.eff_name; FStar_Syntax_Syntax.residual_typ = FStar_Pervasives_Native.Some (lc.FStar_Syntax_Syntax.res_typ); FStar_Syntax_Syntax.residual_flags = lc.FStar_Syntax_Syntax.cflags})


let mk_forall_aux : FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax  ->  FStar_Syntax_Syntax.bv  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax = (fun fa x body -> (

let uu____5233 = (

let uu____5236 = (

let uu____5237 = (

let uu____5252 = (

let uu____5255 = (FStar_Syntax_Syntax.iarg x.FStar_Syntax_Syntax.sort)
in (

let uu____5256 = (

let uu____5259 = (

let uu____5260 = (

let uu____5261 = (

let uu____5262 = (FStar_Syntax_Syntax.mk_binder x)
in (uu____5262)::[])
in (abs uu____5261 body (FStar_Pervasives_Native.Some ((residual_tot ktype0)))))
in (FStar_Syntax_Syntax.as_arg uu____5260))
in (uu____5259)::[])
in (uu____5255)::uu____5256))
in ((fa), (uu____5252)))
in FStar_Syntax_Syntax.Tm_app (uu____5237))
in (FStar_Syntax_Syntax.mk uu____5236))
in (uu____5233 FStar_Pervasives_Native.None FStar_Range.dummyRange)))


let mk_forall_no_univ : FStar_Syntax_Syntax.bv  ->  FStar_Syntax_Syntax.typ  ->  FStar_Syntax_Syntax.typ = (fun x body -> (mk_forall_aux tforall x body))


let mk_forall : FStar_Syntax_Syntax.universe  ->  FStar_Syntax_Syntax.bv  ->  FStar_Syntax_Syntax.typ  ->  FStar_Syntax_Syntax.typ = (fun u x body -> (

let tforall1 = (FStar_Syntax_Syntax.mk_Tm_uinst tforall ((u)::[]))
in (mk_forall_aux tforall1 x body)))


let close_forall_no_univs : FStar_Syntax_Syntax.binder Prims.list  ->  FStar_Syntax_Syntax.typ  ->  FStar_Syntax_Syntax.typ = (fun bs f -> (FStar_List.fold_right (fun b f1 -> (

let uu____5308 = (FStar_Syntax_Syntax.is_null_binder b)
in (match (uu____5308) with
| true -> begin
f1
end
| uu____5309 -> begin
(mk_forall_no_univ (FStar_Pervasives_Native.fst b) f1)
end))) bs f))


let rec is_wild_pat : FStar_Syntax_Syntax.pat' FStar_Syntax_Syntax.withinfo_t  ->  Prims.bool = (fun p -> (match (p.FStar_Syntax_Syntax.v) with
| FStar_Syntax_Syntax.Pat_wild (uu____5318) -> begin
true
end
| uu____5319 -> begin
false
end))


let if_then_else : FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax  ->  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax  ->  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax  ->  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax = (fun b t1 t2 -> (

let then_branch = (

let uu____5361 = (FStar_Syntax_Syntax.withinfo (FStar_Syntax_Syntax.Pat_constant (FStar_Const.Const_bool (true))) t1.FStar_Syntax_Syntax.pos)
in ((uu____5361), (FStar_Pervasives_Native.None), (t1)))
in (

let else_branch = (

let uu____5389 = (FStar_Syntax_Syntax.withinfo (FStar_Syntax_Syntax.Pat_constant (FStar_Const.Const_bool (false))) t2.FStar_Syntax_Syntax.pos)
in ((uu____5389), (FStar_Pervasives_Native.None), (t2)))
in (

let uu____5402 = (

let uu____5403 = (FStar_Range.union_ranges t1.FStar_Syntax_Syntax.pos t2.FStar_Syntax_Syntax.pos)
in (FStar_Range.union_ranges b.FStar_Syntax_Syntax.pos uu____5403))
in (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_match (((b), ((then_branch)::(else_branch)::[])))) FStar_Pervasives_Native.None uu____5402)))))


let mk_squash : FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax = (fun p -> (

let sq = (FStar_Syntax_Syntax.fvar FStar_Parser_Const.squash_lid (FStar_Syntax_Syntax.Delta_defined_at_level ((Prims.parse_int "1"))) FStar_Pervasives_Native.None)
in (

let uu____5471 = (FStar_Syntax_Syntax.mk_Tm_uinst sq ((FStar_Syntax_Syntax.U_zero)::[]))
in (

let uu____5474 = (

let uu____5483 = (FStar_Syntax_Syntax.as_arg p)
in (uu____5483)::[])
in (mk_app uu____5471 uu____5474)))))


let un_squash : FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax FStar_Pervasives_Native.option = (fun t -> (

let uu____5492 = (head_and_args t)
in (match (uu____5492) with
| (head1, args) -> begin
(

let uu____5533 = (

let uu____5546 = (

let uu____5547 = (un_uinst head1)
in uu____5547.FStar_Syntax_Syntax.n)
in ((uu____5546), (args)))
in (match (uu____5533) with
| (FStar_Syntax_Syntax.Tm_fvar (fv), ((p, uu____5564))::[]) when (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.squash_lid) -> begin
FStar_Pervasives_Native.Some (p)
end
| (FStar_Syntax_Syntax.Tm_refine (b, p), []) -> begin
(match (b.FStar_Syntax_Syntax.sort.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_fvar (fv) when (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.unit_lid) -> begin
(

let uu____5616 = (

let uu____5621 = (

let uu____5622 = (FStar_Syntax_Syntax.mk_binder b)
in (uu____5622)::[])
in (FStar_Syntax_Subst.open_term uu____5621 p))
in (match (uu____5616) with
| (bs, p1) -> begin
(

let b1 = (match (bs) with
| (b1)::[] -> begin
b1
end
| uu____5651 -> begin
(failwith "impossible")
end)
in (

let uu____5656 = (

let uu____5657 = (FStar_Syntax_Free.names p1)
in (FStar_Util.set_mem (FStar_Pervasives_Native.fst b1) uu____5657))
in (match (uu____5656) with
| true -> begin
FStar_Pervasives_Native.None
end
| uu____5666 -> begin
FStar_Pervasives_Native.Some (p1)
end)))
end))
end
| uu____5667 -> begin
FStar_Pervasives_Native.None
end)
end
| uu____5670 -> begin
FStar_Pervasives_Native.None
end))
end)))


let arrow_one : FStar_Syntax_Syntax.typ  ->  (FStar_Syntax_Syntax.binder * FStar_Syntax_Syntax.comp) FStar_Pervasives_Native.option = (fun t -> (

let uu____5701 = (

let uu____5714 = (

let uu____5715 = (FStar_Syntax_Subst.compress t)
in uu____5715.FStar_Syntax_Syntax.n)
in (match (uu____5714) with
| FStar_Syntax_Syntax.Tm_arrow ([], c) -> begin
(failwith "fatal: empty binders on arrow?")
end
| FStar_Syntax_Syntax.Tm_arrow ((b)::[], c) -> begin
FStar_Pervasives_Native.Some (((b), (c)))
end
| FStar_Syntax_Syntax.Tm_arrow ((b)::bs, c) -> begin
(

let uu____5824 = (

let uu____5833 = (

let uu____5834 = (arrow bs c)
in (FStar_Syntax_Syntax.mk_Total uu____5834))
in ((b), (uu____5833)))
in FStar_Pervasives_Native.Some (uu____5824))
end
| uu____5847 -> begin
FStar_Pervasives_Native.None
end))
in (FStar_Util.bind_opt uu____5701 (fun uu____5883 -> (match (uu____5883) with
| (b, c) -> begin
(

let uu____5918 = (FStar_Syntax_Subst.open_comp ((b)::[]) c)
in (match (uu____5918) with
| (bs, c1) -> begin
(

let b1 = (match (bs) with
| (b1)::[] -> begin
b1
end
| uu____5965 -> begin
(failwith "impossible: open_comp returned different amount of binders")
end)
in FStar_Pervasives_Native.Some (((b1), (c1))))
end))
end)))))


let is_free_in : FStar_Syntax_Syntax.bv  ->  FStar_Syntax_Syntax.term  ->  Prims.bool = (fun bv t -> (

let uu____5990 = (FStar_Syntax_Free.names t)
in (FStar_Util.set_mem bv uu____5990)))


type qpats =
FStar_Syntax_Syntax.args Prims.list

type connective =
| QAll of (FStar_Syntax_Syntax.binders * qpats * FStar_Syntax_Syntax.typ)
| QEx of (FStar_Syntax_Syntax.binders * qpats * FStar_Syntax_Syntax.typ)
| BaseConn of (FStar_Ident.lident * FStar_Syntax_Syntax.args)


let uu___is_QAll : connective  ->  Prims.bool = (fun projectee -> (match (projectee) with
| QAll (_0) -> begin
true
end
| uu____6034 -> begin
false
end))


let __proj__QAll__item___0 : connective  ->  (FStar_Syntax_Syntax.binders * qpats * FStar_Syntax_Syntax.typ) = (fun projectee -> (match (projectee) with
| QAll (_0) -> begin
_0
end))


let uu___is_QEx : connective  ->  Prims.bool = (fun projectee -> (match (projectee) with
| QEx (_0) -> begin
true
end
| uu____6072 -> begin
false
end))


let __proj__QEx__item___0 : connective  ->  (FStar_Syntax_Syntax.binders * qpats * FStar_Syntax_Syntax.typ) = (fun projectee -> (match (projectee) with
| QEx (_0) -> begin
_0
end))


let uu___is_BaseConn : connective  ->  Prims.bool = (fun projectee -> (match (projectee) with
| BaseConn (_0) -> begin
true
end
| uu____6108 -> begin
false
end))


let __proj__BaseConn__item___0 : connective  ->  (FStar_Ident.lident * FStar_Syntax_Syntax.args) = (fun projectee -> (match (projectee) with
| BaseConn (_0) -> begin
_0
end))


let destruct_typ_as_formula : FStar_Syntax_Syntax.term  ->  connective FStar_Pervasives_Native.option = (fun f -> (

let rec unmeta_monadic = (fun f1 -> (

let f2 = (FStar_Syntax_Subst.compress f1)
in (match (f2.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_meta (t, FStar_Syntax_Syntax.Meta_monadic (uu____6143)) -> begin
(unmeta_monadic t)
end
| FStar_Syntax_Syntax.Tm_meta (t, FStar_Syntax_Syntax.Meta_monadic_lift (uu____6155)) -> begin
(unmeta_monadic t)
end
| uu____6168 -> begin
f2
end)))
in (

let destruct_base_conn = (fun f1 -> (

let connectives = (((FStar_Parser_Const.true_lid), ((Prims.parse_int "0"))))::(((FStar_Parser_Const.false_lid), ((Prims.parse_int "0"))))::(((FStar_Parser_Const.and_lid), ((Prims.parse_int "2"))))::(((FStar_Parser_Const.or_lid), ((Prims.parse_int "2"))))::(((FStar_Parser_Const.imp_lid), ((Prims.parse_int "2"))))::(((FStar_Parser_Const.iff_lid), ((Prims.parse_int "2"))))::(((FStar_Parser_Const.ite_lid), ((Prims.parse_int "3"))))::(((FStar_Parser_Const.not_lid), ((Prims.parse_int "1"))))::(((FStar_Parser_Const.eq2_lid), ((Prims.parse_int "3"))))::(((FStar_Parser_Const.eq2_lid), ((Prims.parse_int "2"))))::(((FStar_Parser_Const.eq3_lid), ((Prims.parse_int "4"))))::(((FStar_Parser_Const.eq3_lid), ((Prims.parse_int "2"))))::[]
in (

let aux = (fun f2 uu____6246 -> (match (uu____6246) with
| (lid, arity) -> begin
(

let uu____6255 = (

let uu____6270 = (unmeta_monadic f2)
in (head_and_args uu____6270))
in (match (uu____6255) with
| (t, args) -> begin
(

let t1 = (un_uinst t)
in (

let uu____6296 = ((is_constructor t1 lid) && (Prims.op_Equality (FStar_List.length args) arity))
in (match (uu____6296) with
| true -> begin
FStar_Pervasives_Native.Some (BaseConn (((lid), (args))))
end
| uu____6317 -> begin
FStar_Pervasives_Native.None
end)))
end))
end))
in (FStar_Util.find_map connectives (aux f1)))))
in (

let patterns = (fun t -> (

let t1 = (FStar_Syntax_Subst.compress t)
in (match (t1.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_meta (t2, FStar_Syntax_Syntax.Meta_pattern (pats)) -> begin
(

let uu____6371 = (FStar_Syntax_Subst.compress t2)
in ((pats), (uu____6371)))
end
| uu____6382 -> begin
(

let uu____6383 = (FStar_Syntax_Subst.compress t1)
in (([]), (uu____6383)))
end)))
in (

let destruct_q_conn = (fun t -> (

let is_q = (fun fa fv -> (match (fa) with
| true -> begin
(is_forall fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v)
end
| uu____6415 -> begin
(is_exists fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v)
end))
in (

let flat = (fun t1 -> (

let uu____6430 = (head_and_args t1)
in (match (uu____6430) with
| (t2, args) -> begin
(

let uu____6477 = (un_uinst t2)
in (

let uu____6478 = (FStar_All.pipe_right args (FStar_List.map (fun uu____6511 -> (match (uu____6511) with
| (t3, imp) -> begin
(

let uu____6522 = (unascribe t3)
in ((uu____6522), (imp)))
end))))
in ((uu____6477), (uu____6478))))
end)))
in (

let rec aux = (fun qopt out t1 -> (

let uu____6557 = (

let uu____6574 = (flat t1)
in ((qopt), (uu____6574)))
in (match (uu____6557) with
| (FStar_Pervasives_Native.Some (fa), ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar (tc); FStar_Syntax_Syntax.pos = uu____6601; FStar_Syntax_Syntax.vars = uu____6602}, (({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_abs ((b)::[], t2, uu____6605); FStar_Syntax_Syntax.pos = uu____6606; FStar_Syntax_Syntax.vars = uu____6607}, uu____6608))::[])) when (is_q fa tc) -> begin
(aux qopt ((b)::out) t2)
end
| (FStar_Pervasives_Native.Some (fa), ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar (tc); FStar_Syntax_Syntax.pos = uu____6685; FStar_Syntax_Syntax.vars = uu____6686}, (uu____6687)::(({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_abs ((b)::[], t2, uu____6690); FStar_Syntax_Syntax.pos = uu____6691; FStar_Syntax_Syntax.vars = uu____6692}, uu____6693))::[])) when (is_q fa tc) -> begin
(aux qopt ((b)::out) t2)
end
| (FStar_Pervasives_Native.None, ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar (tc); FStar_Syntax_Syntax.pos = uu____6781; FStar_Syntax_Syntax.vars = uu____6782}, (({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_abs ((b)::[], t2, uu____6785); FStar_Syntax_Syntax.pos = uu____6786; FStar_Syntax_Syntax.vars = uu____6787}, uu____6788))::[])) when (is_qlid tc.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v) -> begin
(aux (FStar_Pervasives_Native.Some ((is_forall tc.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v))) ((b)::out) t2)
end
| (FStar_Pervasives_Native.None, ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar (tc); FStar_Syntax_Syntax.pos = uu____6864; FStar_Syntax_Syntax.vars = uu____6865}, (uu____6866)::(({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_abs ((b)::[], t2, uu____6869); FStar_Syntax_Syntax.pos = uu____6870; FStar_Syntax_Syntax.vars = uu____6871}, uu____6872))::[])) when (is_qlid tc.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v) -> begin
(aux (FStar_Pervasives_Native.Some ((is_forall tc.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v))) ((b)::out) t2)
end
| (FStar_Pervasives_Native.Some (b), uu____6960) -> begin
(

let bs = (FStar_List.rev out)
in (

let uu____6994 = (FStar_Syntax_Subst.open_term bs t1)
in (match (uu____6994) with
| (bs1, t2) -> begin
(

let uu____7003 = (patterns t2)
in (match (uu____7003) with
| (pats, body) -> begin
(match (b) with
| true -> begin
FStar_Pervasives_Native.Some (QAll (((bs1), (pats), (body))))
end
| uu____7054 -> begin
FStar_Pervasives_Native.Some (QEx (((bs1), (pats), (body))))
end)
end))
end)))
end
| uu____7065 -> begin
FStar_Pervasives_Native.None
end)))
in (aux FStar_Pervasives_Native.None [] t)))))
in (

let u_connectives = (((FStar_Parser_Const.true_lid), (FStar_Parser_Const.c_true_lid), ((Prims.parse_int "0"))))::(((FStar_Parser_Const.false_lid), (FStar_Parser_Const.c_false_lid), ((Prims.parse_int "0"))))::(((FStar_Parser_Const.and_lid), (FStar_Parser_Const.c_and_lid), ((Prims.parse_int "2"))))::(((FStar_Parser_Const.or_lid), (FStar_Parser_Const.c_or_lid), ((Prims.parse_int "2"))))::[]
in (

let destruct_sq_base_conn = (fun t -> (

let uu____7131 = (un_squash t)
in (FStar_Util.bind_opt uu____7131 (fun t1 -> (

let uu____7147 = (head_and_args' t1)
in (match (uu____7147) with
| (hd1, args) -> begin
(

let uu____7180 = (

let uu____7185 = (

let uu____7186 = (un_uinst hd1)
in uu____7186.FStar_Syntax_Syntax.n)
in ((uu____7185), ((FStar_List.length args))))
in (match (uu____7180) with
| (FStar_Syntax_Syntax.Tm_fvar (fv), _0_30) when ((_0_30 = (Prims.parse_int "2")) && (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.c_and_lid)) -> begin
FStar_Pervasives_Native.Some (BaseConn (((FStar_Parser_Const.and_lid), (args))))
end
| (FStar_Syntax_Syntax.Tm_fvar (fv), _0_31) when ((_0_31 = (Prims.parse_int "2")) && (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.c_or_lid)) -> begin
FStar_Pervasives_Native.Some (BaseConn (((FStar_Parser_Const.or_lid), (args))))
end
| (FStar_Syntax_Syntax.Tm_fvar (fv), _0_32) when ((_0_32 = (Prims.parse_int "2")) && (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.c_eq2_lid)) -> begin
FStar_Pervasives_Native.Some (BaseConn (((FStar_Parser_Const.eq2_lid), (args))))
end
| (FStar_Syntax_Syntax.Tm_fvar (fv), _0_33) when ((_0_33 = (Prims.parse_int "3")) && (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.c_eq2_lid)) -> begin
FStar_Pervasives_Native.Some (BaseConn (((FStar_Parser_Const.eq2_lid), (args))))
end
| (FStar_Syntax_Syntax.Tm_fvar (fv), _0_34) when ((_0_34 = (Prims.parse_int "2")) && (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.c_eq3_lid)) -> begin
FStar_Pervasives_Native.Some (BaseConn (((FStar_Parser_Const.eq3_lid), (args))))
end
| (FStar_Syntax_Syntax.Tm_fvar (fv), _0_35) when ((_0_35 = (Prims.parse_int "4")) && (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.c_eq3_lid)) -> begin
FStar_Pervasives_Native.Some (BaseConn (((FStar_Parser_Const.eq3_lid), (args))))
end
| (FStar_Syntax_Syntax.Tm_fvar (fv), _0_36) when ((_0_36 = (Prims.parse_int "0")) && (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.c_true_lid)) -> begin
FStar_Pervasives_Native.Some (BaseConn (((FStar_Parser_Const.true_lid), (args))))
end
| (FStar_Syntax_Syntax.Tm_fvar (fv), _0_37) when ((_0_37 = (Prims.parse_int "0")) && (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.c_false_lid)) -> begin
FStar_Pervasives_Native.Some (BaseConn (((FStar_Parser_Const.false_lid), (args))))
end
| uu____7269 -> begin
FStar_Pervasives_Native.None
end))
end))))))
in (

let rec destruct_sq_forall = (fun t -> (

let uu____7292 = (un_squash t)
in (FStar_Util.bind_opt uu____7292 (fun t1 -> (

let uu____7307 = (arrow_one t1)
in (match (uu____7307) with
| FStar_Pervasives_Native.Some (b, c) -> begin
(

let uu____7322 = (

let uu____7323 = (is_tot_or_gtot_comp c)
in (not (uu____7323)))
in (match (uu____7322) with
| true -> begin
FStar_Pervasives_Native.None
end
| uu____7326 -> begin
(

let q = (

let uu____7330 = (comp_to_comp_typ c)
in uu____7330.FStar_Syntax_Syntax.result_typ)
in (

let uu____7331 = (FStar_Syntax_Subst.open_term ((b)::[]) q)
in (match (uu____7331) with
| (bs, q1) -> begin
(

let b1 = (match (bs) with
| (b1)::[] -> begin
b1
end
| uu____7362 -> begin
(failwith "impossible")
end)
in (

let uu____7367 = (is_free_in (FStar_Pervasives_Native.fst b1) q1)
in (match (uu____7367) with
| true -> begin
(

let uu____7370 = (patterns q1)
in (match (uu____7370) with
| (pats, q2) -> begin
(FStar_All.pipe_left maybe_collect (FStar_Pervasives_Native.Some (QAll ((((b1)::[]), (pats), (q2))))))
end))
end
| uu____7437 -> begin
(

let uu____7438 = (

let uu____7439 = (

let uu____7444 = (

let uu____7447 = (FStar_Syntax_Syntax.as_arg (FStar_Pervasives_Native.fst b1).FStar_Syntax_Syntax.sort)
in (

let uu____7448 = (

let uu____7451 = (FStar_Syntax_Syntax.as_arg q1)
in (uu____7451)::[])
in (uu____7447)::uu____7448))
in ((FStar_Parser_Const.imp_lid), (uu____7444)))
in BaseConn (uu____7439))
in FStar_Pervasives_Native.Some (uu____7438))
end)))
end)))
end))
end
| uu____7454 -> begin
FStar_Pervasives_Native.None
end))))))
and destruct_sq_exists = (fun t -> (

let uu____7462 = (un_squash t)
in (FStar_Util.bind_opt uu____7462 (fun t1 -> (

let uu____7493 = (head_and_args' t1)
in (match (uu____7493) with
| (hd1, args) -> begin
(

let uu____7526 = (

let uu____7539 = (

let uu____7540 = (un_uinst hd1)
in uu____7540.FStar_Syntax_Syntax.n)
in ((uu____7539), (args)))
in (match (uu____7526) with
| (FStar_Syntax_Syntax.Tm_fvar (fv), ((a1, uu____7555))::((a2, uu____7557))::[]) when (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.dtuple2_lid) -> begin
(

let uu____7592 = (

let uu____7593 = (FStar_Syntax_Subst.compress a2)
in uu____7593.FStar_Syntax_Syntax.n)
in (match (uu____7592) with
| FStar_Syntax_Syntax.Tm_abs ((b)::[], q, uu____7600) -> begin
(

let uu____7627 = (FStar_Syntax_Subst.open_term ((b)::[]) q)
in (match (uu____7627) with
| (bs, q1) -> begin
(

let b1 = (match (bs) with
| (b1)::[] -> begin
b1
end
| uu____7666 -> begin
(failwith "impossible")
end)
in (

let uu____7671 = (patterns q1)
in (match (uu____7671) with
| (pats, q2) -> begin
(FStar_All.pipe_left maybe_collect (FStar_Pervasives_Native.Some (QEx ((((b1)::[]), (pats), (q2))))))
end)))
end))
end
| uu____7738 -> begin
FStar_Pervasives_Native.None
end))
end
| uu____7739 -> begin
FStar_Pervasives_Native.None
end))
end))))))
and maybe_collect = (fun f1 -> (match (f1) with
| FStar_Pervasives_Native.Some (QAll (bs, pats, phi)) -> begin
(

let uu____7760 = (destruct_sq_forall phi)
in (match (uu____7760) with
| FStar_Pervasives_Native.Some (QAll (bs', pats', psi)) -> begin
(FStar_All.pipe_left (fun _0_38 -> FStar_Pervasives_Native.Some (_0_38)) (QAll ((((FStar_List.append bs bs')), ((FStar_List.append pats pats')), (psi)))))
end
| uu____7782 -> begin
f1
end))
end
| FStar_Pervasives_Native.Some (QEx (bs, pats, phi)) -> begin
(

let uu____7788 = (destruct_sq_exists phi)
in (match (uu____7788) with
| FStar_Pervasives_Native.Some (QEx (bs', pats', psi)) -> begin
(FStar_All.pipe_left (fun _0_39 -> FStar_Pervasives_Native.Some (_0_39)) (QEx ((((FStar_List.append bs bs')), ((FStar_List.append pats pats')), (psi)))))
end
| uu____7810 -> begin
f1
end))
end
| uu____7813 -> begin
f1
end))
in (

let phi = (unmeta_monadic f)
in (

let uu____7817 = (destruct_base_conn phi)
in (FStar_Util.catch_opt uu____7817 (fun uu____7822 -> (

let uu____7823 = (destruct_q_conn phi)
in (FStar_Util.catch_opt uu____7823 (fun uu____7828 -> (

let uu____7829 = (destruct_sq_base_conn phi)
in (FStar_Util.catch_opt uu____7829 (fun uu____7834 -> (

let uu____7835 = (destruct_sq_forall phi)
in (FStar_Util.catch_opt uu____7835 (fun uu____7840 -> (

let uu____7841 = (destruct_sq_exists phi)
in (FStar_Util.catch_opt uu____7841 (fun uu____7845 -> FStar_Pervasives_Native.None))))))))))))))))))))))))


let action_as_lb : FStar_Ident.lident  ->  FStar_Syntax_Syntax.action  ->  FStar_Syntax_Syntax.sigelt = (fun eff_lid a -> (

let lb = (

let uu____7855 = (

let uu____7860 = (FStar_Syntax_Syntax.lid_as_fv a.FStar_Syntax_Syntax.action_name FStar_Syntax_Syntax.Delta_equational FStar_Pervasives_Native.None)
in FStar_Util.Inr (uu____7860))
in (

let uu____7861 = (

let uu____7862 = (FStar_Syntax_Syntax.mk_Total a.FStar_Syntax_Syntax.action_typ)
in (arrow a.FStar_Syntax_Syntax.action_params uu____7862))
in (

let uu____7865 = (abs a.FStar_Syntax_Syntax.action_params a.FStar_Syntax_Syntax.action_defn FStar_Pervasives_Native.None)
in (close_univs_and_mk_letbinding FStar_Pervasives_Native.None uu____7855 a.FStar_Syntax_Syntax.action_univs uu____7861 FStar_Parser_Const.effect_Tot_lid uu____7865))))
in {FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_let (((((false), ((lb)::[]))), ((a.FStar_Syntax_Syntax.action_name)::[]))); FStar_Syntax_Syntax.sigrng = a.FStar_Syntax_Syntax.action_defn.FStar_Syntax_Syntax.pos; FStar_Syntax_Syntax.sigquals = (FStar_Syntax_Syntax.Visible_default)::(FStar_Syntax_Syntax.Action (eff_lid))::[]; FStar_Syntax_Syntax.sigmeta = FStar_Syntax_Syntax.default_sigmeta; FStar_Syntax_Syntax.sigattrs = []}))


let mk_reify : FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax  ->  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax = (fun t -> (

let reify_ = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_reify)) FStar_Pervasives_Native.None t.FStar_Syntax_Syntax.pos)
in (

let uu____7891 = (

let uu____7894 = (

let uu____7895 = (

let uu____7910 = (

let uu____7913 = (FStar_Syntax_Syntax.as_arg t)
in (uu____7913)::[])
in ((reify_), (uu____7910)))
in FStar_Syntax_Syntax.Tm_app (uu____7895))
in (FStar_Syntax_Syntax.mk uu____7894))
in (uu____7891 FStar_Pervasives_Native.None t.FStar_Syntax_Syntax.pos))))


let rec delta_qualifier : FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.delta_depth = (fun t -> (

let t1 = (FStar_Syntax_Subst.compress t)
in (match (t1.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_delayed (uu____7926) -> begin
(failwith "Impossible")
end
| FStar_Syntax_Syntax.Tm_fvar (fv) -> begin
fv.FStar_Syntax_Syntax.fv_delta
end
| FStar_Syntax_Syntax.Tm_bvar (uu____7952) -> begin
FStar_Syntax_Syntax.Delta_equational
end
| FStar_Syntax_Syntax.Tm_name (uu____7953) -> begin
FStar_Syntax_Syntax.Delta_equational
end
| FStar_Syntax_Syntax.Tm_match (uu____7954) -> begin
FStar_Syntax_Syntax.Delta_equational
end
| FStar_Syntax_Syntax.Tm_uvar (uu____7977) -> begin
FStar_Syntax_Syntax.Delta_equational
end
| FStar_Syntax_Syntax.Tm_unknown -> begin
FStar_Syntax_Syntax.Delta_equational
end
| FStar_Syntax_Syntax.Tm_type (uu____7994) -> begin
FStar_Syntax_Syntax.Delta_constant
end
| FStar_Syntax_Syntax.Tm_constant (uu____7995) -> begin
FStar_Syntax_Syntax.Delta_constant
end
| FStar_Syntax_Syntax.Tm_arrow (uu____7996) -> begin
FStar_Syntax_Syntax.Delta_constant
end
| FStar_Syntax_Syntax.Tm_uinst (t2, uu____8010) -> begin
(delta_qualifier t2)
end
| FStar_Syntax_Syntax.Tm_refine ({FStar_Syntax_Syntax.ppname = uu____8015; FStar_Syntax_Syntax.index = uu____8016; FStar_Syntax_Syntax.sort = t2}, uu____8018) -> begin
(delta_qualifier t2)
end
| FStar_Syntax_Syntax.Tm_meta (t2, uu____8026) -> begin
(delta_qualifier t2)
end
| FStar_Syntax_Syntax.Tm_ascribed (t2, uu____8032, uu____8033) -> begin
(delta_qualifier t2)
end
| FStar_Syntax_Syntax.Tm_app (t2, uu____8075) -> begin
(delta_qualifier t2)
end
| FStar_Syntax_Syntax.Tm_abs (uu____8096, t2, uu____8098) -> begin
(delta_qualifier t2)
end
| FStar_Syntax_Syntax.Tm_let (uu____8119, t2) -> begin
(delta_qualifier t2)
end)))


let rec incr_delta_depth : FStar_Syntax_Syntax.delta_depth  ->  FStar_Syntax_Syntax.delta_depth = (fun d -> (match (d) with
| FStar_Syntax_Syntax.Delta_equational -> begin
d
end
| FStar_Syntax_Syntax.Delta_constant -> begin
FStar_Syntax_Syntax.Delta_defined_at_level ((Prims.parse_int "1"))
end
| FStar_Syntax_Syntax.Delta_defined_at_level (i) -> begin
FStar_Syntax_Syntax.Delta_defined_at_level ((i + (Prims.parse_int "1")))
end
| FStar_Syntax_Syntax.Delta_abstract (d1) -> begin
(incr_delta_depth d1)
end))


let incr_delta_qualifier : FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.delta_depth = (fun t -> (

let uu____8147 = (delta_qualifier t)
in (incr_delta_depth uu____8147)))


let is_unknown : FStar_Syntax_Syntax.term  ->  Prims.bool = (fun t -> (

let uu____8152 = (

let uu____8153 = (FStar_Syntax_Subst.compress t)
in uu____8153.FStar_Syntax_Syntax.n)
in (match (uu____8152) with
| FStar_Syntax_Syntax.Tm_unknown -> begin
true
end
| uu____8156 -> begin
false
end)))


let rec list_elements : FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term Prims.list FStar_Pervasives_Native.option = (fun e -> (

let uu____8169 = (

let uu____8184 = (unmeta e)
in (head_and_args uu____8184))
in (match (uu____8169) with
| (head1, args) -> begin
(

let uu____8211 = (

let uu____8224 = (

let uu____8225 = (un_uinst head1)
in uu____8225.FStar_Syntax_Syntax.n)
in ((uu____8224), (args)))
in (match (uu____8211) with
| (FStar_Syntax_Syntax.Tm_fvar (fv), uu____8241) when (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.nil_lid) -> begin
FStar_Pervasives_Native.Some ([])
end
| (FStar_Syntax_Syntax.Tm_fvar (fv), (uu____8261)::((hd1, uu____8263))::((tl1, uu____8265))::[]) when (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.cons_lid) -> begin
(

let uu____8312 = (

let uu____8317 = (

let uu____8322 = (list_elements tl1)
in (FStar_Util.must uu____8322))
in (hd1)::uu____8317)
in FStar_Pervasives_Native.Some (uu____8312))
end
| uu____8335 -> begin
FStar_Pervasives_Native.None
end))
end)))


let rec apply_last : 'Auu____8356 . ('Auu____8356  ->  'Auu____8356)  ->  'Auu____8356 Prims.list  ->  'Auu____8356 Prims.list = (fun f l -> (match (l) with
| [] -> begin
(failwith "apply_last: got empty list")
end
| (a)::[] -> begin
(

let uu____8379 = (f a)
in (uu____8379)::[])
end
| (x)::xs -> begin
(

let uu____8384 = (apply_last f xs)
in (x)::uu____8384)
end))


let dm4f_lid : FStar_Syntax_Syntax.eff_decl  ->  Prims.string  ->  FStar_Ident.lident = (fun ed name -> (

let p = (FStar_Ident.path_of_lid ed.FStar_Syntax_Syntax.mname)
in (

let p' = (apply_last (fun s -> (Prims.strcat "_dm4f_" (Prims.strcat s (Prims.strcat "_" name)))) p)
in (FStar_Ident.lid_of_path p' FStar_Range.dummyRange))))


let rec mk_list : FStar_Syntax_Syntax.term  ->  FStar_Range.range  ->  FStar_Syntax_Syntax.term Prims.list  ->  FStar_Syntax_Syntax.term = (fun typ rng l -> (

let ctor = (fun l1 -> (

let uu____8425 = (

let uu____8428 = (

let uu____8429 = (FStar_Syntax_Syntax.lid_as_fv l1 FStar_Syntax_Syntax.Delta_constant (FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Data_ctor)))
in FStar_Syntax_Syntax.Tm_fvar (uu____8429))
in (FStar_Syntax_Syntax.mk uu____8428))
in (uu____8425 FStar_Pervasives_Native.None rng)))
in (

let cons1 = (fun args pos -> (

let uu____8442 = (

let uu____8443 = (

let uu____8444 = (ctor FStar_Parser_Const.cons_lid)
in (FStar_Syntax_Syntax.mk_Tm_uinst uu____8444 ((FStar_Syntax_Syntax.U_zero)::[])))
in (FStar_Syntax_Syntax.mk_Tm_app uu____8443 args))
in (uu____8442 FStar_Pervasives_Native.None pos)))
in (

let nil = (fun args pos -> (

let uu____8456 = (

let uu____8457 = (

let uu____8458 = (ctor FStar_Parser_Const.nil_lid)
in (FStar_Syntax_Syntax.mk_Tm_uinst uu____8458 ((FStar_Syntax_Syntax.U_zero)::[])))
in (FStar_Syntax_Syntax.mk_Tm_app uu____8457 args))
in (uu____8456 FStar_Pervasives_Native.None pos)))
in (

let uu____8461 = (

let uu____8462 = (

let uu____8463 = (FStar_Syntax_Syntax.iarg typ)
in (uu____8463)::[])
in (nil uu____8462 rng))
in (FStar_List.fold_right (fun t a -> (

let uu____8469 = (

let uu____8470 = (FStar_Syntax_Syntax.iarg typ)
in (

let uu____8471 = (

let uu____8474 = (FStar_Syntax_Syntax.as_arg t)
in (

let uu____8475 = (

let uu____8478 = (FStar_Syntax_Syntax.as_arg a)
in (uu____8478)::[])
in (uu____8474)::uu____8475))
in (uu____8470)::uu____8471))
in (cons1 uu____8469 t.FStar_Syntax_Syntax.pos))) l uu____8461))))))


let uvar_from_id : Prims.int  ->  FStar_Syntax_Syntax.typ  ->  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax = (fun id t -> (

let uu____8489 = (

let uu____8492 = (

let uu____8493 = (

let uu____8510 = (FStar_Syntax_Unionfind.from_id id)
in ((uu____8510), (t)))
in FStar_Syntax_Syntax.Tm_uvar (uu____8493))
in (FStar_Syntax_Syntax.mk uu____8492))
in (uu____8489 FStar_Pervasives_Native.None FStar_Range.dummyRange)))


let rec eqlist : 'a . ('a  ->  'a  ->  Prims.bool)  ->  'a Prims.list  ->  'a Prims.list  ->  Prims.bool = (fun eq1 xs ys -> (match (((xs), (ys))) with
| ([], []) -> begin
true
end
| ((x)::xs1, (y)::ys1) -> begin
((eq1 x y) && (eqlist eq1 xs1 ys1))
end
| uu____8573 -> begin
false
end))


let eqsum : 'a 'b . ('a  ->  'a  ->  Prims.bool)  ->  ('b  ->  'b  ->  Prims.bool)  ->  ('a, 'b) FStar_Util.either  ->  ('a, 'b) FStar_Util.either  ->  Prims.bool = (fun e1 e2 x y -> (match (((x), (y))) with
| (FStar_Util.Inl (x1), FStar_Util.Inl (y1)) -> begin
(e1 x1 y1)
end
| (FStar_Util.Inr (x1), FStar_Util.Inr (y1)) -> begin
(e2 x1 y1)
end
| uu____8676 -> begin
false
end))


let eqprod : 'a 'b . ('a  ->  'a  ->  Prims.bool)  ->  ('b  ->  'b  ->  Prims.bool)  ->  ('a * 'b)  ->  ('a * 'b)  ->  Prims.bool = (fun e1 e2 x y -> (match (((x), (y))) with
| ((x1, x2), (y1, y2)) -> begin
((e1 x1 y1) && (e2 x2 y2))
end))


let eqopt : 'a . ('a  ->  'a  ->  Prims.bool)  ->  'a FStar_Pervasives_Native.option  ->  'a FStar_Pervasives_Native.option  ->  Prims.bool = (fun e x y -> (match (((x), (y))) with
| (FStar_Pervasives_Native.Some (x1), FStar_Pervasives_Native.Some (y1)) -> begin
(e x1 y1)
end
| uu____8824 -> begin
false
end))


let rec term_eq : FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term  ->  Prims.bool = (fun t1 t2 -> (

let canon_app = (fun t -> (match (t.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_app (uu____8935) -> begin
(

let uu____8950 = (head_and_args' t)
in (match (uu____8950) with
| (hd1, args) -> begin
(

let uu___175_8983 = t
in {FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_app (((hd1), (args))); FStar_Syntax_Syntax.pos = uu___175_8983.FStar_Syntax_Syntax.pos; FStar_Syntax_Syntax.vars = uu___175_8983.FStar_Syntax_Syntax.vars})
end))
end
| uu____8994 -> begin
t
end))
in (

let t11 = (

let uu____8998 = (unmeta_safe t1)
in (canon_app uu____8998))
in (

let t21 = (

let uu____9004 = (unmeta_safe t2)
in (canon_app uu____9004))
in (match (((t11.FStar_Syntax_Syntax.n), (t21.FStar_Syntax_Syntax.n))) with
| (FStar_Syntax_Syntax.Tm_bvar (x), FStar_Syntax_Syntax.Tm_bvar (y)) -> begin
(Prims.op_Equality x.FStar_Syntax_Syntax.index y.FStar_Syntax_Syntax.index)
end
| (FStar_Syntax_Syntax.Tm_name (x), FStar_Syntax_Syntax.Tm_name (y)) -> begin
(FStar_Syntax_Syntax.bv_eq x y)
end
| (FStar_Syntax_Syntax.Tm_fvar (x), FStar_Syntax_Syntax.Tm_fvar (y)) -> begin
(FStar_Syntax_Syntax.fv_eq x y)
end
| (FStar_Syntax_Syntax.Tm_uinst (t12, us1), FStar_Syntax_Syntax.Tm_uinst (t22, us2)) -> begin
((eqlist eq_univs us1 us2) && (term_eq t12 t22))
end
| (FStar_Syntax_Syntax.Tm_constant (c1), FStar_Syntax_Syntax.Tm_constant (c2)) -> begin
(FStar_Const.eq_const c1 c2)
end
| (FStar_Syntax_Syntax.Tm_type (x), FStar_Syntax_Syntax.Tm_type (y)) -> begin
(Prims.op_Equality x y)
end
| (FStar_Syntax_Syntax.Tm_abs (b1, t12, k1), FStar_Syntax_Syntax.Tm_abs (b2, t22, k2)) -> begin
((eqlist binder_eq b1 b2) && (term_eq t12 t22))
end
| (FStar_Syntax_Syntax.Tm_app (f1, a1), FStar_Syntax_Syntax.Tm_app (f2, a2)) -> begin
((term_eq f1 f2) && (eqlist arg_eq a1 a2))
end
| (FStar_Syntax_Syntax.Tm_arrow (b1, c1), FStar_Syntax_Syntax.Tm_arrow (b2, c2)) -> begin
((eqlist binder_eq b1 b2) && (comp_eq c1 c2))
end
| (FStar_Syntax_Syntax.Tm_refine (b1, t12), FStar_Syntax_Syntax.Tm_refine (b2, t22)) -> begin
((FStar_Syntax_Syntax.bv_eq b1 b2) && (term_eq t12 t22))
end
| (FStar_Syntax_Syntax.Tm_match (t12, bs1), FStar_Syntax_Syntax.Tm_match (t22, bs2)) -> begin
((term_eq t12 t22) && (eqlist branch_eq bs1 bs2))
end
| (uu____9271, uu____9272) -> begin
false
end)))))
and arg_eq : (FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax * FStar_Syntax_Syntax.aqual)  ->  (FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax * FStar_Syntax_Syntax.aqual)  ->  Prims.bool = (fun a1 a2 -> (eqprod term_eq (fun q1 q2 -> (Prims.op_Equality q1 q2)) a1 a2))
and binder_eq : (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.aqual)  ->  (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.aqual)  ->  Prims.bool = (fun b1 b2 -> (eqprod (fun b11 b21 -> (term_eq b11.FStar_Syntax_Syntax.sort b21.FStar_Syntax_Syntax.sort)) (fun q1 q2 -> (Prims.op_Equality q1 q2)) b1 b2))
and lcomp_eq : FStar_Syntax_Syntax.lcomp  ->  FStar_Syntax_Syntax.lcomp  ->  Prims.bool = (fun c1 c2 -> false)
and residual_eq : FStar_Syntax_Syntax.residual_comp  ->  FStar_Syntax_Syntax.residual_comp  ->  Prims.bool = (fun r1 r2 -> false)
and comp_eq : FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax  ->  FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax  ->  Prims.bool = (fun c1 c2 -> (match (((c1.FStar_Syntax_Syntax.n), (c2.FStar_Syntax_Syntax.n))) with
| (FStar_Syntax_Syntax.Total (t1, u1), FStar_Syntax_Syntax.Total (t2, u2)) -> begin
(term_eq t1 t2)
end
| (FStar_Syntax_Syntax.GTotal (t1, u1), FStar_Syntax_Syntax.GTotal (t2, u2)) -> begin
(term_eq t1 t2)
end
| (FStar_Syntax_Syntax.Comp (c11), FStar_Syntax_Syntax.Comp (c21)) -> begin
(((((Prims.op_Equality c11.FStar_Syntax_Syntax.comp_univs c21.FStar_Syntax_Syntax.comp_univs) && (Prims.op_Equality c11.FStar_Syntax_Syntax.effect_name c21.FStar_Syntax_Syntax.effect_name)) && (term_eq c11.FStar_Syntax_Syntax.result_typ c21.FStar_Syntax_Syntax.result_typ)) && (eqlist arg_eq c11.FStar_Syntax_Syntax.effect_args c21.FStar_Syntax_Syntax.effect_args)) && (eq_flags c11.FStar_Syntax_Syntax.flags c21.FStar_Syntax_Syntax.flags))
end
| (uu____9367, uu____9368) -> begin
false
end))
and eq_flags : FStar_Syntax_Syntax.cflags Prims.list  ->  FStar_Syntax_Syntax.cflags Prims.list  ->  Prims.bool = (fun f1 f2 -> false)
and branch_eq : (FStar_Syntax_Syntax.pat' FStar_Syntax_Syntax.withinfo_t * FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax FStar_Pervasives_Native.option * FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax)  ->  (FStar_Syntax_Syntax.pat' FStar_Syntax_Syntax.withinfo_t * FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax FStar_Pervasives_Native.option * FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax)  ->  Prims.bool = (fun uu____9375 uu____9376 -> (match (((uu____9375), (uu____9376))) with
| ((p1, w1, t1), (p2, w2, t2)) -> begin
false
end))


let rec bottom_fold : (FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term)  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term = (fun f t -> (

let ff = (bottom_fold f)
in (

let tn = (

let uu____9516 = (FStar_Syntax_Subst.compress t)
in uu____9516.FStar_Syntax_Syntax.n)
in (

let tn1 = (match (tn) with
| FStar_Syntax_Syntax.Tm_app (f1, args) -> begin
(

let uu____9542 = (

let uu____9557 = (ff f1)
in (

let uu____9558 = (FStar_List.map (fun uu____9577 -> (match (uu____9577) with
| (a, q) -> begin
(

let uu____9588 = (ff a)
in ((uu____9588), (q)))
end)) args)
in ((uu____9557), (uu____9558))))
in FStar_Syntax_Syntax.Tm_app (uu____9542))
end
| FStar_Syntax_Syntax.Tm_abs (bs, t1, k) -> begin
(

let uu____9618 = (FStar_Syntax_Subst.open_term bs t1)
in (match (uu____9618) with
| (bs1, t') -> begin
(

let t'' = (ff t')
in (

let uu____9626 = (

let uu____9643 = (FStar_Syntax_Subst.close bs1 t'')
in ((bs1), (uu____9643), (k)))
in FStar_Syntax_Syntax.Tm_abs (uu____9626)))
end))
end
| FStar_Syntax_Syntax.Tm_arrow (bs, k) -> begin
tn
end
| FStar_Syntax_Syntax.Tm_uinst (t1, us) -> begin
(

let uu____9670 = (

let uu____9677 = (ff t1)
in ((uu____9677), (us)))
in FStar_Syntax_Syntax.Tm_uinst (uu____9670))
end
| uu____9678 -> begin
tn
end)
in (f (

let uu___176_9681 = t
in {FStar_Syntax_Syntax.n = tn1; FStar_Syntax_Syntax.pos = uu___176_9681.FStar_Syntax_Syntax.pos; FStar_Syntax_Syntax.vars = uu___176_9681.FStar_Syntax_Syntax.vars}))))))


let rec sizeof : FStar_Syntax_Syntax.term  ->  Prims.int = (fun t -> (match (t.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_delayed (uu____9686) -> begin
(

let uu____9711 = (

let uu____9712 = (FStar_Syntax_Subst.compress t)
in (sizeof uu____9712))
in ((Prims.parse_int "1") + uu____9711))
end
| FStar_Syntax_Syntax.Tm_bvar (bv) -> begin
(

let uu____9714 = (sizeof bv.FStar_Syntax_Syntax.sort)
in ((Prims.parse_int "1") + uu____9714))
end
| FStar_Syntax_Syntax.Tm_name (bv) -> begin
(

let uu____9716 = (sizeof bv.FStar_Syntax_Syntax.sort)
in ((Prims.parse_int "1") + uu____9716))
end
| FStar_Syntax_Syntax.Tm_uinst (t1, us) -> begin
(

let uu____9723 = (sizeof t1)
in ((FStar_List.length us) + uu____9723))
end
| FStar_Syntax_Syntax.Tm_abs (bs, t1, uu____9726) -> begin
(

let uu____9747 = (sizeof t1)
in (

let uu____9748 = (FStar_List.fold_left (fun acc uu____9759 -> (match (uu____9759) with
| (bv, uu____9765) -> begin
(

let uu____9766 = (sizeof bv.FStar_Syntax_Syntax.sort)
in (acc + uu____9766))
end)) (Prims.parse_int "0") bs)
in (uu____9747 + uu____9748)))
end
| FStar_Syntax_Syntax.Tm_app (hd1, args) -> begin
(

let uu____9789 = (sizeof hd1)
in (

let uu____9790 = (FStar_List.fold_left (fun acc uu____9801 -> (match (uu____9801) with
| (arg, uu____9807) -> begin
(

let uu____9808 = (sizeof arg)
in (acc + uu____9808))
end)) (Prims.parse_int "0") args)
in (uu____9789 + uu____9790)))
end
| uu____9809 -> begin
(Prims.parse_int "1")
end))


let is_synth_by_tactic : FStar_Syntax_Syntax.term  ->  Prims.bool = (fun t -> (

let uu____9814 = (

let uu____9815 = (un_uinst t)
in uu____9815.FStar_Syntax_Syntax.n)
in (match (uu____9814) with
| FStar_Syntax_Syntax.Tm_fvar (fv) -> begin
(FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.synth_lid)
end
| uu____9819 -> begin
false
end)))


let mk_alien : 'a . 'a  ->  Prims.string  ->  FStar_Range.range FStar_Pervasives_Native.option  ->  FStar_Syntax_Syntax.term = (fun b s r -> (

let uu____9845 = (

let uu____9848 = (

let uu____9849 = (

let uu____9856 = (

let uu____9857 = (

let uu____9862 = (FStar_Dyn.mkdyn b)
in ((uu____9862), (s)))
in FStar_Syntax_Syntax.Meta_alien (uu____9857))
in ((FStar_Syntax_Syntax.tun), (uu____9856)))
in FStar_Syntax_Syntax.Tm_meta (uu____9849))
in (FStar_Syntax_Syntax.mk uu____9848))
in (uu____9845 FStar_Pervasives_Native.None (match (r) with
| FStar_Pervasives_Native.Some (r1) -> begin
r1
end
| FStar_Pervasives_Native.None -> begin
FStar_Range.dummyRange
end))))


let un_alien : FStar_Syntax_Syntax.term  ->  FStar_Dyn.dyn = (fun t -> (match (t.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_meta (uu____9874, FStar_Syntax_Syntax.Meta_alien (blob, uu____9876)) -> begin
blob
end
| uu____9881 -> begin
(failwith "unexpected: term was not an alien embedding")
end))




