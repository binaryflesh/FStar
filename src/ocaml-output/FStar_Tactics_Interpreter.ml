
open Prims
open FStar_Pervasives

let tacdbg : Prims.bool FStar_ST.ref = (FStar_Util.mk_ref false)


let mk_tactic_interpretation_0 : 'a . FStar_Tactics_Types.proofstate  ->  'a FStar_Tactics_Basic.tac  ->  ('a  ->  FStar_Syntax_Syntax.term)  ->  FStar_Syntax_Syntax.typ  ->  FStar_Ident.lid  ->  FStar_Syntax_Syntax.args  ->  FStar_Syntax_Syntax.term FStar_Pervasives_Native.option = (fun ps t embed_a t_a nm args -> (match (args) with
| ((embedded_state, uu____61))::[] -> begin
((FStar_Tactics_Basic.log ps (fun uu____82 -> (

let uu____83 = (FStar_Ident.string_of_lid nm)
in (

let uu____84 = (FStar_Syntax_Print.args_to_string args)
in (FStar_Util.print2 "Reached %s, args are: %s\n" uu____83 uu____84)))));
(

let ps1 = (FStar_Tactics_Embedding.unembed_proofstate ps embedded_state)
in (

let res = (FStar_Tactics_Basic.run t ps1)
in (

let uu____89 = (FStar_Tactics_Embedding.embed_result ps1 res embed_a t_a)
in FStar_Pervasives_Native.Some (uu____89))));
)
end
| uu____90 -> begin
(failwith "Unexpected application of tactic primitive")
end))


let mk_tactic_interpretation_1 : 'a 'b . FStar_Tactics_Types.proofstate  ->  ('b  ->  'a FStar_Tactics_Basic.tac)  ->  (FStar_Syntax_Syntax.term  ->  'b)  ->  ('a  ->  FStar_Syntax_Syntax.term)  ->  FStar_Syntax_Syntax.typ  ->  FStar_Ident.lid  ->  FStar_Syntax_Syntax.args  ->  FStar_Syntax_Syntax.term FStar_Pervasives_Native.option = (fun ps t unembed_b embed_a t_a nm args -> (match (args) with
| ((b, uu____163))::((embedded_state, uu____165))::[] -> begin
((FStar_Tactics_Basic.log ps (fun uu____196 -> (

let uu____197 = (FStar_Ident.string_of_lid nm)
in (

let uu____198 = (FStar_Syntax_Print.term_to_string embedded_state)
in (FStar_Util.print2 "Reached %s, goals are: %s\n" uu____197 uu____198)))));
(

let ps1 = (FStar_Tactics_Embedding.unembed_proofstate ps embedded_state)
in (

let res = (

let uu____203 = (

let uu____206 = (unembed_b b)
in (t uu____206))
in (FStar_Tactics_Basic.run uu____203 ps1))
in (

let uu____207 = (FStar_Tactics_Embedding.embed_result ps1 res embed_a t_a)
in FStar_Pervasives_Native.Some (uu____207))));
)
end
| uu____208 -> begin
(

let uu____209 = (

let uu____210 = (FStar_Ident.string_of_lid nm)
in (

let uu____211 = (FStar_Syntax_Print.args_to_string args)
in (FStar_Util.format2 "Unexpected application of tactic primitive %s %s" uu____210 uu____211)))
in (failwith uu____209))
end))


let mk_tactic_interpretation_2 : 'a 'b 'c . FStar_Tactics_Types.proofstate  ->  ('a  ->  'b  ->  'c FStar_Tactics_Basic.tac)  ->  (FStar_Syntax_Syntax.term  ->  'a)  ->  (FStar_Syntax_Syntax.term  ->  'b)  ->  ('c  ->  FStar_Syntax_Syntax.term)  ->  FStar_Syntax_Syntax.typ  ->  FStar_Ident.lid  ->  FStar_Syntax_Syntax.args  ->  FStar_Syntax_Syntax.term FStar_Pervasives_Native.option = (fun ps t unembed_a unembed_b embed_c t_c nm args -> (match (args) with
| ((a, uu____303))::((b, uu____305))::((embedded_state, uu____307))::[] -> begin
((FStar_Tactics_Basic.log ps (fun uu____348 -> (

let uu____349 = (FStar_Ident.string_of_lid nm)
in (

let uu____350 = (FStar_Syntax_Print.term_to_string embedded_state)
in (FStar_Util.print2 "Reached %s, goals are: %s\n" uu____349 uu____350)))));
(

let ps1 = (FStar_Tactics_Embedding.unembed_proofstate ps embedded_state)
in (

let res = (

let uu____355 = (

let uu____358 = (unembed_a a)
in (

let uu____359 = (unembed_b b)
in (t uu____358 uu____359)))
in (FStar_Tactics_Basic.run uu____355 ps1))
in (

let uu____360 = (FStar_Tactics_Embedding.embed_result ps1 res embed_c t_c)
in FStar_Pervasives_Native.Some (uu____360))));
)
end
| uu____361 -> begin
(

let uu____362 = (

let uu____363 = (FStar_Ident.string_of_lid nm)
in (

let uu____364 = (FStar_Syntax_Print.args_to_string args)
in (FStar_Util.format2 "Unexpected application of tactic primitive %s %s" uu____363 uu____364)))
in (failwith uu____362))
end))


let mk_tactic_interpretation_3 : 'a 'b 'c 'd . FStar_Tactics_Types.proofstate  ->  ('a  ->  'b  ->  'c  ->  'd FStar_Tactics_Basic.tac)  ->  (FStar_Syntax_Syntax.term  ->  'a)  ->  (FStar_Syntax_Syntax.term  ->  'b)  ->  (FStar_Syntax_Syntax.term  ->  'c)  ->  ('d  ->  FStar_Syntax_Syntax.term)  ->  FStar_Syntax_Syntax.typ  ->  FStar_Ident.lid  ->  FStar_Syntax_Syntax.args  ->  FStar_Syntax_Syntax.term FStar_Pervasives_Native.option = (fun ps t unembed_a unembed_b unembed_c embed_d t_d nm args -> (match (args) with
| ((a, uu____475))::((b, uu____477))::((c, uu____479))::((embedded_state, uu____481))::[] -> begin
((FStar_Tactics_Basic.log ps (fun uu____532 -> (

let uu____533 = (FStar_Ident.string_of_lid nm)
in (

let uu____534 = (FStar_Syntax_Print.term_to_string embedded_state)
in (FStar_Util.print2 "Reached %s, goals are: %s\n" uu____533 uu____534)))));
(

let ps1 = (FStar_Tactics_Embedding.unembed_proofstate ps embedded_state)
in (

let res = (

let uu____539 = (

let uu____542 = (unembed_a a)
in (

let uu____543 = (unembed_b b)
in (

let uu____544 = (unembed_c c)
in (t uu____542 uu____543 uu____544))))
in (FStar_Tactics_Basic.run uu____539 ps1))
in (

let uu____545 = (FStar_Tactics_Embedding.embed_result ps1 res embed_d t_d)
in FStar_Pervasives_Native.Some (uu____545))));
)
end
| uu____546 -> begin
(

let uu____547 = (

let uu____548 = (FStar_Ident.string_of_lid nm)
in (

let uu____549 = (FStar_Syntax_Print.args_to_string args)
in (FStar_Util.format2 "Unexpected application of tactic primitive %s %s" uu____548 uu____549)))
in (failwith uu____547))
end))


let mk_tactic_interpretation_5 : 'a 'b 'c 'd 'e 'f . FStar_Tactics_Types.proofstate  ->  ('a  ->  'b  ->  'c  ->  'd  ->  'e  ->  'f FStar_Tactics_Basic.tac)  ->  (FStar_Syntax_Syntax.term  ->  'a)  ->  (FStar_Syntax_Syntax.term  ->  'b)  ->  (FStar_Syntax_Syntax.term  ->  'c)  ->  (FStar_Syntax_Syntax.term  ->  'd)  ->  (FStar_Syntax_Syntax.term  ->  'e)  ->  ('f  ->  FStar_Syntax_Syntax.term)  ->  FStar_Syntax_Syntax.typ  ->  FStar_Ident.lid  ->  FStar_Syntax_Syntax.args  ->  FStar_Syntax_Syntax.term FStar_Pervasives_Native.option = (fun ps t unembed_a unembed_b unembed_c unembed_d unembed_e embed_f t_f nm args -> (match (args) with
| ((a, uu____698))::((b, uu____700))::((c, uu____702))::((d, uu____704))::((e, uu____706))::((embedded_state, uu____708))::[] -> begin
((FStar_Tactics_Basic.log ps (fun uu____779 -> (

let uu____780 = (FStar_Ident.string_of_lid nm)
in (

let uu____781 = (FStar_Syntax_Print.term_to_string embedded_state)
in (FStar_Util.print2 "Reached %s, goals are: %s\n" uu____780 uu____781)))));
(

let ps1 = (FStar_Tactics_Embedding.unembed_proofstate ps embedded_state)
in (

let res = (

let uu____786 = (

let uu____789 = (unembed_a a)
in (

let uu____790 = (unembed_b b)
in (

let uu____791 = (unembed_c c)
in (

let uu____792 = (unembed_d d)
in (

let uu____793 = (unembed_e e)
in (t uu____789 uu____790 uu____791 uu____792 uu____793))))))
in (FStar_Tactics_Basic.run uu____786 ps1))
in (

let uu____794 = (FStar_Tactics_Embedding.embed_result ps1 res embed_f t_f)
in FStar_Pervasives_Native.Some (uu____794))));
)
end
| uu____795 -> begin
(

let uu____796 = (

let uu____797 = (FStar_Ident.string_of_lid nm)
in (

let uu____798 = (FStar_Syntax_Print.args_to_string args)
in (FStar_Util.format2 "Unexpected application of tactic primitive %s %s" uu____797 uu____798)))
in (failwith uu____796))
end))


let step_from_native_step : FStar_Tactics_Types.proofstate  ->  FStar_Tactics_Native.native_primitive_step  ->  FStar_TypeChecker_Normalize.primitive_step = (fun ps s -> {FStar_TypeChecker_Normalize.name = s.FStar_Tactics_Native.name; FStar_TypeChecker_Normalize.arity = s.FStar_Tactics_Native.arity; FStar_TypeChecker_Normalize.strong_reduction_ok = s.FStar_Tactics_Native.strong_reduction_ok; FStar_TypeChecker_Normalize.interpretation = (fun _rng args -> (s.FStar_Tactics_Native.tactic ps args))})


let rec primitive_steps : FStar_Tactics_Types.proofstate  ->  FStar_TypeChecker_Normalize.primitive_step Prims.list = (fun ps -> (

let mk1 = (fun nm arity interpretation -> (

let nm1 = (FStar_Tactics_Embedding.fstar_tactics_lid' (("Builtins")::(nm)::[]))
in {FStar_TypeChecker_Normalize.name = nm1; FStar_TypeChecker_Normalize.arity = arity; FStar_TypeChecker_Normalize.strong_reduction_ok = false; FStar_TypeChecker_Normalize.interpretation = (fun _rng args -> (interpretation nm1 args))}))
in (

let native_tactics = (FStar_Tactics_Native.list_all ())
in (

let native_tactics_steps = (FStar_List.map (step_from_native_step ps) native_tactics)
in (

let mktac0 = (fun name f e_a ta -> (mk1 name (Prims.parse_int "1") (mk_tactic_interpretation_0 ps f e_a ta)))
in (

let mktac1 = (fun name f u_a e_b tb -> (mk1 name (Prims.parse_int "2") (mk_tactic_interpretation_1 ps f u_a e_b tb)))
in (

let mktac2 = (fun name f u_a u_b e_c tc -> (mk1 name (Prims.parse_int "3") (mk_tactic_interpretation_2 ps f u_a u_b e_c tc)))
in (

let mktac3 = (fun name f u_a u_b u_c e_d tc -> (mk1 name (Prims.parse_int "4") (mk_tactic_interpretation_3 ps f u_a u_b u_c e_d tc)))
in (

let mktac5 = (fun name f u_a u_b u_c u_d u_e e_f tc -> (mk1 name (Prims.parse_int "6") (mk_tactic_interpretation_5 ps f u_a u_b u_c u_d u_e e_f tc)))
in (

let uu____1217 = (

let uu____1220 = (mktac0 "__trivial" FStar_Tactics_Basic.trivial FStar_Syntax_Embeddings.embed_unit FStar_Syntax_Syntax.t_unit)
in (

let uu____1221 = (

let uu____1224 = (mktac2 "__trytac" (fun uu____1230 -> FStar_Tactics_Basic.trytac) (fun t -> t) (unembed_tactic_0 (fun t -> t)) (FStar_Syntax_Embeddings.embed_option (fun t -> t) FStar_Syntax_Syntax.t_unit) FStar_Syntax_Syntax.t_unit)
in (

let uu____1237 = (

let uu____1240 = (mktac0 "__intro" FStar_Tactics_Basic.intro FStar_Reflection_Basic.embed_binder FStar_Reflection_Data.fstar_refl_binder)
in (

let uu____1241 = (

let uu____1244 = (

let uu____1245 = (FStar_Tactics_Embedding.pair_typ FStar_Reflection_Data.fstar_refl_binder FStar_Reflection_Data.fstar_refl_binder)
in (mktac0 "__intro_rec" FStar_Tactics_Basic.intro_rec (FStar_Syntax_Embeddings.embed_pair FStar_Reflection_Basic.embed_binder FStar_Reflection_Data.fstar_refl_binder FStar_Reflection_Basic.embed_binder FStar_Reflection_Data.fstar_refl_binder) uu____1245))
in (

let uu____1250 = (

let uu____1253 = (mktac1 "__norm" FStar_Tactics_Basic.norm (FStar_Syntax_Embeddings.unembed_list FStar_Syntax_Embeddings.unembed_norm_step) FStar_Syntax_Embeddings.embed_unit FStar_Syntax_Syntax.t_unit)
in (

let uu____1256 = (

let uu____1259 = (mktac2 "__norm_term" FStar_Tactics_Basic.norm_term (FStar_Syntax_Embeddings.unembed_list FStar_Syntax_Embeddings.unembed_norm_step) FStar_Reflection_Basic.unembed_term FStar_Reflection_Basic.embed_term FStar_Reflection_Data.fstar_refl_term)
in (

let uu____1262 = (

let uu____1265 = (mktac2 "__rename_to" FStar_Tactics_Basic.rename_to FStar_Reflection_Basic.unembed_binder FStar_Syntax_Embeddings.unembed_string FStar_Syntax_Embeddings.embed_unit FStar_Syntax_Syntax.t_unit)
in (

let uu____1266 = (

let uu____1269 = (mktac0 "__revert" FStar_Tactics_Basic.revert FStar_Syntax_Embeddings.embed_unit FStar_Syntax_Syntax.t_unit)
in (

let uu____1270 = (

let uu____1273 = (mktac0 "__clear_top" FStar_Tactics_Basic.clear_top FStar_Syntax_Embeddings.embed_unit FStar_Syntax_Syntax.t_unit)
in (

let uu____1274 = (

let uu____1277 = (mktac1 "__clear" FStar_Tactics_Basic.clear FStar_Reflection_Basic.unembed_binder FStar_Syntax_Embeddings.embed_unit FStar_Syntax_Syntax.t_unit)
in (

let uu____1278 = (

let uu____1281 = (mktac1 "__rewrite" FStar_Tactics_Basic.rewrite FStar_Reflection_Basic.unembed_binder FStar_Syntax_Embeddings.embed_unit FStar_Syntax_Syntax.t_unit)
in (

let uu____1282 = (

let uu____1285 = (mktac0 "__smt" FStar_Tactics_Basic.smt FStar_Syntax_Embeddings.embed_unit FStar_Syntax_Syntax.t_unit)
in (

let uu____1286 = (

let uu____1289 = (mktac1 "__exact" FStar_Tactics_Basic.exact FStar_Reflection_Basic.unembed_term FStar_Syntax_Embeddings.embed_unit FStar_Syntax_Syntax.t_unit)
in (

let uu____1290 = (

let uu____1293 = (mktac1 "__exact_lemma" FStar_Tactics_Basic.exact_lemma FStar_Reflection_Basic.unembed_term FStar_Syntax_Embeddings.embed_unit FStar_Syntax_Syntax.t_unit)
in (

let uu____1294 = (

let uu____1297 = (mktac1 "__apply" (FStar_Tactics_Basic.apply true) FStar_Reflection_Basic.unembed_term FStar_Syntax_Embeddings.embed_unit FStar_Syntax_Syntax.t_unit)
in (

let uu____1298 = (

let uu____1301 = (mktac1 "__apply_raw" (FStar_Tactics_Basic.apply false) FStar_Reflection_Basic.unembed_term FStar_Syntax_Embeddings.embed_unit FStar_Syntax_Syntax.t_unit)
in (

let uu____1302 = (

let uu____1305 = (mktac1 "__apply_lemma" FStar_Tactics_Basic.apply_lemma FStar_Reflection_Basic.unembed_term FStar_Syntax_Embeddings.embed_unit FStar_Syntax_Syntax.t_unit)
in (

let uu____1306 = (

let uu____1309 = (mktac5 "__divide" (fun uu____1320 uu____1321 -> FStar_Tactics_Basic.divide) (fun t -> t) (fun t -> t) FStar_Syntax_Embeddings.unembed_int (unembed_tactic_0 (fun t -> t)) (unembed_tactic_0 (fun t -> t)) (FStar_Syntax_Embeddings.embed_pair (fun t -> t) FStar_Syntax_Syntax.t_unit (fun t -> t) FStar_Syntax_Syntax.t_unit) FStar_Syntax_Syntax.t_unit)
in (

let uu____1334 = (

let uu____1337 = (mktac1 "__set_options" FStar_Tactics_Basic.set_options FStar_Syntax_Embeddings.unembed_string FStar_Syntax_Embeddings.embed_unit FStar_Syntax_Syntax.t_unit)
in (

let uu____1338 = (

let uu____1341 = (mktac2 "__seq" FStar_Tactics_Basic.seq (unembed_tactic_0 FStar_Syntax_Embeddings.unembed_unit) (unembed_tactic_0 FStar_Syntax_Embeddings.unembed_unit) FStar_Syntax_Embeddings.embed_unit FStar_Syntax_Syntax.t_unit)
in (

let uu____1346 = (

let uu____1349 = (mktac2 "__unquote" FStar_Tactics_Basic.unquote (fun t -> t) FStar_Reflection_Basic.unembed_term (fun t -> t) FStar_Syntax_Syntax.t_unit)
in (

let uu____1354 = (

let uu____1357 = (mktac1 "__prune" FStar_Tactics_Basic.prune FStar_Syntax_Embeddings.unembed_string FStar_Syntax_Embeddings.embed_unit FStar_Syntax_Syntax.t_unit)
in (

let uu____1358 = (

let uu____1361 = (mktac1 "__addns" FStar_Tactics_Basic.addns FStar_Syntax_Embeddings.unembed_string FStar_Syntax_Embeddings.embed_unit FStar_Syntax_Syntax.t_unit)
in (

let uu____1362 = (

let uu____1365 = (mktac1 "__print" (fun x -> ((FStar_Tactics_Basic.tacprint x);
(FStar_Tactics_Basic.ret ());
)) FStar_Syntax_Embeddings.unembed_string FStar_Syntax_Embeddings.embed_unit FStar_Syntax_Syntax.t_unit)
in (

let uu____1370 = (

let uu____1373 = (mktac1 "__dump" FStar_Tactics_Basic.print_proof_state FStar_Syntax_Embeddings.unembed_string FStar_Syntax_Embeddings.embed_unit FStar_Syntax_Syntax.t_unit)
in (

let uu____1374 = (

let uu____1377 = (mktac1 "__dump1" FStar_Tactics_Basic.print_proof_state1 FStar_Syntax_Embeddings.unembed_string FStar_Syntax_Embeddings.embed_unit FStar_Syntax_Syntax.t_unit)
in (

let uu____1378 = (

let uu____1381 = (mktac1 "__pointwise" FStar_Tactics_Basic.pointwise (unembed_tactic_0 FStar_Syntax_Embeddings.unembed_unit) FStar_Syntax_Embeddings.embed_unit FStar_Syntax_Syntax.t_unit)
in (

let uu____1384 = (

let uu____1387 = (mktac0 "__trefl" FStar_Tactics_Basic.trefl FStar_Syntax_Embeddings.embed_unit FStar_Syntax_Syntax.t_unit)
in (

let uu____1388 = (

let uu____1391 = (mktac0 "__later" FStar_Tactics_Basic.later FStar_Syntax_Embeddings.embed_unit FStar_Syntax_Syntax.t_unit)
in (

let uu____1392 = (

let uu____1395 = (mktac0 "__dup" FStar_Tactics_Basic.dup FStar_Syntax_Embeddings.embed_unit FStar_Syntax_Syntax.t_unit)
in (

let uu____1396 = (

let uu____1399 = (mktac0 "__flip" FStar_Tactics_Basic.flip FStar_Syntax_Embeddings.embed_unit FStar_Syntax_Syntax.t_unit)
in (

let uu____1400 = (

let uu____1403 = (mktac0 "__qed" FStar_Tactics_Basic.qed FStar_Syntax_Embeddings.embed_unit FStar_Syntax_Syntax.t_unit)
in (

let uu____1404 = (

let uu____1407 = (

let uu____1408 = (FStar_Tactics_Embedding.pair_typ FStar_Reflection_Data.fstar_refl_term FStar_Reflection_Data.fstar_refl_term)
in (mktac1 "__cases" FStar_Tactics_Basic.cases FStar_Reflection_Basic.unembed_term (FStar_Syntax_Embeddings.embed_pair FStar_Reflection_Basic.embed_term FStar_Reflection_Data.fstar_refl_term FStar_Reflection_Basic.embed_term FStar_Reflection_Data.fstar_refl_term) uu____1408))
in (

let uu____1413 = (

let uu____1416 = (mktac0 "__cur_env" FStar_Tactics_Basic.cur_env FStar_Reflection_Basic.embed_env FStar_Reflection_Data.fstar_refl_env)
in (

let uu____1417 = (

let uu____1420 = (mktac0 "__cur_goal" FStar_Tactics_Basic.cur_goal' FStar_Reflection_Basic.embed_term FStar_Reflection_Data.fstar_refl_term)
in (

let uu____1421 = (

let uu____1424 = (mktac0 "__cur_witness" FStar_Tactics_Basic.cur_witness FStar_Reflection_Basic.embed_term FStar_Reflection_Data.fstar_refl_term)
in (

let uu____1425 = (

let uu____1428 = (mktac2 "__uvar_env" FStar_Tactics_Basic.uvar_env FStar_Reflection_Basic.unembed_env (FStar_Syntax_Embeddings.unembed_option FStar_Reflection_Basic.unembed_term) FStar_Reflection_Basic.embed_term FStar_Reflection_Data.fstar_refl_term)
in (

let uu____1431 = (

let uu____1434 = (mktac2 "__unify" FStar_Tactics_Basic.unify FStar_Reflection_Basic.unembed_term FStar_Reflection_Basic.unembed_term FStar_Syntax_Embeddings.embed_bool FStar_Syntax_Syntax.t_bool)
in (

let uu____1435 = (

let uu____1438 = (mktac3 "__launch_process" FStar_Tactics_Basic.launch_process FStar_Syntax_Embeddings.unembed_string FStar_Syntax_Embeddings.unembed_string FStar_Syntax_Embeddings.unembed_string FStar_Syntax_Embeddings.embed_string FStar_Syntax_Syntax.t_string)
in (uu____1438)::[])
in (uu____1434)::uu____1435))
in (uu____1428)::uu____1431))
in (uu____1424)::uu____1425))
in (uu____1420)::uu____1421))
in (uu____1416)::uu____1417))
in (uu____1407)::uu____1413))
in (uu____1403)::uu____1404))
in (uu____1399)::uu____1400))
in (uu____1395)::uu____1396))
in (uu____1391)::uu____1392))
in (uu____1387)::uu____1388))
in (uu____1381)::uu____1384))
in (uu____1377)::uu____1378))
in (uu____1373)::uu____1374))
in (uu____1365)::uu____1370))
in (uu____1361)::uu____1362))
in (uu____1357)::uu____1358))
in (uu____1349)::uu____1354))
in (uu____1341)::uu____1346))
in (uu____1337)::uu____1338))
in (uu____1309)::uu____1334))
in (uu____1305)::uu____1306))
in (uu____1301)::uu____1302))
in (uu____1297)::uu____1298))
in (uu____1293)::uu____1294))
in (uu____1289)::uu____1290))
in (uu____1285)::uu____1286))
in (uu____1281)::uu____1282))
in (uu____1277)::uu____1278))
in (uu____1273)::uu____1274))
in (uu____1269)::uu____1270))
in (uu____1265)::uu____1266))
in (uu____1259)::uu____1262))
in (uu____1253)::uu____1256))
in (uu____1244)::uu____1250))
in (uu____1240)::uu____1241))
in (uu____1224)::uu____1237))
in (uu____1220)::uu____1221))
in (FStar_List.append uu____1217 (FStar_List.append FStar_Reflection_Interpreter.reflection_primops native_tactics_steps))))))))))))
and unembed_tactic_0 : 'Ab . (FStar_Syntax_Syntax.term  ->  'Ab)  ->  FStar_Syntax_Syntax.term  ->  'Ab FStar_Tactics_Basic.tac = (fun unembed_b embedded_tac_b -> (FStar_Tactics_Basic.bind FStar_Tactics_Basic.get (fun proof_state -> (

let tm = (

let uu____1451 = (

let uu____1452 = (

let uu____1453 = (

let uu____1454 = (FStar_Tactics_Embedding.embed_proofstate proof_state)
in (FStar_Syntax_Syntax.as_arg uu____1454))
in (uu____1453)::[])
in (FStar_Syntax_Syntax.mk_Tm_app embedded_tac_b uu____1452))
in (uu____1451 FStar_Pervasives_Native.None FStar_Range.dummyRange))
in (

let steps = (FStar_TypeChecker_Normalize.Reify)::(FStar_TypeChecker_Normalize.UnfoldUntil (FStar_Syntax_Syntax.Delta_constant))::(FStar_TypeChecker_Normalize.UnfoldTac)::(FStar_TypeChecker_Normalize.Primops)::[]
in (

let uu____1460 = (FStar_All.pipe_left FStar_Tactics_Basic.mlog (fun uu____1469 -> (

let uu____1470 = (FStar_Syntax_Print.term_to_string tm)
in (FStar_Util.print1 "Starting normalizer with %s\n" uu____1470))))
in (FStar_Tactics_Basic.bind uu____1460 (fun uu____1474 -> (

let result = (

let uu____1476 = (primitive_steps proof_state)
in (FStar_TypeChecker_Normalize.normalize_with_primitive_steps uu____1476 steps proof_state.FStar_Tactics_Types.main_context tm))
in (

let uu____1479 = (FStar_All.pipe_left FStar_Tactics_Basic.mlog (fun uu____1488 -> (

let uu____1489 = (FStar_Syntax_Print.term_to_string result)
in (FStar_Util.print1 "Reduced tactic: got %s\n" uu____1489))))
in (FStar_Tactics_Basic.bind uu____1479 (fun uu____1495 -> (

let uu____1496 = (FStar_Tactics_Embedding.unembed_result proof_state result unembed_b)
in (match (uu____1496) with
| FStar_Util.Inl (b, ps) -> begin
(

let uu____1521 = (FStar_Tactics_Basic.set ps)
in (FStar_Tactics_Basic.bind uu____1521 (fun uu____1525 -> (FStar_Tactics_Basic.ret b))))
end
| FStar_Util.Inr (msg, ps) -> begin
(

let uu____1536 = (FStar_Tactics_Basic.set ps)
in (FStar_Tactics_Basic.bind uu____1536 (fun uu____1540 -> (FStar_Tactics_Basic.fail msg))))
end))))))))))))))


let run_tactic_on_typ : FStar_Syntax_Syntax.term  ->  FStar_Tactics_Basic.env  ->  FStar_Syntax_Syntax.typ  ->  (FStar_Tactics_Types.goal Prims.list * FStar_Syntax_Syntax.term) = (fun tactic env typ -> (

let tactic1 = (FStar_TypeChecker_Normalize.reduce_uvar_solutions env tactic)
in ((

let uu____1567 = (FStar_Syntax_Print.term_to_string tactic1)
in (FStar_Util.print1 "About to check tactic term: %s\n" uu____1567));
(

let uu____1568 = (FStar_TypeChecker_TcTerm.tc_reified_tactic env tactic1)
in (match (uu____1568) with
| (tactic2, uu____1582, uu____1583) -> begin
(

let tau = (unembed_tactic_0 FStar_Syntax_Embeddings.unembed_unit tactic2)
in (

let uu____1587 = (FStar_TypeChecker_Env.clear_expected_typ env)
in (match (uu____1587) with
| (env1, uu____1601) -> begin
(

let env2 = (

let uu___128_1607 = env1
in {FStar_TypeChecker_Env.solver = uu___128_1607.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = uu___128_1607.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = uu___128_1607.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = uu___128_1607.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_cache = uu___128_1607.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = uu___128_1607.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = uu___128_1607.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = uu___128_1607.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.is_pattern = uu___128_1607.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = false; FStar_TypeChecker_Env.effects = uu___128_1607.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = uu___128_1607.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = uu___128_1607.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = uu___128_1607.FStar_TypeChecker_Env.top_level; FStar_TypeChecker_Env.check_uvars = uu___128_1607.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = uu___128_1607.FStar_TypeChecker_Env.use_eq; FStar_TypeChecker_Env.is_iface = uu___128_1607.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = uu___128_1607.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.lax = uu___128_1607.FStar_TypeChecker_Env.lax; FStar_TypeChecker_Env.lax_universes = uu___128_1607.FStar_TypeChecker_Env.lax_universes; FStar_TypeChecker_Env.failhard = uu___128_1607.FStar_TypeChecker_Env.failhard; FStar_TypeChecker_Env.nosynth = uu___128_1607.FStar_TypeChecker_Env.nosynth; FStar_TypeChecker_Env.type_of = uu___128_1607.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = uu___128_1607.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.use_bv_sorts = uu___128_1607.FStar_TypeChecker_Env.use_bv_sorts; FStar_TypeChecker_Env.qname_and_index = uu___128_1607.FStar_TypeChecker_Env.qname_and_index; FStar_TypeChecker_Env.proof_ns = uu___128_1607.FStar_TypeChecker_Env.proof_ns; FStar_TypeChecker_Env.synth = uu___128_1607.FStar_TypeChecker_Env.synth; FStar_TypeChecker_Env.is_native_tactic = uu___128_1607.FStar_TypeChecker_Env.is_native_tactic; FStar_TypeChecker_Env.identifier_info = uu___128_1607.FStar_TypeChecker_Env.identifier_info})
in (

let uu____1608 = (FStar_Tactics_Basic.proofstate_of_goal_ty env2 typ)
in (match (uu____1608) with
| (ps, w) -> begin
(

let r = (FStar_All.try_with (fun uu___130_1627 -> (match (()) with
| () -> begin
(FStar_Tactics_Basic.run tau ps)
end)) (fun uu___129_1632 -> (match (uu___129_1632) with
| FStar_Tactics_Basic.TacFailure (s) -> begin
FStar_Tactics_Result.Failed ((((Prims.strcat "EXCEPTION: " s)), (ps)))
end)))
in (match (r) with
| FStar_Tactics_Result.Success (uu____1642, ps1) -> begin
((

let uu____1645 = (FStar_ST.op_Bang tacdbg)
in (match (uu____1645) with
| true -> begin
(

let uu____1656 = (FStar_Syntax_Print.term_to_string w)
in (FStar_Util.print1 "Tactic generated proofterm %s\n" uu____1656))
end
| uu____1657 -> begin
()
end));
(FStar_List.iter (fun g -> (

let uu____1663 = (FStar_Tactics_Basic.is_irrelevant g)
in (match (uu____1663) with
| true -> begin
(

let uu____1664 = (FStar_TypeChecker_Rel.teq_nosmt g.FStar_Tactics_Types.context g.FStar_Tactics_Types.witness FStar_Syntax_Util.exp_unit)
in (match (uu____1664) with
| true -> begin
()
end
| uu____1665 -> begin
(

let uu____1666 = (

let uu____1667 = (FStar_Syntax_Print.term_to_string g.FStar_Tactics_Types.witness)
in (FStar_Util.format1 "Irrelevant tactic witness does not unify with (): %s" uu____1667))
in (failwith uu____1666))
end))
end
| uu____1668 -> begin
()
end))) (FStar_List.append ps1.FStar_Tactics_Types.goals ps1.FStar_Tactics_Types.smt_goals));
(

let g = (

let uu___131_1670 = FStar_TypeChecker_Rel.trivial_guard
in {FStar_TypeChecker_Env.guard_f = uu___131_1670.FStar_TypeChecker_Env.guard_f; FStar_TypeChecker_Env.deferred = uu___131_1670.FStar_TypeChecker_Env.deferred; FStar_TypeChecker_Env.univ_ineqs = uu___131_1670.FStar_TypeChecker_Env.univ_ineqs; FStar_TypeChecker_Env.implicits = ps1.FStar_Tactics_Types.all_implicits})
in (

let g1 = (

let uu____1672 = (FStar_TypeChecker_Rel.solve_deferred_constraints env2 g)
in (FStar_All.pipe_right uu____1672 FStar_TypeChecker_Rel.resolve_implicits_lax))
in ((FStar_TypeChecker_Rel.force_trivial_guard env2 g1);
(((FStar_List.append ps1.FStar_Tactics_Types.goals ps1.FStar_Tactics_Types.smt_goals)), (w));
)));
)
end
| FStar_Tactics_Result.Failed (s, ps1) -> begin
((FStar_Tactics_Basic.dump_proofstate ps1 "at the time of failure");
(

let uu____1679 = (

let uu____1680 = (

let uu____1685 = (FStar_Util.format1 "user tactic failed: %s" s)
in ((uu____1685), (typ.FStar_Syntax_Syntax.pos)))
in FStar_Errors.Error (uu____1680))
in (FStar_Exn.raise uu____1679));
)
end))
end)))
end)))
end));
)))

type pol =
| Pos
| Neg


let uu___is_Pos : pol  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Pos -> begin
true
end
| uu____1696 -> begin
false
end))


let uu___is_Neg : pol  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Neg -> begin
true
end
| uu____1701 -> begin
false
end))


let flip : pol  ->  pol = (fun p -> (match (p) with
| Pos -> begin
Neg
end
| Neg -> begin
Pos
end))


let by_tactic_interp : pol  ->  FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.term * FStar_Tactics_Types.goal Prims.list) = (fun pol e t -> (

let uu____1730 = (FStar_Syntax_Util.head_and_args t)
in (match (uu____1730) with
| (hd1, args) -> begin
(

let uu____1773 = (

let uu____1786 = (

let uu____1787 = (FStar_Syntax_Util.un_uinst hd1)
in uu____1787.FStar_Syntax_Syntax.n)
in ((uu____1786), (args)))
in (match (uu____1773) with
| (FStar_Syntax_Syntax.Tm_fvar (fv), ((rett, FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Implicit (uu____1806))))::((tactic, FStar_Pervasives_Native.None))::((assertion, FStar_Pervasives_Native.None))::[]) when (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.by_tactic_lid) -> begin
(match ((Prims.op_Equality pol Pos)) with
| true -> begin
(

let uu____1875 = (run_tactic_on_typ tactic e assertion)
in (match (uu____1875) with
| (gs, uu____1889) -> begin
((FStar_Syntax_Util.t_true), (gs))
end))
end
| uu____1896 -> begin
((assertion), ([]))
end)
end
| (FStar_Syntax_Syntax.Tm_fvar (fv), ((assertion, FStar_Pervasives_Native.None))::[]) when (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.spinoff_lid) -> begin
(match ((Prims.op_Equality pol Pos)) with
| true -> begin
(

let uu____1941 = (

let uu____1944 = (

let uu____1945 = (FStar_Tactics_Basic.goal_of_goal_ty e assertion)
in (FStar_All.pipe_left FStar_Pervasives_Native.fst uu____1945))
in (uu____1944)::[])
in ((FStar_Syntax_Util.t_true), (uu____1941)))
end
| uu____1956 -> begin
((assertion), ([]))
end)
end
| uu____1961 -> begin
((t), ([]))
end))
end)))


let rec traverse : (pol  ->  FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.term * FStar_Tactics_Types.goal Prims.list))  ->  pol  ->  FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.term * FStar_Tactics_Types.goal Prims.list) = (fun f pol e t -> (

let uu____2031 = (

let uu____2038 = (

let uu____2039 = (FStar_Syntax_Subst.compress t)
in uu____2039.FStar_Syntax_Syntax.n)
in (match (uu____2038) with
| FStar_Syntax_Syntax.Tm_uinst (t1, us) -> begin
(

let uu____2054 = (traverse f pol e t1)
in (match (uu____2054) with
| (t', gs) -> begin
((FStar_Syntax_Syntax.Tm_uinst (((t'), (us)))), (gs))
end))
end
| FStar_Syntax_Syntax.Tm_meta (t1, m) -> begin
(

let uu____2081 = (traverse f pol e t1)
in (match (uu____2081) with
| (t', gs) -> begin
((FStar_Syntax_Syntax.Tm_meta (((t'), (m)))), (gs))
end))
end
| FStar_Syntax_Syntax.Tm_app ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar (fv); FStar_Syntax_Syntax.pos = uu____2103; FStar_Syntax_Syntax.vars = uu____2104}, ((p, uu____2106))::((q, uu____2108))::[]) when (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.imp_lid) -> begin
(

let x = (

let uu____2148 = (FStar_Syntax_Util.mk_squash p)
in (FStar_Syntax_Syntax.new_bv FStar_Pervasives_Native.None uu____2148))
in (

let uu____2149 = (traverse f (flip pol) e p)
in (match (uu____2149) with
| (p', gs1) -> begin
(

let uu____2168 = (

let uu____2175 = (FStar_TypeChecker_Env.push_bv e x)
in (traverse f pol uu____2175 q))
in (match (uu____2168) with
| (q', gs2) -> begin
(

let uu____2188 = (

let uu____2189 = (FStar_Syntax_Util.mk_imp p' q')
in uu____2189.FStar_Syntax_Syntax.n)
in ((uu____2188), ((FStar_List.append gs1 gs2))))
end))
end)))
end
| FStar_Syntax_Syntax.Tm_app (hd1, args) -> begin
(

let uu____2216 = (traverse f pol e hd1)
in (match (uu____2216) with
| (hd', gs1) -> begin
(

let uu____2235 = (FStar_List.fold_right (fun uu____2273 uu____2274 -> (match (((uu____2273), (uu____2274))) with
| ((a, q), (as', gs)) -> begin
(

let uu____2355 = (traverse f pol e a)
in (match (uu____2355) with
| (a', gs') -> begin
(((((a'), (q)))::as'), ((FStar_List.append gs gs')))
end))
end)) args (([]), ([])))
in (match (uu____2235) with
| (as', gs2) -> begin
((FStar_Syntax_Syntax.Tm_app (((hd'), (as')))), ((FStar_List.append gs1 gs2)))
end))
end))
end
| FStar_Syntax_Syntax.Tm_abs (bs, t1, k) -> begin
(

let uu____2459 = (FStar_Syntax_Subst.open_term bs t1)
in (match (uu____2459) with
| (bs1, topen) -> begin
(

let e' = (FStar_TypeChecker_Env.push_binders e bs1)
in (

let uu____2473 = (

let uu____2488 = (FStar_List.map (fun uu____2521 -> (match (uu____2521) with
| (bv, aq) -> begin
(

let uu____2538 = (traverse f (flip pol) e bv.FStar_Syntax_Syntax.sort)
in (match (uu____2538) with
| (s', gs) -> begin
(((((

let uu___132_2568 = bv
in {FStar_Syntax_Syntax.ppname = uu___132_2568.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = uu___132_2568.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = s'})), (aq))), (gs))
end))
end)) bs1)
in (FStar_All.pipe_left FStar_List.unzip uu____2488))
in (match (uu____2473) with
| (bs2, gs1) -> begin
(

let gs11 = (FStar_List.flatten gs1)
in (

let uu____2632 = (traverse f pol e' topen)
in (match (uu____2632) with
| (topen', gs2) -> begin
(

let uu____2651 = (

let uu____2652 = (FStar_Syntax_Util.abs bs2 topen' k)
in uu____2652.FStar_Syntax_Syntax.n)
in ((uu____2651), ((FStar_List.append gs11 gs2))))
end)))
end)))
end))
end
| x -> begin
((x), ([]))
end))
in (match (uu____2031) with
| (tn', gs) -> begin
(

let t' = (

let uu___133_2675 = t
in {FStar_Syntax_Syntax.n = tn'; FStar_Syntax_Syntax.pos = uu___133_2675.FStar_Syntax_Syntax.pos; FStar_Syntax_Syntax.vars = uu___133_2675.FStar_Syntax_Syntax.vars})
in (

let uu____2676 = (f pol e t')
in (match (uu____2676) with
| (t'1, gs') -> begin
((t'1), ((FStar_List.append gs gs')))
end)))
end)))


let getprop : FStar_Tactics_Basic.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term FStar_Pervasives_Native.option = (fun e t -> (

let tn = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.WHNF)::(FStar_TypeChecker_Normalize.UnfoldUntil (FStar_Syntax_Syntax.Delta_constant))::[]) e t)
in (FStar_Syntax_Util.un_squash tn)))


let preprocess : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  (FStar_TypeChecker_Env.env * FStar_Syntax_Syntax.term * FStar_Options.optionstate) Prims.list = (fun env goal -> ((

let uu____2735 = (FStar_TypeChecker_Env.debug env (FStar_Options.Other ("Tac")))
in (FStar_ST.op_Colon_Equals tacdbg uu____2735));
(

let uu____2747 = (FStar_ST.op_Bang tacdbg)
in (match (uu____2747) with
| true -> begin
(

let uu____2758 = (

let uu____2759 = (FStar_TypeChecker_Env.all_binders env)
in (FStar_All.pipe_right uu____2759 (FStar_Syntax_Print.binders_to_string ",")))
in (

let uu____2760 = (FStar_Syntax_Print.term_to_string goal)
in (FStar_Util.print2 "About to preprocess %s |= %s\n" uu____2758 uu____2760)))
end
| uu____2761 -> begin
()
end));
(

let initial = (((Prims.parse_int "1")), ([]))
in (

let uu____2789 = (traverse by_tactic_interp Pos env goal)
in (match (uu____2789) with
| (t', gs) -> begin
((

let uu____2811 = (FStar_ST.op_Bang tacdbg)
in (match (uu____2811) with
| true -> begin
(

let uu____2822 = (

let uu____2823 = (FStar_TypeChecker_Env.all_binders env)
in (FStar_All.pipe_right uu____2823 (FStar_Syntax_Print.binders_to_string ", ")))
in (

let uu____2824 = (FStar_Syntax_Print.term_to_string t')
in (FStar_Util.print2 "Main goal simplified to: %s |- %s\n" uu____2822 uu____2824)))
end
| uu____2825 -> begin
()
end));
(

let s = initial
in (

let s1 = (FStar_List.fold_left (fun uu____2871 g -> (match (uu____2871) with
| (n1, gs1) -> begin
(

let phi = (

let uu____2916 = (getprop g.FStar_Tactics_Types.context g.FStar_Tactics_Types.goal_ty)
in (match (uu____2916) with
| FStar_Pervasives_Native.None -> begin
(

let uu____2919 = (

let uu____2920 = (FStar_Syntax_Print.term_to_string g.FStar_Tactics_Types.goal_ty)
in (FStar_Util.format1 "Tactic returned proof-relevant goal: %s" uu____2920))
in (failwith uu____2919))
end
| FStar_Pervasives_Native.Some (phi) -> begin
phi
end))
in ((

let uu____2923 = (FStar_ST.op_Bang tacdbg)
in (match (uu____2923) with
| true -> begin
(

let uu____2934 = (FStar_Util.string_of_int n1)
in (

let uu____2935 = (FStar_Tactics_Basic.goal_to_string g)
in (FStar_Util.print2 "Got goal #%s: %s\n" uu____2934 uu____2935)))
end
| uu____2936 -> begin
()
end));
(

let gt' = (

let uu____2938 = (

let uu____2939 = (FStar_Util.string_of_int n1)
in (Prims.strcat "Could not prove goal #" uu____2939))
in (FStar_TypeChecker_Util.label uu____2938 goal.FStar_Syntax_Syntax.pos phi))
in (((n1 + (Prims.parse_int "1"))), ((((g.FStar_Tactics_Types.context), (gt'), (g.FStar_Tactics_Types.opts)))::gs1)));
))
end)) s gs)
in (

let uu____2954 = s1
in (match (uu____2954) with
| (uu____2975, gs1) -> begin
(

let uu____2993 = (

let uu____3000 = (FStar_Options.peek ())
in ((env), (t'), (uu____3000)))
in (uu____2993)::gs1)
end))));
)
end)));
))


let reify_tactic : FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term = (fun a -> (

let r = (

let uu____3012 = (

let uu____3013 = (FStar_Syntax_Syntax.lid_as_fv FStar_Parser_Const.reify_tactic_lid FStar_Syntax_Syntax.Delta_equational FStar_Pervasives_Native.None)
in (FStar_Syntax_Syntax.fv_to_tm uu____3013))
in (FStar_Syntax_Syntax.mk_Tm_uinst uu____3012 ((FStar_Syntax_Syntax.U_zero)::[])))
in (

let uu____3014 = (

let uu____3015 = (

let uu____3016 = (FStar_Syntax_Syntax.iarg FStar_Syntax_Syntax.t_unit)
in (

let uu____3017 = (

let uu____3020 = (FStar_Syntax_Syntax.as_arg a)
in (uu____3020)::[])
in (uu____3016)::uu____3017))
in (FStar_Syntax_Syntax.mk_Tm_app r uu____3015))
in (uu____3014 FStar_Pervasives_Native.None a.FStar_Syntax_Syntax.pos))))


let synth : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.typ  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term = (fun env typ tau -> ((

let uu____3036 = (FStar_TypeChecker_Env.debug env (FStar_Options.Other ("Tac")))
in (FStar_ST.op_Colon_Equals tacdbg uu____3036));
(

let uu____3047 = (

let uu____3054 = (reify_tactic tau)
in (run_tactic_on_typ uu____3054 env typ))
in (match (uu____3047) with
| (gs, w) -> begin
(

let uu____3061 = (FStar_List.existsML (fun g -> (

let uu____3065 = (

let uu____3066 = (getprop g.FStar_Tactics_Types.context g.FStar_Tactics_Types.goal_ty)
in (FStar_Option.isSome uu____3066))
in (not (uu____3065)))) gs)
in (match (uu____3061) with
| true -> begin
(FStar_Exn.raise (FStar_Errors.Error ((("synthesis left open goals"), (typ.FStar_Syntax_Syntax.pos)))))
end
| uu____3069 -> begin
w
end))
end));
))




