open Prims
let (instantiate_both :
  FStar_TypeChecker_Env.env -> FStar_TypeChecker_Env.env) =
  fun env  ->
    let uu___8_5 = env  in
    {
      FStar_TypeChecker_Env.solver = (uu___8_5.FStar_TypeChecker_Env.solver);
      FStar_TypeChecker_Env.range = (uu___8_5.FStar_TypeChecker_Env.range);
      FStar_TypeChecker_Env.curmodule =
        (uu___8_5.FStar_TypeChecker_Env.curmodule);
      FStar_TypeChecker_Env.gamma = (uu___8_5.FStar_TypeChecker_Env.gamma);
      FStar_TypeChecker_Env.gamma_sig =
        (uu___8_5.FStar_TypeChecker_Env.gamma_sig);
      FStar_TypeChecker_Env.gamma_cache =
        (uu___8_5.FStar_TypeChecker_Env.gamma_cache);
      FStar_TypeChecker_Env.modules =
        (uu___8_5.FStar_TypeChecker_Env.modules);
      FStar_TypeChecker_Env.expected_typ =
        (uu___8_5.FStar_TypeChecker_Env.expected_typ);
      FStar_TypeChecker_Env.sigtab = (uu___8_5.FStar_TypeChecker_Env.sigtab);
      FStar_TypeChecker_Env.attrtab =
        (uu___8_5.FStar_TypeChecker_Env.attrtab);
      FStar_TypeChecker_Env.instantiate_imp = true;
      FStar_TypeChecker_Env.effects =
        (uu___8_5.FStar_TypeChecker_Env.effects);
      FStar_TypeChecker_Env.generalize =
        (uu___8_5.FStar_TypeChecker_Env.generalize);
      FStar_TypeChecker_Env.letrecs =
        (uu___8_5.FStar_TypeChecker_Env.letrecs);
      FStar_TypeChecker_Env.top_level =
        (uu___8_5.FStar_TypeChecker_Env.top_level);
      FStar_TypeChecker_Env.check_uvars =
        (uu___8_5.FStar_TypeChecker_Env.check_uvars);
      FStar_TypeChecker_Env.use_eq = (uu___8_5.FStar_TypeChecker_Env.use_eq);
      FStar_TypeChecker_Env.is_iface =
        (uu___8_5.FStar_TypeChecker_Env.is_iface);
      FStar_TypeChecker_Env.admit = (uu___8_5.FStar_TypeChecker_Env.admit);
      FStar_TypeChecker_Env.lax = (uu___8_5.FStar_TypeChecker_Env.lax);
      FStar_TypeChecker_Env.lax_universes =
        (uu___8_5.FStar_TypeChecker_Env.lax_universes);
      FStar_TypeChecker_Env.phase1 = (uu___8_5.FStar_TypeChecker_Env.phase1);
      FStar_TypeChecker_Env.failhard =
        (uu___8_5.FStar_TypeChecker_Env.failhard);
      FStar_TypeChecker_Env.nosynth =
        (uu___8_5.FStar_TypeChecker_Env.nosynth);
      FStar_TypeChecker_Env.uvar_subtyping =
        (uu___8_5.FStar_TypeChecker_Env.uvar_subtyping);
      FStar_TypeChecker_Env.tc_term =
        (uu___8_5.FStar_TypeChecker_Env.tc_term);
      FStar_TypeChecker_Env.type_of =
        (uu___8_5.FStar_TypeChecker_Env.type_of);
      FStar_TypeChecker_Env.universe_of =
        (uu___8_5.FStar_TypeChecker_Env.universe_of);
      FStar_TypeChecker_Env.check_type_of =
        (uu___8_5.FStar_TypeChecker_Env.check_type_of);
      FStar_TypeChecker_Env.use_bv_sorts =
        (uu___8_5.FStar_TypeChecker_Env.use_bv_sorts);
      FStar_TypeChecker_Env.qtbl_name_and_index =
        (uu___8_5.FStar_TypeChecker_Env.qtbl_name_and_index);
      FStar_TypeChecker_Env.normalized_eff_names =
        (uu___8_5.FStar_TypeChecker_Env.normalized_eff_names);
      FStar_TypeChecker_Env.fv_delta_depths =
        (uu___8_5.FStar_TypeChecker_Env.fv_delta_depths);
      FStar_TypeChecker_Env.proof_ns =
        (uu___8_5.FStar_TypeChecker_Env.proof_ns);
      FStar_TypeChecker_Env.synth_hook =
        (uu___8_5.FStar_TypeChecker_Env.synth_hook);
      FStar_TypeChecker_Env.splice = (uu___8_5.FStar_TypeChecker_Env.splice);
      FStar_TypeChecker_Env.mpreprocess =
        (uu___8_5.FStar_TypeChecker_Env.mpreprocess);
      FStar_TypeChecker_Env.postprocess =
        (uu___8_5.FStar_TypeChecker_Env.postprocess);
      FStar_TypeChecker_Env.is_native_tactic =
        (uu___8_5.FStar_TypeChecker_Env.is_native_tactic);
      FStar_TypeChecker_Env.identifier_info =
        (uu___8_5.FStar_TypeChecker_Env.identifier_info);
      FStar_TypeChecker_Env.tc_hooks =
        (uu___8_5.FStar_TypeChecker_Env.tc_hooks);
      FStar_TypeChecker_Env.dsenv = (uu___8_5.FStar_TypeChecker_Env.dsenv);
      FStar_TypeChecker_Env.nbe = (uu___8_5.FStar_TypeChecker_Env.nbe);
      FStar_TypeChecker_Env.strict_args_tab =
        (uu___8_5.FStar_TypeChecker_Env.strict_args_tab);
      FStar_TypeChecker_Env.erasable_types_tab =
        (uu___8_5.FStar_TypeChecker_Env.erasable_types_tab)
    }
  
let (no_inst : FStar_TypeChecker_Env.env -> FStar_TypeChecker_Env.env) =
  fun env  ->
    let uu___11_13 = env  in
    {
      FStar_TypeChecker_Env.solver =
        (uu___11_13.FStar_TypeChecker_Env.solver);
      FStar_TypeChecker_Env.range = (uu___11_13.FStar_TypeChecker_Env.range);
      FStar_TypeChecker_Env.curmodule =
        (uu___11_13.FStar_TypeChecker_Env.curmodule);
      FStar_TypeChecker_Env.gamma = (uu___11_13.FStar_TypeChecker_Env.gamma);
      FStar_TypeChecker_Env.gamma_sig =
        (uu___11_13.FStar_TypeChecker_Env.gamma_sig);
      FStar_TypeChecker_Env.gamma_cache =
        (uu___11_13.FStar_TypeChecker_Env.gamma_cache);
      FStar_TypeChecker_Env.modules =
        (uu___11_13.FStar_TypeChecker_Env.modules);
      FStar_TypeChecker_Env.expected_typ =
        (uu___11_13.FStar_TypeChecker_Env.expected_typ);
      FStar_TypeChecker_Env.sigtab =
        (uu___11_13.FStar_TypeChecker_Env.sigtab);
      FStar_TypeChecker_Env.attrtab =
        (uu___11_13.FStar_TypeChecker_Env.attrtab);
      FStar_TypeChecker_Env.instantiate_imp = false;
      FStar_TypeChecker_Env.effects =
        (uu___11_13.FStar_TypeChecker_Env.effects);
      FStar_TypeChecker_Env.generalize =
        (uu___11_13.FStar_TypeChecker_Env.generalize);
      FStar_TypeChecker_Env.letrecs =
        (uu___11_13.FStar_TypeChecker_Env.letrecs);
      FStar_TypeChecker_Env.top_level =
        (uu___11_13.FStar_TypeChecker_Env.top_level);
      FStar_TypeChecker_Env.check_uvars =
        (uu___11_13.FStar_TypeChecker_Env.check_uvars);
      FStar_TypeChecker_Env.use_eq =
        (uu___11_13.FStar_TypeChecker_Env.use_eq);
      FStar_TypeChecker_Env.is_iface =
        (uu___11_13.FStar_TypeChecker_Env.is_iface);
      FStar_TypeChecker_Env.admit = (uu___11_13.FStar_TypeChecker_Env.admit);
      FStar_TypeChecker_Env.lax = (uu___11_13.FStar_TypeChecker_Env.lax);
      FStar_TypeChecker_Env.lax_universes =
        (uu___11_13.FStar_TypeChecker_Env.lax_universes);
      FStar_TypeChecker_Env.phase1 =
        (uu___11_13.FStar_TypeChecker_Env.phase1);
      FStar_TypeChecker_Env.failhard =
        (uu___11_13.FStar_TypeChecker_Env.failhard);
      FStar_TypeChecker_Env.nosynth =
        (uu___11_13.FStar_TypeChecker_Env.nosynth);
      FStar_TypeChecker_Env.uvar_subtyping =
        (uu___11_13.FStar_TypeChecker_Env.uvar_subtyping);
      FStar_TypeChecker_Env.tc_term =
        (uu___11_13.FStar_TypeChecker_Env.tc_term);
      FStar_TypeChecker_Env.type_of =
        (uu___11_13.FStar_TypeChecker_Env.type_of);
      FStar_TypeChecker_Env.universe_of =
        (uu___11_13.FStar_TypeChecker_Env.universe_of);
      FStar_TypeChecker_Env.check_type_of =
        (uu___11_13.FStar_TypeChecker_Env.check_type_of);
      FStar_TypeChecker_Env.use_bv_sorts =
        (uu___11_13.FStar_TypeChecker_Env.use_bv_sorts);
      FStar_TypeChecker_Env.qtbl_name_and_index =
        (uu___11_13.FStar_TypeChecker_Env.qtbl_name_and_index);
      FStar_TypeChecker_Env.normalized_eff_names =
        (uu___11_13.FStar_TypeChecker_Env.normalized_eff_names);
      FStar_TypeChecker_Env.fv_delta_depths =
        (uu___11_13.FStar_TypeChecker_Env.fv_delta_depths);
      FStar_TypeChecker_Env.proof_ns =
        (uu___11_13.FStar_TypeChecker_Env.proof_ns);
      FStar_TypeChecker_Env.synth_hook =
        (uu___11_13.FStar_TypeChecker_Env.synth_hook);
      FStar_TypeChecker_Env.splice =
        (uu___11_13.FStar_TypeChecker_Env.splice);
      FStar_TypeChecker_Env.mpreprocess =
        (uu___11_13.FStar_TypeChecker_Env.mpreprocess);
      FStar_TypeChecker_Env.postprocess =
        (uu___11_13.FStar_TypeChecker_Env.postprocess);
      FStar_TypeChecker_Env.is_native_tactic =
        (uu___11_13.FStar_TypeChecker_Env.is_native_tactic);
      FStar_TypeChecker_Env.identifier_info =
        (uu___11_13.FStar_TypeChecker_Env.identifier_info);
      FStar_TypeChecker_Env.tc_hooks =
        (uu___11_13.FStar_TypeChecker_Env.tc_hooks);
      FStar_TypeChecker_Env.dsenv = (uu___11_13.FStar_TypeChecker_Env.dsenv);
      FStar_TypeChecker_Env.nbe = (uu___11_13.FStar_TypeChecker_Env.nbe);
      FStar_TypeChecker_Env.strict_args_tab =
        (uu___11_13.FStar_TypeChecker_Env.strict_args_tab);
      FStar_TypeChecker_Env.erasable_types_tab =
        (uu___11_13.FStar_TypeChecker_Env.erasable_types_tab)
    }
  
let (mk_lex_list :
  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax Prims.list ->
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax)
  =
  fun vs  ->
    FStar_List.fold_right
      (fun v1  ->
         fun tl1  ->
           let r =
             if tl1.FStar_Syntax_Syntax.pos = FStar_Range.dummyRange
             then v1.FStar_Syntax_Syntax.pos
             else
               FStar_Range.union_ranges v1.FStar_Syntax_Syntax.pos
                 tl1.FStar_Syntax_Syntax.pos
              in
           let uu____49 =
             let uu____54 =
               let uu____55 = FStar_Syntax_Syntax.as_arg v1  in
               let uu____64 =
                 let uu____75 = FStar_Syntax_Syntax.as_arg tl1  in [uu____75]
                  in
               uu____55 :: uu____64  in
             FStar_Syntax_Syntax.mk_Tm_app FStar_Syntax_Util.lex_pair
               uu____54
              in
           uu____49 FStar_Pervasives_Native.None r) vs
      FStar_Syntax_Util.lex_top
  
let (is_eq :
  FStar_Syntax_Syntax.arg_qualifier FStar_Pervasives_Native.option ->
    Prims.bool)
  =
  fun uu___0_116  ->
    match uu___0_116 with
    | FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Equality ) -> true
    | uu____121 -> false
  
let steps :
  'Auu____130 . 'Auu____130 -> FStar_TypeChecker_Env.step Prims.list =
  fun env  ->
    [FStar_TypeChecker_Env.Beta;
    FStar_TypeChecker_Env.Eager_unfolding;
    FStar_TypeChecker_Env.NoFullNorm]
  
let (norm :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term)
  =
  fun env  ->
    fun t  -> FStar_TypeChecker_Normalize.normalize (steps env) env t
  
let (norm_c :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.comp -> FStar_Syntax_Syntax.comp)
  =
  fun env  ->
    fun c  -> FStar_TypeChecker_Normalize.normalize_comp (steps env) env c
  
let (check_no_escape :
  FStar_Syntax_Syntax.term FStar_Pervasives_Native.option ->
    FStar_TypeChecker_Env.env ->
      FStar_Syntax_Syntax.bv Prims.list ->
        FStar_Syntax_Syntax.term ->
          (FStar_Syntax_Syntax.term * FStar_TypeChecker_Common.guard_t))
  =
  fun head_opt  ->
    fun env  ->
      fun fvs  ->
        fun kt  ->
          let rec aux try_norm t =
            match fvs with
            | [] -> (t, FStar_TypeChecker_Env.trivial_guard)
            | uu____218 ->
                let t1 = if try_norm then norm env t else t  in
                let fvs' = FStar_Syntax_Free.names t1  in
                let uu____232 =
                  FStar_List.tryFind (fun x  -> FStar_Util.set_mem x fvs')
                    fvs
                   in
                (match uu____232 with
                 | FStar_Pervasives_Native.None  ->
                     (t1, FStar_TypeChecker_Env.trivial_guard)
                 | FStar_Pervasives_Native.Some x ->
                     if Prims.op_Negation try_norm
                     then aux true t1
                     else
                       (let fail1 uu____259 =
                          let msg =
                            match head_opt with
                            | FStar_Pervasives_Native.None  ->
                                let uu____263 =
                                  FStar_Syntax_Print.bv_to_string x  in
                                FStar_Util.format1
                                  "Bound variables '%s' escapes; add a type annotation"
                                  uu____263
                            | FStar_Pervasives_Native.Some head1 ->
                                let uu____267 =
                                  FStar_Syntax_Print.bv_to_string x  in
                                let uu____269 =
                                  FStar_TypeChecker_Normalize.term_to_string
                                    env head1
                                   in
                                FStar_Util.format2
                                  "Bound variables '%s' in the type of '%s' escape because of impure applications; add explicit let-bindings"
                                  uu____267 uu____269
                             in
                          let uu____272 = FStar_TypeChecker_Env.get_range env
                             in
                          FStar_Errors.raise_error
                            (FStar_Errors.Fatal_EscapedBoundVar, msg)
                            uu____272
                           in
                        let uu____278 =
                          let uu____291 = FStar_TypeChecker_Env.get_range env
                             in
                          let uu____292 =
                            let uu____293 = FStar_Syntax_Util.type_u ()  in
                            FStar_All.pipe_left FStar_Pervasives_Native.fst
                              uu____293
                             in
                          FStar_TypeChecker_Util.new_implicit_var "no escape"
                            uu____291 env uu____292
                           in
                        match uu____278 with
                        | (s,uu____308,g0) ->
                            let uu____322 =
                              FStar_TypeChecker_Rel.try_teq true env t1 s  in
                            (match uu____322 with
                             | FStar_Pervasives_Native.Some g ->
                                 let g1 =
                                   let uu____332 =
                                     FStar_TypeChecker_Env.conj_guard g g0
                                      in
                                   FStar_TypeChecker_Rel.solve_deferred_constraints
                                     env uu____332
                                    in
                                 (s, g1)
                             | uu____333 -> fail1 ())))
             in
          aux false kt
  
let push_binding :
  'Auu____344 .
    FStar_TypeChecker_Env.env ->
      (FStar_Syntax_Syntax.bv * 'Auu____344) -> FStar_TypeChecker_Env.env
  =
  fun env  ->
    fun b  ->
      FStar_TypeChecker_Env.push_bv env (FStar_Pervasives_Native.fst b)
  
let (maybe_extend_subst :
  FStar_Syntax_Syntax.subst_elt Prims.list ->
    (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.arg_qualifier
      FStar_Pervasives_Native.option) ->
      FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
        FStar_Syntax_Syntax.subst_t)
  =
  fun s  ->
    fun b  ->
      fun v1  ->
        let uu____399 = FStar_Syntax_Syntax.is_null_binder b  in
        if uu____399
        then s
        else (FStar_Syntax_Syntax.NT ((FStar_Pervasives_Native.fst b), v1))
          :: s
  
let (set_lcomp_result :
  FStar_TypeChecker_Common.lcomp ->
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
      FStar_TypeChecker_Common.lcomp)
  =
  fun lc  ->
    fun t  ->
      FStar_TypeChecker_Common.apply_lcomp
        (fun c  -> FStar_Syntax_Util.set_result_typ c t) (fun g  -> g)
        (let uu___66_429 = lc  in
         {
           FStar_TypeChecker_Common.eff_name =
             (uu___66_429.FStar_TypeChecker_Common.eff_name);
           FStar_TypeChecker_Common.res_typ = t;
           FStar_TypeChecker_Common.cflags =
             (uu___66_429.FStar_TypeChecker_Common.cflags);
           FStar_TypeChecker_Common.comp_thunk =
             (uu___66_429.FStar_TypeChecker_Common.comp_thunk)
         })
  
let (memo_tk :
  FStar_Syntax_Syntax.term ->
    FStar_Syntax_Syntax.typ -> FStar_Syntax_Syntax.term)
  = fun e  -> fun t  -> e 
let (value_check_expected_typ :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term ->
      (FStar_Syntax_Syntax.typ,FStar_TypeChecker_Common.lcomp)
        FStar_Util.either ->
        FStar_TypeChecker_Common.guard_t ->
          (FStar_Syntax_Syntax.term * FStar_TypeChecker_Common.lcomp *
            FStar_TypeChecker_Common.guard_t))
  =
  fun env  ->
    fun e  ->
      fun tlc  ->
        fun guard  ->
          FStar_TypeChecker_Env.def_check_guard_wf e.FStar_Syntax_Syntax.pos
            "value_check_expected_typ" env guard;
          (let lc =
             match tlc with
             | FStar_Util.Inl t ->
                 let uu____486 = FStar_Syntax_Syntax.mk_Total t  in
                 FStar_All.pipe_left FStar_TypeChecker_Common.lcomp_of_comp
                   uu____486
             | FStar_Util.Inr lc -> lc  in
           let t = lc.FStar_TypeChecker_Common.res_typ  in
           let uu____489 =
             let uu____496 = FStar_TypeChecker_Env.expected_typ env  in
             match uu____496 with
             | FStar_Pervasives_Native.None  -> ((memo_tk e t), lc, guard)
             | FStar_Pervasives_Native.Some t' ->
                 let uu____506 =
                   FStar_TypeChecker_Util.check_and_ascribe env e lc t'  in
                 (match uu____506 with
                  | (e1,lc1,g) ->
                      ((let uu____523 =
                          FStar_TypeChecker_Env.debug env
                            FStar_Options.Medium
                           in
                        if uu____523
                        then
                          let uu____526 =
                            FStar_TypeChecker_Common.lcomp_to_string lc1  in
                          let uu____528 =
                            FStar_Syntax_Print.term_to_string t'  in
                          let uu____530 =
                            FStar_TypeChecker_Rel.guard_to_string env g  in
                          let uu____532 =
                            FStar_TypeChecker_Rel.guard_to_string env guard
                             in
                          FStar_Util.print4
                            "check_and_ascribe: type is %s<:%s \tguard is %s, %s\n"
                            uu____526 uu____528 uu____530 uu____532
                        else ());
                       (let t1 = lc1.FStar_TypeChecker_Common.res_typ  in
                        let g1 = FStar_TypeChecker_Env.conj_guard g guard  in
                        let uu____539 =
                          let uu____544 =
                            ((FStar_All.pipe_right tlc FStar_Util.is_left) &&
                               (FStar_TypeChecker_Util.should_return env
                                  (FStar_Pervasives_Native.Some e1) lc1))
                              && (FStar_TypeChecker_Common.is_pure_lcomp lc1)
                             in
                          if uu____544
                          then
                            let uu____556 =
                              FStar_TypeChecker_Util.lcomp_univ_opt lc1  in
                            match uu____556 with
                            | (u_opt,g_lc) ->
                                let uu____573 =
                                  let uu____574 =
                                    FStar_TypeChecker_Util.return_value env
                                      u_opt t1 e1
                                     in
                                  FStar_All.pipe_right uu____574
                                    FStar_TypeChecker_Common.lcomp_of_comp
                                   in
                                let uu____575 =
                                  FStar_TypeChecker_Env.conj_guard g1 g_lc
                                   in
                                (uu____573, uu____575)
                          else (lc1, g1)  in
                        match uu____539 with
                        | (lc2,g2) ->
                            let msg =
                              let uu____593 =
                                FStar_TypeChecker_Env.is_trivial_guard_formula
                                  g2
                                 in
                              if uu____593
                              then FStar_Pervasives_Native.None
                              else
                                FStar_All.pipe_left
                                  (fun _622  ->
                                     FStar_Pervasives_Native.Some _622)
                                  (FStar_TypeChecker_Err.subtyping_failed env
                                     t1 t')
                               in
                            let uu____623 =
                              FStar_TypeChecker_Util.strengthen_precondition
                                msg env e1 lc2 g2
                               in
                            (match uu____623 with
                             | (lc3,g3) ->
                                 let uu____636 = set_lcomp_result lc3 t'  in
                                 ((memo_tk e1 t'), uu____636, g3)))))
              in
           match uu____489 with | (e1,lc1,g) -> (e1, lc1, g))
  
let (comp_check_expected_typ :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term ->
      FStar_TypeChecker_Common.lcomp ->
        (FStar_Syntax_Syntax.term * FStar_TypeChecker_Common.lcomp *
          FStar_TypeChecker_Common.guard_t))
  =
  fun env  ->
    fun e  ->
      fun lc  ->
        let uu____674 = FStar_TypeChecker_Env.expected_typ env  in
        match uu____674 with
        | FStar_Pervasives_Native.None  ->
            (e, lc, FStar_TypeChecker_Env.trivial_guard)
        | FStar_Pervasives_Native.Some t ->
            let uu____684 = FStar_TypeChecker_Util.maybe_coerce_lc env e lc t
               in
            (match uu____684 with
             | (e1,lc1,g_c) ->
                 let uu____700 =
                   FStar_TypeChecker_Util.weaken_result_typ env e1 lc1 t  in
                 (match uu____700 with
                  | (e2,lc2,g) ->
                      let uu____716 = FStar_TypeChecker_Env.conj_guard g g_c
                         in
                      (e2, lc2, uu____716)))
  
let (check_expected_effect :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.comp FStar_Pervasives_Native.option ->
      (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.comp) ->
        (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.comp *
          FStar_TypeChecker_Common.guard_t))
  =
  fun env  ->
    fun copt  ->
      fun ec  ->
        let uu____757 = ec  in
        match uu____757 with
        | (e,c) ->
            let tot_or_gtot c1 =
              let uu____780 = FStar_Syntax_Util.is_pure_comp c1  in
              if uu____780
              then
                FStar_Syntax_Syntax.mk_Total
                  (FStar_Syntax_Util.comp_result c1)
              else
                (let uu____785 = FStar_Syntax_Util.is_pure_or_ghost_comp c1
                    in
                 if uu____785
                 then
                   FStar_Syntax_Syntax.mk_GTotal
                     (FStar_Syntax_Util.comp_result c1)
                 else failwith "Impossible: Expected pure_or_ghost comp")
               in
            let uu____791 =
              let ct = FStar_Syntax_Util.comp_result c  in
              match copt with
              | FStar_Pervasives_Native.Some uu____815 ->
                  (copt, c, FStar_Pervasives_Native.None)
              | FStar_Pervasives_Native.None  ->
                  let uu____820 =
                    ((FStar_Options.ml_ish ()) &&
                       (FStar_Ident.lid_equals
                          FStar_Parser_Const.effect_ALL_lid
                          (FStar_Syntax_Util.comp_effect_name c)))
                      ||
                      (((FStar_Options.ml_ish ()) &&
                          env.FStar_TypeChecker_Env.lax)
                         &&
                         (let uu____823 =
                            FStar_Syntax_Util.is_pure_or_ghost_comp c  in
                          Prims.op_Negation uu____823))
                     in
                  if uu____820
                  then
                    let uu____836 =
                      let uu____839 =
                        FStar_Syntax_Util.ml_comp ct
                          e.FStar_Syntax_Syntax.pos
                         in
                      FStar_Pervasives_Native.Some uu____839  in
                    (uu____836, c, FStar_Pervasives_Native.None)
                  else
                    (let uu____846 = FStar_Syntax_Util.is_tot_or_gtot_comp c
                        in
                     if uu____846
                     then
                       let uu____859 = tot_or_gtot c  in
                       (FStar_Pervasives_Native.None, uu____859,
                         FStar_Pervasives_Native.None)
                     else
                       (let uu____866 =
                          FStar_Syntax_Util.is_pure_or_ghost_comp c  in
                        if uu____866
                        then
                          let uu____879 =
                            let uu____882 = tot_or_gtot c  in
                            FStar_Pervasives_Native.Some uu____882  in
                          (uu____879, c, FStar_Pervasives_Native.None)
                        else
                          (let uu____889 =
                             let uu____891 =
                               FStar_All.pipe_right
                                 (FStar_Syntax_Util.comp_effect_name c)
                                 (FStar_TypeChecker_Env.norm_eff_name env)
                                in
                             FStar_All.pipe_right uu____891
                               (FStar_TypeChecker_Env.is_layered_effect env)
                              in
                           if uu____889
                           then
                             let uu____904 =
                               let uu____910 =
                                 let uu____912 =
                                   let uu____914 =
                                     FStar_All.pipe_right c
                                       FStar_Syntax_Util.comp_effect_name
                                      in
                                   FStar_All.pipe_right uu____914
                                     FStar_Ident.string_of_lid
                                    in
                                 let uu____918 =
                                   FStar_Range.string_of_range
                                     e.FStar_Syntax_Syntax.pos
                                    in
                                 FStar_Util.format2
                                   "Missing annotation for a layered effect (%s) computation at %s"
                                   uu____912 uu____918
                                  in
                               (FStar_Errors.Fatal_IllTyped, uu____910)  in
                             FStar_Errors.raise_error uu____904
                               e.FStar_Syntax_Syntax.pos
                           else
                             (let uu____934 =
                                FStar_Options.trivial_pre_for_unannotated_effectful_fns
                                  ()
                                 in
                              if uu____934
                              then
                                let uu____947 =
                                  let uu____950 =
                                    FStar_TypeChecker_Util.check_trivial_precondition
                                      env c
                                     in
                                  match uu____950 with
                                  | (uu____959,uu____960,g) ->
                                      FStar_Pervasives_Native.Some g
                                   in
                                (FStar_Pervasives_Native.None, c, uu____947)
                              else
                                (FStar_Pervasives_Native.None, c,
                                  FStar_Pervasives_Native.None)))))
               in
            (match uu____791 with
             | (expected_c_opt,c1,gopt) ->
                 let c2 = norm_c env c1  in
                 (match expected_c_opt with
                  | FStar_Pervasives_Native.None  ->
                      (e, c2,
                        ((match gopt with
                          | FStar_Pervasives_Native.None  ->
                              FStar_TypeChecker_Env.trivial_guard
                          | FStar_Pervasives_Native.Some g -> g)))
                  | FStar_Pervasives_Native.Some expected_c ->
                      ((match gopt with
                        | FStar_Pervasives_Native.None  -> ()
                        | FStar_Pervasives_Native.Some uu____999 ->
                            failwith
                              "Impossible! check_expected_effect, gopt should have been None");
                       (let c3 =
                          let uu____1002 =
                            FStar_TypeChecker_Common.lcomp_of_comp c2  in
                          FStar_TypeChecker_Util.maybe_assume_result_eq_pure_term
                            env e uu____1002
                           in
                        let uu____1003 =
                          FStar_TypeChecker_Common.lcomp_comp c3  in
                        match uu____1003 with
                        | (c4,g_c) ->
                            ((let uu____1017 =
                                FStar_All.pipe_left
                                  (FStar_TypeChecker_Env.debug env)
                                  FStar_Options.Medium
                                 in
                              if uu____1017
                              then
                                let uu____1021 =
                                  FStar_Syntax_Print.term_to_string e  in
                                let uu____1023 =
                                  FStar_Syntax_Print.comp_to_string c4  in
                                let uu____1025 =
                                  FStar_Syntax_Print.comp_to_string
                                    expected_c
                                   in
                                FStar_Util.print3
                                  "In check_expected_effect, asking rel to solve the problem on e=(%s) and c=(%s) and expected_c=(%s)\n"
                                  uu____1021 uu____1023 uu____1025
                              else ());
                             (let uu____1030 =
                                FStar_TypeChecker_Util.check_comp env e c4
                                  expected_c
                                 in
                              match uu____1030 with
                              | (e1,uu____1044,g) ->
                                  let g1 =
                                    let uu____1047 =
                                      FStar_TypeChecker_Env.get_range env  in
                                    FStar_TypeChecker_Util.label_guard
                                      uu____1047
                                      "could not prove post-condition" g
                                     in
                                  ((let uu____1050 =
                                      FStar_TypeChecker_Env.debug env
                                        FStar_Options.Medium
                                       in
                                    if uu____1050
                                    then
                                      let uu____1053 =
                                        FStar_Range.string_of_range
                                          e1.FStar_Syntax_Syntax.pos
                                         in
                                      let uu____1055 =
                                        FStar_TypeChecker_Rel.guard_to_string
                                          env g1
                                         in
                                      FStar_Util.print2
                                        "(%s) DONE check_expected_effect;\n\tguard is: %s\n"
                                        uu____1053 uu____1055
                                    else ());
                                   (let e2 =
                                      FStar_TypeChecker_Util.maybe_lift env
                                        e1
                                        (FStar_Syntax_Util.comp_effect_name
                                           c4)
                                        (FStar_Syntax_Util.comp_effect_name
                                           expected_c)
                                        (FStar_Syntax_Util.comp_result c4)
                                       in
                                    let uu____1061 =
                                      FStar_TypeChecker_Env.conj_guard g_c g1
                                       in
                                    (e2, expected_c, uu____1061)))))))))
  
let no_logical_guard :
  'Auu____1071 'Auu____1072 .
    FStar_TypeChecker_Env.env ->
      ('Auu____1071 * 'Auu____1072 * FStar_TypeChecker_Env.guard_t) ->
        ('Auu____1071 * 'Auu____1072 * FStar_TypeChecker_Env.guard_t)
  =
  fun env  ->
    fun uu____1094  ->
      match uu____1094 with
      | (te,kt,f) ->
          let uu____1104 = FStar_TypeChecker_Env.guard_form f  in
          (match uu____1104 with
           | FStar_TypeChecker_Common.Trivial  -> (te, kt, f)
           | FStar_TypeChecker_Common.NonTrivial f1 ->
               let uu____1112 =
                 FStar_TypeChecker_Err.unexpected_non_trivial_precondition_on_term
                   env f1
                  in
               let uu____1118 = FStar_TypeChecker_Env.get_range env  in
               FStar_Errors.raise_error uu____1112 uu____1118)
  
let (print_expected_ty : FStar_TypeChecker_Env.env -> unit) =
  fun env  ->
    let uu____1131 = FStar_TypeChecker_Env.expected_typ env  in
    match uu____1131 with
    | FStar_Pervasives_Native.None  ->
        FStar_Util.print_string "Expected type is None\n"
    | FStar_Pervasives_Native.Some t ->
        let uu____1136 = FStar_Syntax_Print.term_to_string t  in
        FStar_Util.print1 "Expected type is %s" uu____1136
  
let rec (get_pat_vars' :
  FStar_Syntax_Syntax.bv Prims.list ->
    Prims.bool ->
      FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.bv FStar_Util.set)
  =
  fun all  ->
    fun andlist  ->
      fun pats  ->
        let pats1 = FStar_Syntax_Util.unmeta pats  in
        let uu____1166 = FStar_Syntax_Util.head_and_args pats1  in
        match uu____1166 with
        | (head1,args) ->
            let uu____1211 =
              let uu____1226 =
                let uu____1227 = FStar_Syntax_Util.un_uinst head1  in
                uu____1227.FStar_Syntax_Syntax.n  in
              (uu____1226, args)  in
            (match uu____1211 with
             | (FStar_Syntax_Syntax.Tm_fvar fv,uu____1243) when
                 FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.nil_lid
                 ->
                 if andlist
                 then FStar_Util.as_set all FStar_Syntax_Syntax.order_bv
                 else FStar_Util.new_set FStar_Syntax_Syntax.order_bv
             | (FStar_Syntax_Syntax.Tm_fvar
                fv,(uu____1270,FStar_Pervasives_Native.Some
                    (FStar_Syntax_Syntax.Implicit uu____1271))::(hd1,FStar_Pervasives_Native.None
                                                                 )::(tl1,FStar_Pervasives_Native.None
                                                                    )::[])
                 when
                 FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.cons_lid
                 ->
                 let hdvs = get_pat_vars' all false hd1  in
                 let tlvs = get_pat_vars' all andlist tl1  in
                 if andlist
                 then FStar_Util.set_intersect hdvs tlvs
                 else FStar_Util.set_union hdvs tlvs
             | (FStar_Syntax_Syntax.Tm_fvar
                fv,(uu____1348,FStar_Pervasives_Native.Some
                    (FStar_Syntax_Syntax.Implicit uu____1349))::(pat,FStar_Pervasives_Native.None
                                                                 )::[])
                 when
                 FStar_Syntax_Syntax.fv_eq_lid fv
                   FStar_Parser_Const.smtpat_lid
                 -> FStar_Syntax_Free.names pat
             | (FStar_Syntax_Syntax.Tm_fvar
                fv,(subpats,FStar_Pervasives_Native.None )::[]) when
                 FStar_Syntax_Syntax.fv_eq_lid fv
                   FStar_Parser_Const.smtpatOr_lid
                 -> get_pat_vars' all true subpats
             | uu____1433 -> FStar_Util.new_set FStar_Syntax_Syntax.order_bv)
  
let (get_pat_vars :
  FStar_Syntax_Syntax.bv Prims.list ->
    FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.bv FStar_Util.set)
  = fun all  -> fun pats  -> get_pat_vars' all false pats 
let check_pat_fvs :
  'Auu____1477 .
    FStar_Range.range ->
      FStar_TypeChecker_Env.env ->
        FStar_Syntax_Syntax.term ->
          (FStar_Syntax_Syntax.bv * 'Auu____1477) Prims.list -> unit
  =
  fun rng  ->
    fun env  ->
      fun pats  ->
        fun bs  ->
          let pat_vars =
            let uu____1513 = FStar_List.map FStar_Pervasives_Native.fst bs
               in
            let uu____1520 =
              FStar_TypeChecker_Normalize.normalize
                [FStar_TypeChecker_Env.Beta] env pats
               in
            get_pat_vars uu____1513 uu____1520  in
          let uu____1521 =
            FStar_All.pipe_right bs
              (FStar_Util.find_opt
                 (fun uu____1548  ->
                    match uu____1548 with
                    | (b,uu____1555) ->
                        let uu____1556 = FStar_Util.set_mem b pat_vars  in
                        Prims.op_Negation uu____1556))
             in
          match uu____1521 with
          | FStar_Pervasives_Native.None  -> ()
          | FStar_Pervasives_Native.Some (x,uu____1563) ->
              let uu____1568 =
                let uu____1574 =
                  let uu____1576 = FStar_Syntax_Print.bv_to_string x  in
                  FStar_Util.format1
                    "Pattern misses at least one bound variable: %s"
                    uu____1576
                   in
                (FStar_Errors.Warning_SMTPatternIllFormed, uu____1574)  in
              FStar_Errors.log_issue rng uu____1568
  
let (check_no_smt_theory_symbols :
  FStar_TypeChecker_Env.env -> FStar_Syntax_Syntax.term -> unit) =
  fun en  ->
    fun t  ->
      let rec pat_terms t1 =
        let t2 = FStar_Syntax_Util.unmeta t1  in
        let uu____1602 = FStar_Syntax_Util.head_and_args t2  in
        match uu____1602 with
        | (head1,args) ->
            let uu____1647 =
              let uu____1662 =
                let uu____1663 = FStar_Syntax_Util.un_uinst head1  in
                uu____1663.FStar_Syntax_Syntax.n  in
              (uu____1662, args)  in
            (match uu____1647 with
             | (FStar_Syntax_Syntax.Tm_fvar fv,uu____1679) when
                 FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.nil_lid
                 -> []
             | (FStar_Syntax_Syntax.Tm_fvar
                fv,uu____1701::(hd1,uu____1703)::(tl1,uu____1705)::[]) when
                 FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.cons_lid
                 ->
                 let uu____1772 = pat_terms hd1  in
                 let uu____1775 = pat_terms tl1  in
                 FStar_List.append uu____1772 uu____1775
             | (FStar_Syntax_Syntax.Tm_fvar
                fv,uu____1779::(pat,uu____1781)::[]) when
                 FStar_Syntax_Syntax.fv_eq_lid fv
                   FStar_Parser_Const.smtpat_lid
                 -> [pat]
             | (FStar_Syntax_Syntax.Tm_fvar
                fv,(subpats,FStar_Pervasives_Native.None )::[]) when
                 FStar_Syntax_Syntax.fv_eq_lid fv
                   FStar_Parser_Const.smtpatOr_lid
                 -> pat_terms subpats
             | uu____1866 -> [])
         in
      let rec aux t1 =
        let uu____1891 =
          let uu____1892 = FStar_Syntax_Subst.compress t1  in
          uu____1892.FStar_Syntax_Syntax.n  in
        match uu____1891 with
        | FStar_Syntax_Syntax.Tm_bvar uu____1897 -> []
        | FStar_Syntax_Syntax.Tm_name uu____1898 -> []
        | FStar_Syntax_Syntax.Tm_type uu____1899 -> []
        | FStar_Syntax_Syntax.Tm_uvar uu____1900 -> []
        | FStar_Syntax_Syntax.Tm_lazy uu____1913 -> []
        | FStar_Syntax_Syntax.Tm_unknown  -> []
        | FStar_Syntax_Syntax.Tm_constant uu____1914 -> [t1]
        | FStar_Syntax_Syntax.Tm_abs uu____1915 -> [t1]
        | FStar_Syntax_Syntax.Tm_arrow uu____1934 -> [t1]
        | FStar_Syntax_Syntax.Tm_refine uu____1949 -> [t1]
        | FStar_Syntax_Syntax.Tm_match uu____1956 -> [t1]
        | FStar_Syntax_Syntax.Tm_let uu____1979 -> [t1]
        | FStar_Syntax_Syntax.Tm_delayed uu____1993 -> [t1]
        | FStar_Syntax_Syntax.Tm_quoted uu____2016 -> [t1]
        | FStar_Syntax_Syntax.Tm_fvar fv ->
            let uu____2024 =
              FStar_TypeChecker_Env.fv_has_attr en fv
                FStar_Parser_Const.smt_theory_symbol_attr_lid
               in
            if uu____2024 then [t1] else []
        | FStar_Syntax_Syntax.Tm_app (t2,args) ->
            let uu____2057 = aux t2  in
            FStar_List.fold_left
              (fun acc  ->
                 fun uu____2074  ->
                   match uu____2074 with
                   | (t3,uu____2086) ->
                       let uu____2091 = aux t3  in
                       FStar_List.append acc uu____2091) uu____2057 args
        | FStar_Syntax_Syntax.Tm_ascribed (t2,uu____2095,uu____2096) ->
            aux t2
        | FStar_Syntax_Syntax.Tm_uinst (t2,uu____2138) -> aux t2
        | FStar_Syntax_Syntax.Tm_meta (t2,uu____2144) -> aux t2  in
      let tlist =
        let uu____2152 = FStar_All.pipe_right t pat_terms  in
        FStar_All.pipe_right uu____2152 (FStar_List.collect aux)  in
      if (FStar_List.length tlist) = Prims.int_zero
      then ()
      else
        (let msg =
           FStar_List.fold_left
             (fun s  ->
                fun t1  ->
                  let uu____2175 =
                    let uu____2177 = FStar_Syntax_Print.term_to_string t1  in
                    Prims.op_Hat " " uu____2177  in
                  Prims.op_Hat s uu____2175) "" tlist
            in
         let uu____2181 =
           let uu____2187 =
             FStar_Util.format1
               "Pattern uses these theory symbols or terms that should not be in an smt pattern: %s"
               msg
              in
           (FStar_Errors.Warning_SMTPatternIllFormed, uu____2187)  in
         FStar_Errors.log_issue t.FStar_Syntax_Syntax.pos uu____2181)
  
let check_smt_pat :
  'Auu____2202 .
    FStar_TypeChecker_Env.env ->
      FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
        (FStar_Syntax_Syntax.bv * 'Auu____2202) Prims.list ->
          FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax -> unit
  =
  fun env  ->
    fun t  ->
      fun bs  ->
        fun c  ->
          let uu____2243 = FStar_Syntax_Util.is_smt_lemma t  in
          if uu____2243
          then
            match c.FStar_Syntax_Syntax.n with
            | FStar_Syntax_Syntax.Comp
                { FStar_Syntax_Syntax.comp_univs = uu____2246;
                  FStar_Syntax_Syntax.effect_name = uu____2247;
                  FStar_Syntax_Syntax.result_typ = uu____2248;
                  FStar_Syntax_Syntax.effect_args =
                    _pre::_post::(pats,uu____2252)::[];
                  FStar_Syntax_Syntax.flags = uu____2253;_}
                ->
                (check_pat_fvs t.FStar_Syntax_Syntax.pos env pats bs;
                 check_no_smt_theory_symbols env pats)
            | uu____2315 -> failwith "Impossible"
          else ()
  
let (guard_letrecs :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.binders ->
      FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax ->
        (FStar_Syntax_Syntax.lbname * FStar_Syntax_Syntax.typ *
          FStar_Syntax_Syntax.univ_names) Prims.list)
  =
  fun env  ->
    fun actuals  ->
      fun expected_c  ->
        match env.FStar_TypeChecker_Env.letrecs with
        | [] -> []
        | letrecs ->
            let r = FStar_TypeChecker_Env.get_range env  in
            let env1 =
              let uu___373_2378 = env  in
              {
                FStar_TypeChecker_Env.solver =
                  (uu___373_2378.FStar_TypeChecker_Env.solver);
                FStar_TypeChecker_Env.range =
                  (uu___373_2378.FStar_TypeChecker_Env.range);
                FStar_TypeChecker_Env.curmodule =
                  (uu___373_2378.FStar_TypeChecker_Env.curmodule);
                FStar_TypeChecker_Env.gamma =
                  (uu___373_2378.FStar_TypeChecker_Env.gamma);
                FStar_TypeChecker_Env.gamma_sig =
                  (uu___373_2378.FStar_TypeChecker_Env.gamma_sig);
                FStar_TypeChecker_Env.gamma_cache =
                  (uu___373_2378.FStar_TypeChecker_Env.gamma_cache);
                FStar_TypeChecker_Env.modules =
                  (uu___373_2378.FStar_TypeChecker_Env.modules);
                FStar_TypeChecker_Env.expected_typ =
                  (uu___373_2378.FStar_TypeChecker_Env.expected_typ);
                FStar_TypeChecker_Env.sigtab =
                  (uu___373_2378.FStar_TypeChecker_Env.sigtab);
                FStar_TypeChecker_Env.attrtab =
                  (uu___373_2378.FStar_TypeChecker_Env.attrtab);
                FStar_TypeChecker_Env.instantiate_imp =
                  (uu___373_2378.FStar_TypeChecker_Env.instantiate_imp);
                FStar_TypeChecker_Env.effects =
                  (uu___373_2378.FStar_TypeChecker_Env.effects);
                FStar_TypeChecker_Env.generalize =
                  (uu___373_2378.FStar_TypeChecker_Env.generalize);
                FStar_TypeChecker_Env.letrecs = [];
                FStar_TypeChecker_Env.top_level =
                  (uu___373_2378.FStar_TypeChecker_Env.top_level);
                FStar_TypeChecker_Env.check_uvars =
                  (uu___373_2378.FStar_TypeChecker_Env.check_uvars);
                FStar_TypeChecker_Env.use_eq =
                  (uu___373_2378.FStar_TypeChecker_Env.use_eq);
                FStar_TypeChecker_Env.is_iface =
                  (uu___373_2378.FStar_TypeChecker_Env.is_iface);
                FStar_TypeChecker_Env.admit =
                  (uu___373_2378.FStar_TypeChecker_Env.admit);
                FStar_TypeChecker_Env.lax =
                  (uu___373_2378.FStar_TypeChecker_Env.lax);
                FStar_TypeChecker_Env.lax_universes =
                  (uu___373_2378.FStar_TypeChecker_Env.lax_universes);
                FStar_TypeChecker_Env.phase1 =
                  (uu___373_2378.FStar_TypeChecker_Env.phase1);
                FStar_TypeChecker_Env.failhard =
                  (uu___373_2378.FStar_TypeChecker_Env.failhard);
                FStar_TypeChecker_Env.nosynth =
                  (uu___373_2378.FStar_TypeChecker_Env.nosynth);
                FStar_TypeChecker_Env.uvar_subtyping =
                  (uu___373_2378.FStar_TypeChecker_Env.uvar_subtyping);
                FStar_TypeChecker_Env.tc_term =
                  (uu___373_2378.FStar_TypeChecker_Env.tc_term);
                FStar_TypeChecker_Env.type_of =
                  (uu___373_2378.FStar_TypeChecker_Env.type_of);
                FStar_TypeChecker_Env.universe_of =
                  (uu___373_2378.FStar_TypeChecker_Env.universe_of);
                FStar_TypeChecker_Env.check_type_of =
                  (uu___373_2378.FStar_TypeChecker_Env.check_type_of);
                FStar_TypeChecker_Env.use_bv_sorts =
                  (uu___373_2378.FStar_TypeChecker_Env.use_bv_sorts);
                FStar_TypeChecker_Env.qtbl_name_and_index =
                  (uu___373_2378.FStar_TypeChecker_Env.qtbl_name_and_index);
                FStar_TypeChecker_Env.normalized_eff_names =
                  (uu___373_2378.FStar_TypeChecker_Env.normalized_eff_names);
                FStar_TypeChecker_Env.fv_delta_depths =
                  (uu___373_2378.FStar_TypeChecker_Env.fv_delta_depths);
                FStar_TypeChecker_Env.proof_ns =
                  (uu___373_2378.FStar_TypeChecker_Env.proof_ns);
                FStar_TypeChecker_Env.synth_hook =
                  (uu___373_2378.FStar_TypeChecker_Env.synth_hook);
                FStar_TypeChecker_Env.splice =
                  (uu___373_2378.FStar_TypeChecker_Env.splice);
                FStar_TypeChecker_Env.mpreprocess =
                  (uu___373_2378.FStar_TypeChecker_Env.mpreprocess);
                FStar_TypeChecker_Env.postprocess =
                  (uu___373_2378.FStar_TypeChecker_Env.postprocess);
                FStar_TypeChecker_Env.is_native_tactic =
                  (uu___373_2378.FStar_TypeChecker_Env.is_native_tactic);
                FStar_TypeChecker_Env.identifier_info =
                  (uu___373_2378.FStar_TypeChecker_Env.identifier_info);
                FStar_TypeChecker_Env.tc_hooks =
                  (uu___373_2378.FStar_TypeChecker_Env.tc_hooks);
                FStar_TypeChecker_Env.dsenv =
                  (uu___373_2378.FStar_TypeChecker_Env.dsenv);
                FStar_TypeChecker_Env.nbe =
                  (uu___373_2378.FStar_TypeChecker_Env.nbe);
                FStar_TypeChecker_Env.strict_args_tab =
                  (uu___373_2378.FStar_TypeChecker_Env.strict_args_tab);
                FStar_TypeChecker_Env.erasable_types_tab =
                  (uu___373_2378.FStar_TypeChecker_Env.erasable_types_tab)
              }  in
            let precedes =
              FStar_TypeChecker_Util.fvar_const env1
                FStar_Parser_Const.precedes_lid
               in
            let decreases_clause bs c =
              (let uu____2404 =
                 FStar_TypeChecker_Env.debug env1 FStar_Options.Low  in
               if uu____2404
               then
                 let uu____2407 =
                   FStar_Syntax_Print.binders_to_string ", " bs  in
                 let uu____2410 = FStar_Syntax_Print.comp_to_string c  in
                 FStar_Util.print2
                   "Building a decreases clause over (%s) and %s\n"
                   uu____2407 uu____2410
               else ());
              (let filter_types_and_functions bs1 =
                 FStar_All.pipe_right bs1
                   (FStar_List.collect
                      (fun uu____2444  ->
                         match uu____2444 with
                         | (b,uu____2454) ->
                             let t =
                               let uu____2460 =
                                 FStar_Syntax_Util.unrefine
                                   b.FStar_Syntax_Syntax.sort
                                  in
                               FStar_TypeChecker_Normalize.unfold_whnf env1
                                 uu____2460
                                in
                             (match t.FStar_Syntax_Syntax.n with
                              | FStar_Syntax_Syntax.Tm_type uu____2463 -> []
                              | FStar_Syntax_Syntax.Tm_arrow uu____2464 -> []
                              | uu____2479 ->
                                  let uu____2480 =
                                    FStar_Syntax_Syntax.bv_to_name b  in
                                  [uu____2480])))
                  in
               let as_lex_list dec =
                 let uu____2493 = FStar_Syntax_Util.head_and_args dec  in
                 match uu____2493 with
                 | (head1,uu____2513) ->
                     (match head1.FStar_Syntax_Syntax.n with
                      | FStar_Syntax_Syntax.Tm_fvar fv when
                          FStar_Syntax_Syntax.fv_eq_lid fv
                            FStar_Parser_Const.lexcons_lid
                          -> dec
                      | uu____2541 -> mk_lex_list [dec])
                  in
               let cflags = FStar_Syntax_Util.comp_flags c  in
               let uu____2549 =
                 FStar_All.pipe_right cflags
                   (FStar_List.tryFind
                      (fun uu___1_2558  ->
                         match uu___1_2558 with
                         | FStar_Syntax_Syntax.DECREASES uu____2560 -> true
                         | uu____2564 -> false))
                  in
               match uu____2549 with
               | FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.DECREASES
                   dec) -> as_lex_list dec
               | uu____2571 ->
                   let xs =
                     FStar_All.pipe_right bs filter_types_and_functions  in
                   (match xs with | x::[] -> x | uu____2592 -> mk_lex_list xs))
               in
            let previous_dec = decreases_clause actuals expected_c  in
            let guard_one_letrec uu____2621 =
              match uu____2621 with
              | (l,t,u_names) ->
                  let uu____2645 =
                    let uu____2646 = FStar_Syntax_Subst.compress t  in
                    uu____2646.FStar_Syntax_Syntax.n  in
                  (match uu____2645 with
                   | FStar_Syntax_Syntax.Tm_arrow (formals,c) ->
                       let formals1 =
                         FStar_All.pipe_right formals
                           (FStar_List.map
                              (fun uu____2705  ->
                                 match uu____2705 with
                                 | (x,imp) ->
                                     let uu____2724 =
                                       FStar_Syntax_Syntax.is_null_bv x  in
                                     if uu____2724
                                     then
                                       let uu____2733 =
                                         let uu____2734 =
                                           let uu____2737 =
                                             FStar_Syntax_Syntax.range_of_bv
                                               x
                                              in
                                           FStar_Pervasives_Native.Some
                                             uu____2737
                                            in
                                         FStar_Syntax_Syntax.new_bv
                                           uu____2734
                                           x.FStar_Syntax_Syntax.sort
                                          in
                                       (uu____2733, imp)
                                     else (x, imp)))
                          in
                       let uu____2744 =
                         FStar_Syntax_Subst.open_comp formals1 c  in
                       (match uu____2744 with
                        | (formals2,c1) ->
                            let dec = decreases_clause formals2 c1  in
                            let precedes1 =
                              let uu____2765 =
                                let uu____2770 =
                                  let uu____2771 =
                                    FStar_Syntax_Syntax.as_arg dec  in
                                  let uu____2780 =
                                    let uu____2791 =
                                      FStar_Syntax_Syntax.as_arg previous_dec
                                       in
                                    [uu____2791]  in
                                  uu____2771 :: uu____2780  in
                                FStar_Syntax_Syntax.mk_Tm_app precedes
                                  uu____2770
                                 in
                              uu____2765 FStar_Pervasives_Native.None r  in
                            let precedes2 =
                              FStar_TypeChecker_Util.label
                                "Could not prove termination of this recursive call"
                                r precedes1
                               in
                            let uu____2826 = FStar_Util.prefix formals2  in
                            (match uu____2826 with
                             | (bs,(last1,imp)) ->
                                 let last2 =
                                   let uu___440_2889 = last1  in
                                   let uu____2890 =
                                     FStar_Syntax_Util.refine last1 precedes2
                                      in
                                   {
                                     FStar_Syntax_Syntax.ppname =
                                       (uu___440_2889.FStar_Syntax_Syntax.ppname);
                                     FStar_Syntax_Syntax.index =
                                       (uu___440_2889.FStar_Syntax_Syntax.index);
                                     FStar_Syntax_Syntax.sort = uu____2890
                                   }  in
                                 let refined_formals =
                                   FStar_List.append bs [(last2, imp)]  in
                                 let t' =
                                   FStar_Syntax_Util.arrow refined_formals c1
                                    in
                                 ((let uu____2926 =
                                     FStar_TypeChecker_Env.debug env1
                                       FStar_Options.Medium
                                      in
                                   if uu____2926
                                   then
                                     let uu____2929 =
                                       FStar_Syntax_Print.lbname_to_string l
                                        in
                                     let uu____2931 =
                                       FStar_Syntax_Print.term_to_string t
                                        in
                                     let uu____2933 =
                                       FStar_Syntax_Print.term_to_string t'
                                        in
                                     FStar_Util.print3
                                       "Refined let rec %s\n\tfrom type %s\n\tto type %s\n"
                                       uu____2929 uu____2931 uu____2933
                                   else ());
                                  (l, t', u_names))))
                   | uu____2940 ->
                       FStar_Errors.raise_error
                         (FStar_Errors.Fatal_ExpectedArrowAnnotatedType,
                           "Annotated type of 'let rec' must be an arrow")
                         t.FStar_Syntax_Syntax.pos)
               in
            FStar_All.pipe_right letrecs (FStar_List.map guard_one_letrec)
  
let (wrap_guard_with_tactic_opt :
  FStar_Syntax_Syntax.term FStar_Pervasives_Native.option ->
    FStar_TypeChecker_Env.guard_t -> FStar_TypeChecker_Env.guard_t)
  =
  fun topt  ->
    fun g  ->
      match topt with
      | FStar_Pervasives_Native.None  -> g
      | FStar_Pervasives_Native.Some tactic ->
          FStar_TypeChecker_Env.always_map_guard g
            (fun g1  ->
               let uu____3004 =
                 FStar_Syntax_Util.mk_squash FStar_Syntax_Syntax.U_zero g1
                  in
               FStar_TypeChecker_Common.mk_by_tactic tactic uu____3004)
  
let (is_comp_ascribed_reflect :
  FStar_Syntax_Syntax.term ->
    (FStar_Ident.lident * FStar_Syntax_Syntax.term *
      FStar_Syntax_Syntax.aqual) FStar_Pervasives_Native.option)
  =
  fun e  ->
    let uu____3027 =
      let uu____3028 = FStar_Syntax_Subst.compress e  in
      uu____3028.FStar_Syntax_Syntax.n  in
    match uu____3027 with
    | FStar_Syntax_Syntax.Tm_ascribed
        (e1,(FStar_Util.Inr uu____3040,uu____3041),uu____3042) ->
        let uu____3089 =
          let uu____3090 = FStar_Syntax_Subst.compress e1  in
          uu____3090.FStar_Syntax_Syntax.n  in
        (match uu____3089 with
         | FStar_Syntax_Syntax.Tm_app (head1,args) when
             (FStar_List.length args) = Prims.int_one ->
             let uu____3137 =
               let uu____3138 = FStar_Syntax_Subst.compress head1  in
               uu____3138.FStar_Syntax_Syntax.n  in
             (match uu____3137 with
              | FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_reflect l)
                  ->
                  let uu____3150 =
                    let uu____3157 = FStar_All.pipe_right args FStar_List.hd
                       in
                    FStar_All.pipe_right uu____3157
                      (fun uu____3213  ->
                         match uu____3213 with | (e2,aqual) -> (l, e2, aqual))
                     in
                  FStar_All.pipe_right uu____3150
                    (fun _3266  -> FStar_Pervasives_Native.Some _3266)
              | uu____3267 -> FStar_Pervasives_Native.None)
         | uu____3274 -> FStar_Pervasives_Native.None)
    | uu____3281 -> FStar_Pervasives_Native.None
  
let rec (tc_term :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term ->
      (FStar_Syntax_Syntax.term * FStar_TypeChecker_Common.lcomp *
        FStar_TypeChecker_Common.guard_t))
  =
  fun env  ->
    fun e  ->
      (let uu____3918 = FStar_TypeChecker_Env.debug env FStar_Options.Medium
          in
       if uu____3918
       then
         let uu____3921 =
           let uu____3923 = FStar_TypeChecker_Env.get_range env  in
           FStar_All.pipe_left FStar_Range.string_of_range uu____3923  in
         let uu____3925 =
           FStar_Util.string_of_bool env.FStar_TypeChecker_Env.phase1  in
         let uu____3927 = FStar_Syntax_Print.term_to_string e  in
         let uu____3929 =
           let uu____3931 = FStar_Syntax_Subst.compress e  in
           FStar_Syntax_Print.tag_of_term uu____3931  in
         let uu____3932 =
           let uu____3934 = FStar_TypeChecker_Env.expected_typ env  in
           match uu____3934 with
           | FStar_Pervasives_Native.None  -> "None"
           | FStar_Pervasives_Native.Some t ->
               FStar_Syntax_Print.term_to_string t
            in
         FStar_Util.print5
           "(%s) Starting tc_term (phase1=%s) of %s (%s) with expected type: %s {\n"
           uu____3921 uu____3925 uu____3927 uu____3929 uu____3932
       else ());
      (let uu____3943 =
         FStar_Util.record_time
           (fun uu____3962  ->
              tc_maybe_toplevel_term
                (let uu___484_3965 = env  in
                 {
                   FStar_TypeChecker_Env.solver =
                     (uu___484_3965.FStar_TypeChecker_Env.solver);
                   FStar_TypeChecker_Env.range =
                     (uu___484_3965.FStar_TypeChecker_Env.range);
                   FStar_TypeChecker_Env.curmodule =
                     (uu___484_3965.FStar_TypeChecker_Env.curmodule);
                   FStar_TypeChecker_Env.gamma =
                     (uu___484_3965.FStar_TypeChecker_Env.gamma);
                   FStar_TypeChecker_Env.gamma_sig =
                     (uu___484_3965.FStar_TypeChecker_Env.gamma_sig);
                   FStar_TypeChecker_Env.gamma_cache =
                     (uu___484_3965.FStar_TypeChecker_Env.gamma_cache);
                   FStar_TypeChecker_Env.modules =
                     (uu___484_3965.FStar_TypeChecker_Env.modules);
                   FStar_TypeChecker_Env.expected_typ =
                     (uu___484_3965.FStar_TypeChecker_Env.expected_typ);
                   FStar_TypeChecker_Env.sigtab =
                     (uu___484_3965.FStar_TypeChecker_Env.sigtab);
                   FStar_TypeChecker_Env.attrtab =
                     (uu___484_3965.FStar_TypeChecker_Env.attrtab);
                   FStar_TypeChecker_Env.instantiate_imp =
                     (uu___484_3965.FStar_TypeChecker_Env.instantiate_imp);
                   FStar_TypeChecker_Env.effects =
                     (uu___484_3965.FStar_TypeChecker_Env.effects);
                   FStar_TypeChecker_Env.generalize =
                     (uu___484_3965.FStar_TypeChecker_Env.generalize);
                   FStar_TypeChecker_Env.letrecs =
                     (uu___484_3965.FStar_TypeChecker_Env.letrecs);
                   FStar_TypeChecker_Env.top_level = false;
                   FStar_TypeChecker_Env.check_uvars =
                     (uu___484_3965.FStar_TypeChecker_Env.check_uvars);
                   FStar_TypeChecker_Env.use_eq =
                     (uu___484_3965.FStar_TypeChecker_Env.use_eq);
                   FStar_TypeChecker_Env.is_iface =
                     (uu___484_3965.FStar_TypeChecker_Env.is_iface);
                   FStar_TypeChecker_Env.admit =
                     (uu___484_3965.FStar_TypeChecker_Env.admit);
                   FStar_TypeChecker_Env.lax =
                     (uu___484_3965.FStar_TypeChecker_Env.lax);
                   FStar_TypeChecker_Env.lax_universes =
                     (uu___484_3965.FStar_TypeChecker_Env.lax_universes);
                   FStar_TypeChecker_Env.phase1 =
                     (uu___484_3965.FStar_TypeChecker_Env.phase1);
                   FStar_TypeChecker_Env.failhard =
                     (uu___484_3965.FStar_TypeChecker_Env.failhard);
                   FStar_TypeChecker_Env.nosynth =
                     (uu___484_3965.FStar_TypeChecker_Env.nosynth);
                   FStar_TypeChecker_Env.uvar_subtyping =
                     (uu___484_3965.FStar_TypeChecker_Env.uvar_subtyping);
                   FStar_TypeChecker_Env.tc_term =
                     (uu___484_3965.FStar_TypeChecker_Env.tc_term);
                   FStar_TypeChecker_Env.type_of =
                     (uu___484_3965.FStar_TypeChecker_Env.type_of);
                   FStar_TypeChecker_Env.universe_of =
                     (uu___484_3965.FStar_TypeChecker_Env.universe_of);
                   FStar_TypeChecker_Env.check_type_of =
                     (uu___484_3965.FStar_TypeChecker_Env.check_type_of);
                   FStar_TypeChecker_Env.use_bv_sorts =
                     (uu___484_3965.FStar_TypeChecker_Env.use_bv_sorts);
                   FStar_TypeChecker_Env.qtbl_name_and_index =
                     (uu___484_3965.FStar_TypeChecker_Env.qtbl_name_and_index);
                   FStar_TypeChecker_Env.normalized_eff_names =
                     (uu___484_3965.FStar_TypeChecker_Env.normalized_eff_names);
                   FStar_TypeChecker_Env.fv_delta_depths =
                     (uu___484_3965.FStar_TypeChecker_Env.fv_delta_depths);
                   FStar_TypeChecker_Env.proof_ns =
                     (uu___484_3965.FStar_TypeChecker_Env.proof_ns);
                   FStar_TypeChecker_Env.synth_hook =
                     (uu___484_3965.FStar_TypeChecker_Env.synth_hook);
                   FStar_TypeChecker_Env.splice =
                     (uu___484_3965.FStar_TypeChecker_Env.splice);
                   FStar_TypeChecker_Env.mpreprocess =
                     (uu___484_3965.FStar_TypeChecker_Env.mpreprocess);
                   FStar_TypeChecker_Env.postprocess =
                     (uu___484_3965.FStar_TypeChecker_Env.postprocess);
                   FStar_TypeChecker_Env.is_native_tactic =
                     (uu___484_3965.FStar_TypeChecker_Env.is_native_tactic);
                   FStar_TypeChecker_Env.identifier_info =
                     (uu___484_3965.FStar_TypeChecker_Env.identifier_info);
                   FStar_TypeChecker_Env.tc_hooks =
                     (uu___484_3965.FStar_TypeChecker_Env.tc_hooks);
                   FStar_TypeChecker_Env.dsenv =
                     (uu___484_3965.FStar_TypeChecker_Env.dsenv);
                   FStar_TypeChecker_Env.nbe =
                     (uu___484_3965.FStar_TypeChecker_Env.nbe);
                   FStar_TypeChecker_Env.strict_args_tab =
                     (uu___484_3965.FStar_TypeChecker_Env.strict_args_tab);
                   FStar_TypeChecker_Env.erasable_types_tab =
                     (uu___484_3965.FStar_TypeChecker_Env.erasable_types_tab)
                 }) e)
          in
       match uu____3943 with
       | (r,ms) ->
           ((let uu____3990 =
               FStar_TypeChecker_Env.debug env FStar_Options.Medium  in
             if uu____3990
             then
               ((let uu____3994 =
                   let uu____3996 = FStar_TypeChecker_Env.get_range env  in
                   FStar_All.pipe_left FStar_Range.string_of_range uu____3996
                    in
                 let uu____3998 = FStar_Syntax_Print.term_to_string e  in
                 let uu____4000 =
                   let uu____4002 = FStar_Syntax_Subst.compress e  in
                   FStar_Syntax_Print.tag_of_term uu____4002  in
                 let uu____4003 = FStar_Util.string_of_int ms  in
                 FStar_Util.print4 "(%s) } tc_term of %s (%s) took %sms\n"
                   uu____3994 uu____3998 uu____4000 uu____4003);
                (let uu____4006 = r  in
                 match uu____4006 with
                 | (e1,lc,uu____4015) ->
                     let uu____4016 =
                       let uu____4018 = FStar_TypeChecker_Env.get_range env
                          in
                       FStar_All.pipe_left FStar_Range.string_of_range
                         uu____4018
                        in
                     let uu____4020 = FStar_Syntax_Print.term_to_string e1
                        in
                     let uu____4022 =
                       FStar_TypeChecker_Common.lcomp_to_string lc  in
                     let uu____4024 =
                       let uu____4026 = FStar_Syntax_Subst.compress e1  in
                       FStar_Syntax_Print.tag_of_term uu____4026  in
                     FStar_Util.print4 "(%s) Result is: (%s:%s) (%s)\n"
                       uu____4016 uu____4020 uu____4022 uu____4024))
             else ());
            r))

and (tc_maybe_toplevel_term :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term ->
      (FStar_Syntax_Syntax.term * FStar_TypeChecker_Common.lcomp *
        FStar_TypeChecker_Common.guard_t))
  =
  fun env  ->
    fun e  ->
      let env1 =
        if e.FStar_Syntax_Syntax.pos = FStar_Range.dummyRange
        then env
        else FStar_TypeChecker_Env.set_range env e.FStar_Syntax_Syntax.pos
         in
      let top = FStar_Syntax_Subst.compress e  in
      (let uu____4044 = FStar_TypeChecker_Env.debug env1 FStar_Options.Medium
          in
       if uu____4044
       then
         let uu____4047 =
           let uu____4049 = FStar_TypeChecker_Env.get_range env1  in
           FStar_All.pipe_left FStar_Range.string_of_range uu____4049  in
         let uu____4051 = FStar_Syntax_Print.tag_of_term top  in
         let uu____4053 = FStar_Syntax_Print.term_to_string top  in
         FStar_Util.print3 "Typechecking %s (%s): %s\n" uu____4047 uu____4051
           uu____4053
       else ());
      (match top.FStar_Syntax_Syntax.n with
       | FStar_Syntax_Syntax.Tm_delayed uu____4064 -> failwith "Impossible"
       | FStar_Syntax_Syntax.Tm_uinst uu____4094 -> tc_value env1 e
       | FStar_Syntax_Syntax.Tm_uvar uu____4101 -> tc_value env1 e
       | FStar_Syntax_Syntax.Tm_bvar uu____4114 -> tc_value env1 e
       | FStar_Syntax_Syntax.Tm_name uu____4115 -> tc_value env1 e
       | FStar_Syntax_Syntax.Tm_fvar uu____4116 -> tc_value env1 e
       | FStar_Syntax_Syntax.Tm_constant uu____4117 -> tc_value env1 e
       | FStar_Syntax_Syntax.Tm_abs uu____4118 -> tc_value env1 e
       | FStar_Syntax_Syntax.Tm_arrow uu____4137 -> tc_value env1 e
       | FStar_Syntax_Syntax.Tm_refine uu____4152 -> tc_value env1 e
       | FStar_Syntax_Syntax.Tm_type uu____4159 -> tc_value env1 e
       | FStar_Syntax_Syntax.Tm_unknown  -> tc_value env1 e
       | FStar_Syntax_Syntax.Tm_quoted (qt,qi) ->
           let projl uu___2_4175 =
             match uu___2_4175 with
             | FStar_Util.Inl x -> x
             | FStar_Util.Inr uu____4181 -> failwith "projl fail"  in
           let non_trivial_antiquotes qi1 =
             let is_name1 t =
               let uu____4197 =
                 let uu____4198 = FStar_Syntax_Subst.compress t  in
                 uu____4198.FStar_Syntax_Syntax.n  in
               match uu____4197 with
               | FStar_Syntax_Syntax.Tm_name uu____4202 -> true
               | uu____4204 -> false  in
             FStar_Util.for_some
               (fun uu____4214  ->
                  match uu____4214 with
                  | (uu____4220,t) ->
                      let uu____4222 = is_name1 t  in
                      Prims.op_Negation uu____4222)
               qi1.FStar_Syntax_Syntax.antiquotes
              in
           (match qi.FStar_Syntax_Syntax.qkind with
            | FStar_Syntax_Syntax.Quote_static  when
                non_trivial_antiquotes qi ->
                let e0 = e  in
                let newbvs =
                  FStar_List.map
                    (fun uu____4241  ->
                       FStar_Syntax_Syntax.new_bv
                         FStar_Pervasives_Native.None
                         FStar_Syntax_Syntax.t_term)
                    qi.FStar_Syntax_Syntax.antiquotes
                   in
                let z =
                  FStar_List.zip qi.FStar_Syntax_Syntax.antiquotes newbvs  in
                let lbs =
                  FStar_List.map
                    (fun uu____4284  ->
                       match uu____4284 with
                       | ((bv,t),bv') ->
                           FStar_Syntax_Util.close_univs_and_mk_letbinding
                             FStar_Pervasives_Native.None
                             (FStar_Util.Inl bv') []
                             FStar_Syntax_Syntax.t_term
                             FStar_Parser_Const.effect_Tot_lid t []
                             t.FStar_Syntax_Syntax.pos) z
                   in
                let qi1 =
                  let uu___557_4313 = qi  in
                  let uu____4314 =
                    FStar_List.map
                      (fun uu____4342  ->
                         match uu____4342 with
                         | ((bv,uu____4358),bv') ->
                             let uu____4370 =
                               FStar_Syntax_Syntax.bv_to_name bv'  in
                             (bv, uu____4370)) z
                     in
                  {
                    FStar_Syntax_Syntax.qkind =
                      (uu___557_4313.FStar_Syntax_Syntax.qkind);
                    FStar_Syntax_Syntax.antiquotes = uu____4314
                  }  in
                let nq =
                  FStar_Syntax_Syntax.mk
                    (FStar_Syntax_Syntax.Tm_quoted (qt, qi1))
                    FStar_Pervasives_Native.None top.FStar_Syntax_Syntax.pos
                   in
                let e1 =
                  FStar_List.fold_left
                    (fun t  ->
                       fun lb  ->
                         let uu____4382 =
                           let uu____4389 =
                             let uu____4390 =
                               let uu____4404 =
                                 let uu____4407 =
                                   let uu____4408 =
                                     let uu____4415 =
                                       projl lb.FStar_Syntax_Syntax.lbname
                                        in
                                     FStar_Syntax_Syntax.mk_binder uu____4415
                                      in
                                   [uu____4408]  in
                                 FStar_Syntax_Subst.close uu____4407 t  in
                               ((false, [lb]), uu____4404)  in
                             FStar_Syntax_Syntax.Tm_let uu____4390  in
                           FStar_Syntax_Syntax.mk uu____4389  in
                         uu____4382 FStar_Pervasives_Native.None
                           top.FStar_Syntax_Syntax.pos) nq lbs
                   in
                tc_maybe_toplevel_term env1 e1
            | FStar_Syntax_Syntax.Quote_static  ->
                let aqs = qi.FStar_Syntax_Syntax.antiquotes  in
                let env_tm =
                  FStar_TypeChecker_Env.set_expected_typ env1
                    FStar_Syntax_Syntax.t_term
                   in
                let uu____4451 =
                  FStar_List.fold_right
                    (fun uu____4487  ->
                       fun uu____4488  ->
                         match (uu____4487, uu____4488) with
                         | ((bv,tm),(aqs_rev,guard)) ->
                             let uu____4557 = tc_term env_tm tm  in
                             (match uu____4557 with
                              | (tm1,uu____4575,g) ->
                                  let uu____4577 =
                                    FStar_TypeChecker_Env.conj_guard g guard
                                     in
                                  (((bv, tm1) :: aqs_rev), uu____4577))) aqs
                    ([], FStar_TypeChecker_Env.trivial_guard)
                   in
                (match uu____4451 with
                 | (aqs_rev,guard) ->
                     let qi1 =
                       let uu___585_4619 = qi  in
                       {
                         FStar_Syntax_Syntax.qkind =
                           (uu___585_4619.FStar_Syntax_Syntax.qkind);
                         FStar_Syntax_Syntax.antiquotes =
                           (FStar_List.rev aqs_rev)
                       }  in
                     let tm =
                       FStar_Syntax_Syntax.mk
                         (FStar_Syntax_Syntax.Tm_quoted (qt, qi1))
                         FStar_Pervasives_Native.None
                         top.FStar_Syntax_Syntax.pos
                        in
                     value_check_expected_typ env1 tm
                       (FStar_Util.Inl FStar_Syntax_Syntax.t_term) guard)
            | FStar_Syntax_Syntax.Quote_dynamic  ->
                let c = FStar_Syntax_Syntax.mk_Tac FStar_Syntax_Syntax.t_term
                   in
                let uu____4630 =
                  FStar_TypeChecker_Env.clear_expected_typ env1  in
                (match uu____4630 with
                 | (env',uu____4644) ->
                     let uu____4649 =
                       tc_term
                         (let uu___594_4658 = env'  in
                          {
                            FStar_TypeChecker_Env.solver =
                              (uu___594_4658.FStar_TypeChecker_Env.solver);
                            FStar_TypeChecker_Env.range =
                              (uu___594_4658.FStar_TypeChecker_Env.range);
                            FStar_TypeChecker_Env.curmodule =
                              (uu___594_4658.FStar_TypeChecker_Env.curmodule);
                            FStar_TypeChecker_Env.gamma =
                              (uu___594_4658.FStar_TypeChecker_Env.gamma);
                            FStar_TypeChecker_Env.gamma_sig =
                              (uu___594_4658.FStar_TypeChecker_Env.gamma_sig);
                            FStar_TypeChecker_Env.gamma_cache =
                              (uu___594_4658.FStar_TypeChecker_Env.gamma_cache);
                            FStar_TypeChecker_Env.modules =
                              (uu___594_4658.FStar_TypeChecker_Env.modules);
                            FStar_TypeChecker_Env.expected_typ =
                              (uu___594_4658.FStar_TypeChecker_Env.expected_typ);
                            FStar_TypeChecker_Env.sigtab =
                              (uu___594_4658.FStar_TypeChecker_Env.sigtab);
                            FStar_TypeChecker_Env.attrtab =
                              (uu___594_4658.FStar_TypeChecker_Env.attrtab);
                            FStar_TypeChecker_Env.instantiate_imp =
                              (uu___594_4658.FStar_TypeChecker_Env.instantiate_imp);
                            FStar_TypeChecker_Env.effects =
                              (uu___594_4658.FStar_TypeChecker_Env.effects);
                            FStar_TypeChecker_Env.generalize =
                              (uu___594_4658.FStar_TypeChecker_Env.generalize);
                            FStar_TypeChecker_Env.letrecs =
                              (uu___594_4658.FStar_TypeChecker_Env.letrecs);
                            FStar_TypeChecker_Env.top_level =
                              (uu___594_4658.FStar_TypeChecker_Env.top_level);
                            FStar_TypeChecker_Env.check_uvars =
                              (uu___594_4658.FStar_TypeChecker_Env.check_uvars);
                            FStar_TypeChecker_Env.use_eq =
                              (uu___594_4658.FStar_TypeChecker_Env.use_eq);
                            FStar_TypeChecker_Env.is_iface =
                              (uu___594_4658.FStar_TypeChecker_Env.is_iface);
                            FStar_TypeChecker_Env.admit =
                              (uu___594_4658.FStar_TypeChecker_Env.admit);
                            FStar_TypeChecker_Env.lax = true;
                            FStar_TypeChecker_Env.lax_universes =
                              (uu___594_4658.FStar_TypeChecker_Env.lax_universes);
                            FStar_TypeChecker_Env.phase1 =
                              (uu___594_4658.FStar_TypeChecker_Env.phase1);
                            FStar_TypeChecker_Env.failhard =
                              (uu___594_4658.FStar_TypeChecker_Env.failhard);
                            FStar_TypeChecker_Env.nosynth =
                              (uu___594_4658.FStar_TypeChecker_Env.nosynth);
                            FStar_TypeChecker_Env.uvar_subtyping =
                              (uu___594_4658.FStar_TypeChecker_Env.uvar_subtyping);
                            FStar_TypeChecker_Env.tc_term =
                              (uu___594_4658.FStar_TypeChecker_Env.tc_term);
                            FStar_TypeChecker_Env.type_of =
                              (uu___594_4658.FStar_TypeChecker_Env.type_of);
                            FStar_TypeChecker_Env.universe_of =
                              (uu___594_4658.FStar_TypeChecker_Env.universe_of);
                            FStar_TypeChecker_Env.check_type_of =
                              (uu___594_4658.FStar_TypeChecker_Env.check_type_of);
                            FStar_TypeChecker_Env.use_bv_sorts =
                              (uu___594_4658.FStar_TypeChecker_Env.use_bv_sorts);
                            FStar_TypeChecker_Env.qtbl_name_and_index =
                              (uu___594_4658.FStar_TypeChecker_Env.qtbl_name_and_index);
                            FStar_TypeChecker_Env.normalized_eff_names =
                              (uu___594_4658.FStar_TypeChecker_Env.normalized_eff_names);
                            FStar_TypeChecker_Env.fv_delta_depths =
                              (uu___594_4658.FStar_TypeChecker_Env.fv_delta_depths);
                            FStar_TypeChecker_Env.proof_ns =
                              (uu___594_4658.FStar_TypeChecker_Env.proof_ns);
                            FStar_TypeChecker_Env.synth_hook =
                              (uu___594_4658.FStar_TypeChecker_Env.synth_hook);
                            FStar_TypeChecker_Env.splice =
                              (uu___594_4658.FStar_TypeChecker_Env.splice);
                            FStar_TypeChecker_Env.mpreprocess =
                              (uu___594_4658.FStar_TypeChecker_Env.mpreprocess);
                            FStar_TypeChecker_Env.postprocess =
                              (uu___594_4658.FStar_TypeChecker_Env.postprocess);
                            FStar_TypeChecker_Env.is_native_tactic =
                              (uu___594_4658.FStar_TypeChecker_Env.is_native_tactic);
                            FStar_TypeChecker_Env.identifier_info =
                              (uu___594_4658.FStar_TypeChecker_Env.identifier_info);
                            FStar_TypeChecker_Env.tc_hooks =
                              (uu___594_4658.FStar_TypeChecker_Env.tc_hooks);
                            FStar_TypeChecker_Env.dsenv =
                              (uu___594_4658.FStar_TypeChecker_Env.dsenv);
                            FStar_TypeChecker_Env.nbe =
                              (uu___594_4658.FStar_TypeChecker_Env.nbe);
                            FStar_TypeChecker_Env.strict_args_tab =
                              (uu___594_4658.FStar_TypeChecker_Env.strict_args_tab);
                            FStar_TypeChecker_Env.erasable_types_tab =
                              (uu___594_4658.FStar_TypeChecker_Env.erasable_types_tab)
                          }) qt
                        in
                     (match uu____4649 with
                      | (qt1,uu____4667,uu____4668) ->
                          let t =
                            FStar_Syntax_Syntax.mk
                              (FStar_Syntax_Syntax.Tm_quoted (qt1, qi))
                              FStar_Pervasives_Native.None
                              top.FStar_Syntax_Syntax.pos
                             in
                          let uu____4674 =
                            let uu____4681 =
                              let uu____4686 =
                                FStar_TypeChecker_Common.lcomp_of_comp c  in
                              FStar_Util.Inr uu____4686  in
                            value_check_expected_typ env1 top uu____4681
                              FStar_TypeChecker_Env.trivial_guard
                             in
                          (match uu____4674 with
                           | (t1,lc,g) ->
                               let t2 =
                                 FStar_Syntax_Syntax.mk
                                   (FStar_Syntax_Syntax.Tm_meta
                                      (t1,
                                        (FStar_Syntax_Syntax.Meta_monadic_lift
                                           (FStar_Parser_Const.effect_PURE_lid,
                                             FStar_Parser_Const.effect_TAC_lid,
                                             FStar_Syntax_Syntax.t_term))))
                                   FStar_Pervasives_Native.None
                                   t1.FStar_Syntax_Syntax.pos
                                  in
                               (t2, lc, g)))))
       | FStar_Syntax_Syntax.Tm_lazy
           { FStar_Syntax_Syntax.blob = uu____4703;
             FStar_Syntax_Syntax.lkind = FStar_Syntax_Syntax.Lazy_embedding
               uu____4704;
             FStar_Syntax_Syntax.ltyp = uu____4705;
             FStar_Syntax_Syntax.rng = uu____4706;_}
           ->
           let uu____4717 = FStar_Syntax_Util.unlazy top  in
           tc_term env1 uu____4717
       | FStar_Syntax_Syntax.Tm_lazy i ->
           value_check_expected_typ env1 top
             (FStar_Util.Inl (i.FStar_Syntax_Syntax.ltyp))
             FStar_TypeChecker_Env.trivial_guard
       | FStar_Syntax_Syntax.Tm_meta
           (e1,FStar_Syntax_Syntax.Meta_desugared
            (FStar_Syntax_Syntax.Meta_smt_pat ))
           ->
           let uu____4724 = tc_tot_or_gtot_term env1 e1  in
           (match uu____4724 with
            | (e2,c,g) ->
                let g1 =
                  let uu___624_4741 = g  in
                  {
                    FStar_TypeChecker_Common.guard_f =
                      FStar_TypeChecker_Common.Trivial;
                    FStar_TypeChecker_Common.deferred =
                      (uu___624_4741.FStar_TypeChecker_Common.deferred);
                    FStar_TypeChecker_Common.univ_ineqs =
                      (uu___624_4741.FStar_TypeChecker_Common.univ_ineqs);
                    FStar_TypeChecker_Common.implicits =
                      (uu___624_4741.FStar_TypeChecker_Common.implicits)
                  }  in
                let uu____4742 =
                  FStar_Syntax_Syntax.mk
                    (FStar_Syntax_Syntax.Tm_meta
                       (e2,
                         (FStar_Syntax_Syntax.Meta_desugared
                            FStar_Syntax_Syntax.Meta_smt_pat)))
                    FStar_Pervasives_Native.None top.FStar_Syntax_Syntax.pos
                   in
                (uu____4742, c, g1))
       | FStar_Syntax_Syntax.Tm_meta
           (e1,FStar_Syntax_Syntax.Meta_pattern (names1,pats)) ->
           let uu____4784 = FStar_Syntax_Util.type_u ()  in
           (match uu____4784 with
            | (t,u) ->
                let uu____4797 = tc_check_tot_or_gtot_term env1 e1 t  in
                (match uu____4797 with
                 | (e2,c,g) ->
                     let uu____4813 =
                       let uu____4830 =
                         FStar_TypeChecker_Env.clear_expected_typ env1  in
                       match uu____4830 with
                       | (env2,uu____4854) -> tc_smt_pats env2 pats  in
                     (match uu____4813 with
                      | (pats1,g') ->
                          let g'1 =
                            let uu___647_4892 = g'  in
                            {
                              FStar_TypeChecker_Common.guard_f =
                                FStar_TypeChecker_Common.Trivial;
                              FStar_TypeChecker_Common.deferred =
                                (uu___647_4892.FStar_TypeChecker_Common.deferred);
                              FStar_TypeChecker_Common.univ_ineqs =
                                (uu___647_4892.FStar_TypeChecker_Common.univ_ineqs);
                              FStar_TypeChecker_Common.implicits =
                                (uu___647_4892.FStar_TypeChecker_Common.implicits)
                            }  in
                          let uu____4893 =
                            FStar_Syntax_Syntax.mk
                              (FStar_Syntax_Syntax.Tm_meta
                                 (e2,
                                   (FStar_Syntax_Syntax.Meta_pattern
                                      (names1, pats1))))
                              FStar_Pervasives_Native.None
                              top.FStar_Syntax_Syntax.pos
                             in
                          let uu____4912 =
                            FStar_TypeChecker_Env.conj_guard g g'1  in
                          (uu____4893, c, uu____4912))))
       | FStar_Syntax_Syntax.Tm_meta
           (e1,FStar_Syntax_Syntax.Meta_desugared
            (FStar_Syntax_Syntax.Sequence ))
           ->
           let uu____4918 =
             let uu____4919 = FStar_Syntax_Subst.compress e1  in
             uu____4919.FStar_Syntax_Syntax.n  in
           (match uu____4918 with
            | FStar_Syntax_Syntax.Tm_let
                ((uu____4928,{ FStar_Syntax_Syntax.lbname = x;
                               FStar_Syntax_Syntax.lbunivs = uu____4930;
                               FStar_Syntax_Syntax.lbtyp = uu____4931;
                               FStar_Syntax_Syntax.lbeff = uu____4932;
                               FStar_Syntax_Syntax.lbdef = e11;
                               FStar_Syntax_Syntax.lbattrs = uu____4934;
                               FStar_Syntax_Syntax.lbpos = uu____4935;_}::[]),e2)
                ->
                let uu____4966 =
                  let uu____4973 =
                    FStar_TypeChecker_Env.set_expected_typ env1
                      FStar_Syntax_Syntax.t_unit
                     in
                  tc_term uu____4973 e11  in
                (match uu____4966 with
                 | (e12,c1,g1) ->
                     let uu____4983 = tc_term env1 e2  in
                     (match uu____4983 with
                      | (e21,c2,g2) ->
                          let c =
                            FStar_TypeChecker_Util.maybe_return_e2_and_bind
                              e12.FStar_Syntax_Syntax.pos env1
                              (FStar_Pervasives_Native.Some e12) c1 e21
                              (FStar_Pervasives_Native.None, c2)
                             in
                          let e13 =
                            FStar_TypeChecker_Util.maybe_lift env1 e12
                              c1.FStar_TypeChecker_Common.eff_name
                              c.FStar_TypeChecker_Common.eff_name
                              c1.FStar_TypeChecker_Common.res_typ
                             in
                          let e22 =
                            FStar_TypeChecker_Util.maybe_lift env1 e21
                              c2.FStar_TypeChecker_Common.eff_name
                              c.FStar_TypeChecker_Common.eff_name
                              c2.FStar_TypeChecker_Common.res_typ
                             in
                          let attrs =
                            let uu____5007 =
                              FStar_TypeChecker_Util.is_pure_or_ghost_effect
                                env1 c1.FStar_TypeChecker_Common.eff_name
                               in
                            if uu____5007
                            then [FStar_Syntax_Util.inline_let_attr]
                            else []  in
                          let e3 =
                            let uu____5017 =
                              let uu____5024 =
                                let uu____5025 =
                                  let uu____5039 =
                                    let uu____5047 =
                                      let uu____5050 =
                                        FStar_Syntax_Syntax.mk_lb
                                          (x, [],
                                            (c1.FStar_TypeChecker_Common.eff_name),
                                            FStar_Syntax_Syntax.t_unit, e13,
                                            attrs,
                                            (e13.FStar_Syntax_Syntax.pos))
                                         in
                                      [uu____5050]  in
                                    (false, uu____5047)  in
                                  (uu____5039, e22)  in
                                FStar_Syntax_Syntax.Tm_let uu____5025  in
                              FStar_Syntax_Syntax.mk uu____5024  in
                            uu____5017 FStar_Pervasives_Native.None
                              e1.FStar_Syntax_Syntax.pos
                             in
                          let e4 =
                            FStar_TypeChecker_Util.maybe_monadic env1 e3
                              c.FStar_TypeChecker_Common.eff_name
                              c.FStar_TypeChecker_Common.res_typ
                             in
                          let e5 =
                            FStar_Syntax_Syntax.mk
                              (FStar_Syntax_Syntax.Tm_meta
                                 (e4,
                                   (FStar_Syntax_Syntax.Meta_desugared
                                      FStar_Syntax_Syntax.Sequence)))
                              FStar_Pervasives_Native.None
                              top.FStar_Syntax_Syntax.pos
                             in
                          let uu____5074 =
                            FStar_TypeChecker_Env.conj_guard g1 g2  in
                          (e5, c, uu____5074)))
            | uu____5075 ->
                let uu____5076 = tc_term env1 e1  in
                (match uu____5076 with
                 | (e2,c,g) ->
                     let e3 =
                       FStar_Syntax_Syntax.mk
                         (FStar_Syntax_Syntax.Tm_meta
                            (e2,
                              (FStar_Syntax_Syntax.Meta_desugared
                                 FStar_Syntax_Syntax.Sequence)))
                         FStar_Pervasives_Native.None
                         top.FStar_Syntax_Syntax.pos
                        in
                     (e3, c, g)))
       | FStar_Syntax_Syntax.Tm_meta
           (e1,FStar_Syntax_Syntax.Meta_monadic uu____5098) ->
           tc_term env1 e1
       | FStar_Syntax_Syntax.Tm_meta
           (e1,FStar_Syntax_Syntax.Meta_monadic_lift uu____5110) ->
           tc_term env1 e1
       | FStar_Syntax_Syntax.Tm_meta (e1,m) ->
           let uu____5129 = tc_term env1 e1  in
           (match uu____5129 with
            | (e2,c,g) ->
                let e3 =
                  FStar_Syntax_Syntax.mk
                    (FStar_Syntax_Syntax.Tm_meta (e2, m))
                    FStar_Pervasives_Native.None top.FStar_Syntax_Syntax.pos
                   in
                (e3, c, g))
       | FStar_Syntax_Syntax.Tm_ascribed
           (uu____5150,(FStar_Util.Inr expected_c,_tacopt),uu____5153) when
           let uu____5200 = FStar_All.pipe_right top is_comp_ascribed_reflect
              in
           FStar_All.pipe_right uu____5200 FStar_Util.is_some ->
           let uu____5232 =
             let uu____5243 =
               FStar_All.pipe_right top is_comp_ascribed_reflect  in
             FStar_All.pipe_right uu____5243 FStar_Util.must  in
           (match uu____5232 with
            | (effect_lid,e1,aqual) ->
                let uu____5317 =
                  FStar_TypeChecker_Env.clear_expected_typ env1  in
                (match uu____5317 with
                 | (env0,uu____5331) ->
                     let uu____5336 = tc_comp env0 expected_c  in
                     (match uu____5336 with
                      | (expected_c1,uu____5350,g_c) ->
                          let expected_ct =
                            FStar_TypeChecker_Env.unfold_effect_abbrev env0
                              expected_c1
                             in
                          ((let uu____5354 =
                              let uu____5356 =
                                FStar_Ident.lid_equals effect_lid
                                  expected_ct.FStar_Syntax_Syntax.effect_name
                                 in
                              Prims.op_Negation uu____5356  in
                            if uu____5354
                            then
                              let uu____5359 =
                                let uu____5365 =
                                  let uu____5367 =
                                    FStar_Ident.string_of_lid effect_lid  in
                                  let uu____5369 =
                                    FStar_Ident.string_of_lid
                                      expected_ct.FStar_Syntax_Syntax.effect_name
                                     in
                                  FStar_Util.format2
                                    "The effect on reflect %s does not match with the annotation %s\n"
                                    uu____5367 uu____5369
                                   in
                                (FStar_Errors.Fatal_UnexpectedEffect,
                                  uu____5365)
                                 in
                              FStar_Errors.raise_error uu____5359
                                top.FStar_Syntax_Syntax.pos
                            else ());
                           (let uu____5376 =
                              let uu____5378 =
                                FStar_TypeChecker_Env.is_user_reflectable_effect
                                  env1 effect_lid
                                 in
                              Prims.op_Negation uu____5378  in
                            if uu____5376
                            then
                              let uu____5381 =
                                let uu____5387 =
                                  let uu____5389 =
                                    FStar_Ident.string_of_lid effect_lid  in
                                  FStar_Util.format1
                                    "Effect %s cannot be reflected"
                                    uu____5389
                                   in
                                (FStar_Errors.Fatal_EffectCannotBeReified,
                                  uu____5387)
                                 in
                              FStar_Errors.raise_error uu____5381
                                top.FStar_Syntax_Syntax.pos
                            else ());
                           (let u_c =
                              FStar_All.pipe_right
                                expected_ct.FStar_Syntax_Syntax.comp_univs
                                FStar_List.hd
                               in
                            let repr =
                              let uu____5399 =
                                let uu____5402 =
                                  FStar_All.pipe_right expected_ct
                                    FStar_Syntax_Syntax.mk_Comp
                                   in
                                FStar_TypeChecker_Env.effect_repr env0
                                  uu____5402 u_c
                                 in
                              FStar_All.pipe_right uu____5399 FStar_Util.must
                               in
                            let e2 =
                              let uu____5408 =
                                let uu____5415 =
                                  let uu____5416 =
                                    let uu____5443 =
                                      let uu____5460 =
                                        let uu____5469 =
                                          FStar_Syntax_Syntax.mk_Total' repr
                                            (FStar_Pervasives_Native.Some u_c)
                                           in
                                        FStar_Util.Inr uu____5469  in
                                      (uu____5460,
                                        FStar_Pervasives_Native.None)
                                       in
                                    (e1, uu____5443,
                                      FStar_Pervasives_Native.None)
                                     in
                                  FStar_Syntax_Syntax.Tm_ascribed uu____5416
                                   in
                                FStar_Syntax_Syntax.mk uu____5415  in
                              uu____5408 FStar_Pervasives_Native.None
                                e1.FStar_Syntax_Syntax.pos
                               in
                            (let uu____5511 =
                               FStar_All.pipe_left
                                 (FStar_TypeChecker_Env.debug env0)
                                 FStar_Options.Extreme
                                in
                             if uu____5511
                             then
                               let uu____5515 =
                                 FStar_Syntax_Print.term_to_string e2  in
                               FStar_Util.print1
                                 "Typechecking ascribed reflect, inner ascribed term: %s\n"
                                 uu____5515
                             else ());
                            (let uu____5520 = tc_tot_or_gtot_term env0 e2  in
                             match uu____5520 with
                             | (e3,uu____5534,g_e) ->
                                 let e4 = FStar_Syntax_Util.unascribe e3  in
                                 ((let uu____5538 =
                                     FStar_All.pipe_left
                                       (FStar_TypeChecker_Env.debug env0)
                                       FStar_Options.Extreme
                                      in
                                   if uu____5538
                                   then
                                     let uu____5542 =
                                       FStar_Syntax_Print.term_to_string e4
                                        in
                                     let uu____5544 =
                                       FStar_TypeChecker_Rel.guard_to_string
                                         env0 g_e
                                        in
                                     FStar_Util.print2
                                       "Typechecking ascribed reflect, after typechecking inner ascribed term: %s and guard: %s\n"
                                       uu____5542 uu____5544
                                   else ());
                                  (let top1 =
                                     let r = top.FStar_Syntax_Syntax.pos  in
                                     let tm =
                                       FStar_Syntax_Syntax.mk
                                         (FStar_Syntax_Syntax.Tm_constant
                                            (FStar_Const.Const_reflect
                                               effect_lid))
                                         FStar_Pervasives_Native.None r
                                        in
                                     let tm1 =
                                       FStar_Syntax_Syntax.mk
                                         (FStar_Syntax_Syntax.Tm_app
                                            (tm, [(e4, aqual)]))
                                         FStar_Pervasives_Native.None r
                                        in
                                     let uu____5591 =
                                       let uu____5598 =
                                         let uu____5599 =
                                           let uu____5626 =
                                             let uu____5629 =
                                               FStar_All.pipe_right
                                                 expected_c1
                                                 FStar_Syntax_Util.comp_effect_name
                                                in
                                             FStar_All.pipe_right uu____5629
                                               (fun _5634  ->
                                                  FStar_Pervasives_Native.Some
                                                    _5634)
                                              in
                                           (tm1,
                                             ((FStar_Util.Inr expected_c1),
                                               _tacopt), uu____5626)
                                            in
                                         FStar_Syntax_Syntax.Tm_ascribed
                                           uu____5599
                                          in
                                       FStar_Syntax_Syntax.mk uu____5598  in
                                     uu____5591 FStar_Pervasives_Native.None
                                       r
                                      in
                                   let uu____5671 =
                                     let uu____5678 =
                                       FStar_All.pipe_right expected_c1
                                         FStar_TypeChecker_Common.lcomp_of_comp
                                        in
                                     comp_check_expected_typ env1 top1
                                       uu____5678
                                      in
                                   match uu____5671 with
                                   | (top2,c,g_env) ->
                                       let uu____5688 =
                                         FStar_TypeChecker_Env.conj_guards
                                           [g_c; g_e; g_env]
                                          in
                                       (top2, c, uu____5688)))))))))
       | FStar_Syntax_Syntax.Tm_ascribed
           (e1,(FStar_Util.Inr expected_c,topt),uu____5692) ->
           let uu____5739 = FStar_TypeChecker_Env.clear_expected_typ env1  in
           (match uu____5739 with
            | (env0,uu____5753) ->
                let uu____5758 = tc_comp env0 expected_c  in
                (match uu____5758 with
                 | (expected_c1,uu____5772,g) ->
                     let uu____5774 =
                       let uu____5781 =
                         FStar_All.pipe_right
                           (FStar_Syntax_Util.comp_result expected_c1)
                           (FStar_TypeChecker_Env.set_expected_typ env0)
                          in
                       tc_term uu____5781 e1  in
                     (match uu____5774 with
                      | (e2,c',g') ->
                          let uu____5791 =
                            let uu____5802 =
                              FStar_TypeChecker_Common.lcomp_comp c'  in
                            match uu____5802 with
                            | (c'1,g_c') ->
                                let uu____5819 =
                                  check_expected_effect env0
                                    (FStar_Pervasives_Native.Some expected_c1)
                                    (e2, c'1)
                                   in
                                (match uu____5819 with
                                 | (e3,expected_c2,g'') ->
                                     let uu____5839 =
                                       FStar_TypeChecker_Env.conj_guard g_c'
                                         g''
                                        in
                                     (e3, expected_c2, uu____5839))
                             in
                          (match uu____5791 with
                           | (e3,expected_c2,g'') ->
                               let uu____5861 = tc_tactic_opt env0 topt  in
                               (match uu____5861 with
                                | (topt1,gtac) ->
                                    let e4 =
                                      FStar_Syntax_Syntax.mk
                                        (FStar_Syntax_Syntax.Tm_ascribed
                                           (e3,
                                             ((FStar_Util.Inr expected_c2),
                                               topt1),
                                             (FStar_Pervasives_Native.Some
                                                (FStar_Syntax_Util.comp_effect_name
                                                   expected_c2))))
                                        FStar_Pervasives_Native.None
                                        top.FStar_Syntax_Syntax.pos
                                       in
                                    let lc =
                                      FStar_TypeChecker_Common.lcomp_of_comp
                                        expected_c2
                                       in
                                    let f =
                                      let uu____5921 =
                                        FStar_TypeChecker_Env.conj_guard g'
                                          g''
                                         in
                                      FStar_TypeChecker_Env.conj_guard g
                                        uu____5921
                                       in
                                    let uu____5922 =
                                      comp_check_expected_typ env1 e4 lc  in
                                    (match uu____5922 with
                                     | (e5,c,f2) ->
                                         let final_guard =
                                           let uu____5939 =
                                             FStar_TypeChecker_Env.conj_guard
                                               f f2
                                              in
                                           wrap_guard_with_tactic_opt topt1
                                             uu____5939
                                            in
                                         let uu____5940 =
                                           FStar_TypeChecker_Env.conj_guard
                                             final_guard gtac
                                            in
                                         (e5, c, uu____5940)))))))
       | FStar_Syntax_Syntax.Tm_ascribed
           (e1,(FStar_Util.Inl t,topt),uu____5944) ->
           let uu____5991 = FStar_Syntax_Util.type_u ()  in
           (match uu____5991 with
            | (k,u) ->
                let uu____6004 = tc_check_tot_or_gtot_term env1 t k  in
                (match uu____6004 with
                 | (t1,uu____6018,f) ->
                     let uu____6020 = tc_tactic_opt env1 topt  in
                     (match uu____6020 with
                      | (topt1,gtac) ->
                          let uu____6039 =
                            let uu____6046 =
                              FStar_TypeChecker_Env.set_expected_typ env1 t1
                               in
                            tc_term uu____6046 e1  in
                          (match uu____6039 with
                           | (e2,c,g) ->
                               let uu____6056 =
                                 let uu____6061 =
                                   FStar_TypeChecker_Env.set_range env1
                                     t1.FStar_Syntax_Syntax.pos
                                    in
                                 FStar_TypeChecker_Util.strengthen_precondition
                                   (FStar_Pervasives_Native.Some
                                      (fun uu____6067  ->
                                         FStar_Util.return_all
                                           FStar_TypeChecker_Err.ill_kinded_type))
                                   uu____6061 e2 c f
                                  in
                               (match uu____6056 with
                                | (c1,f1) ->
                                    let uu____6077 =
                                      let uu____6084 =
                                        FStar_Syntax_Syntax.mk
                                          (FStar_Syntax_Syntax.Tm_ascribed
                                             (e2,
                                               ((FStar_Util.Inl t1), topt1),
                                               (FStar_Pervasives_Native.Some
                                                  (c1.FStar_TypeChecker_Common.eff_name))))
                                          FStar_Pervasives_Native.None
                                          top.FStar_Syntax_Syntax.pos
                                         in
                                      comp_check_expected_typ env1 uu____6084
                                        c1
                                       in
                                    (match uu____6077 with
                                     | (e3,c2,f2) ->
                                         let final_guard =
                                           let uu____6131 =
                                             FStar_TypeChecker_Env.conj_guard
                                               g f2
                                              in
                                           FStar_TypeChecker_Env.conj_guard
                                             f1 uu____6131
                                            in
                                         let final_guard1 =
                                           wrap_guard_with_tactic_opt topt1
                                             final_guard
                                            in
                                         let uu____6133 =
                                           FStar_TypeChecker_Env.conj_guard
                                             final_guard1 gtac
                                            in
                                         (e3, c2, uu____6133)))))))
       | FStar_Syntax_Syntax.Tm_app
           ({
              FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant
                (FStar_Const.Const_range_of );
              FStar_Syntax_Syntax.pos = uu____6134;
              FStar_Syntax_Syntax.vars = uu____6135;_},a::hd1::rest)
           ->
           let rest1 = hd1 :: rest  in
           let uu____6214 = FStar_Syntax_Util.head_and_args top  in
           (match uu____6214 with
            | (unary_op1,uu____6238) ->
                let head1 =
                  let uu____6266 =
                    FStar_Range.union_ranges
                      unary_op1.FStar_Syntax_Syntax.pos
                      (FStar_Pervasives_Native.fst a).FStar_Syntax_Syntax.pos
                     in
                  FStar_Syntax_Syntax.mk
                    (FStar_Syntax_Syntax.Tm_app (unary_op1, [a]))
                    FStar_Pervasives_Native.None uu____6266
                   in
                let t =
                  FStar_Syntax_Syntax.mk
                    (FStar_Syntax_Syntax.Tm_app (head1, rest1))
                    FStar_Pervasives_Native.None top.FStar_Syntax_Syntax.pos
                   in
                tc_term env1 t)
       | FStar_Syntax_Syntax.Tm_app
           ({
              FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant
                (FStar_Const.Const_reify );
              FStar_Syntax_Syntax.pos = uu____6314;
              FStar_Syntax_Syntax.vars = uu____6315;_},a::hd1::rest)
           ->
           let rest1 = hd1 :: rest  in
           let uu____6394 = FStar_Syntax_Util.head_and_args top  in
           (match uu____6394 with
            | (unary_op1,uu____6418) ->
                let head1 =
                  let uu____6446 =
                    FStar_Range.union_ranges
                      unary_op1.FStar_Syntax_Syntax.pos
                      (FStar_Pervasives_Native.fst a).FStar_Syntax_Syntax.pos
                     in
                  FStar_Syntax_Syntax.mk
                    (FStar_Syntax_Syntax.Tm_app (unary_op1, [a]))
                    FStar_Pervasives_Native.None uu____6446
                   in
                let t =
                  FStar_Syntax_Syntax.mk
                    (FStar_Syntax_Syntax.Tm_app (head1, rest1))
                    FStar_Pervasives_Native.None top.FStar_Syntax_Syntax.pos
                   in
                tc_term env1 t)
       | FStar_Syntax_Syntax.Tm_app
           ({
              FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant
                (FStar_Const.Const_reflect uu____6494);
              FStar_Syntax_Syntax.pos = uu____6495;
              FStar_Syntax_Syntax.vars = uu____6496;_},a::hd1::rest)
           ->
           let rest1 = hd1 :: rest  in
           let uu____6575 = FStar_Syntax_Util.head_and_args top  in
           (match uu____6575 with
            | (unary_op1,uu____6599) ->
                let head1 =
                  let uu____6627 =
                    FStar_Range.union_ranges
                      unary_op1.FStar_Syntax_Syntax.pos
                      (FStar_Pervasives_Native.fst a).FStar_Syntax_Syntax.pos
                     in
                  FStar_Syntax_Syntax.mk
                    (FStar_Syntax_Syntax.Tm_app (unary_op1, [a]))
                    FStar_Pervasives_Native.None uu____6627
                   in
                let t =
                  FStar_Syntax_Syntax.mk
                    (FStar_Syntax_Syntax.Tm_app (head1, rest1))
                    FStar_Pervasives_Native.None top.FStar_Syntax_Syntax.pos
                   in
                tc_term env1 t)
       | FStar_Syntax_Syntax.Tm_app
           ({
              FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant
                (FStar_Const.Const_set_range_of );
              FStar_Syntax_Syntax.pos = uu____6675;
              FStar_Syntax_Syntax.vars = uu____6676;_},a1::a2::hd1::rest)
           ->
           let rest1 = hd1 :: rest  in
           let uu____6772 = FStar_Syntax_Util.head_and_args top  in
           (match uu____6772 with
            | (unary_op1,uu____6796) ->
                let head1 =
                  let uu____6824 =
                    FStar_Range.union_ranges
                      unary_op1.FStar_Syntax_Syntax.pos
                      (FStar_Pervasives_Native.fst a1).FStar_Syntax_Syntax.pos
                     in
                  FStar_Syntax_Syntax.mk
                    (FStar_Syntax_Syntax.Tm_app (unary_op1, [a1; a2]))
                    FStar_Pervasives_Native.None uu____6824
                   in
                let t =
                  FStar_Syntax_Syntax.mk
                    (FStar_Syntax_Syntax.Tm_app (head1, rest1))
                    FStar_Pervasives_Native.None top.FStar_Syntax_Syntax.pos
                   in
                tc_term env1 t)
       | FStar_Syntax_Syntax.Tm_app
           ({
              FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant
                (FStar_Const.Const_range_of );
              FStar_Syntax_Syntax.pos = uu____6880;
              FStar_Syntax_Syntax.vars = uu____6881;_},(e1,FStar_Pervasives_Native.None
                                                        )::[])
           ->
           let uu____6919 =
             let uu____6926 =
               let uu____6927 = FStar_TypeChecker_Env.clear_expected_typ env1
                  in
               FStar_All.pipe_left FStar_Pervasives_Native.fst uu____6927  in
             tc_term uu____6926 e1  in
           (match uu____6919 with
            | (e2,c,g) ->
                let uu____6951 = FStar_Syntax_Util.head_and_args top  in
                (match uu____6951 with
                 | (head1,uu____6975) ->
                     let uu____7000 =
                       FStar_Syntax_Syntax.mk
                         (FStar_Syntax_Syntax.Tm_app
                            (head1, [(e2, FStar_Pervasives_Native.None)]))
                         FStar_Pervasives_Native.None
                         top.FStar_Syntax_Syntax.pos
                        in
                     let uu____7033 =
                       let uu____7034 =
                         let uu____7035 =
                           FStar_Syntax_Syntax.tabbrev
                             FStar_Parser_Const.range_lid
                            in
                         FStar_Syntax_Syntax.mk_Total uu____7035  in
                       FStar_All.pipe_left
                         FStar_TypeChecker_Common.lcomp_of_comp uu____7034
                        in
                     (uu____7000, uu____7033, g)))
       | FStar_Syntax_Syntax.Tm_app
           ({
              FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant
                (FStar_Const.Const_set_range_of );
              FStar_Syntax_Syntax.pos = uu____7036;
              FStar_Syntax_Syntax.vars = uu____7037;_},(t,FStar_Pervasives_Native.None
                                                        )::(r,FStar_Pervasives_Native.None
                                                            )::[])
           ->
           let uu____7090 = FStar_Syntax_Util.head_and_args top  in
           (match uu____7090 with
            | (head1,uu____7114) ->
                let env' =
                  let uu____7140 =
                    FStar_Syntax_Syntax.tabbrev FStar_Parser_Const.range_lid
                     in
                  FStar_TypeChecker_Env.set_expected_typ env1 uu____7140  in
                let uu____7141 = tc_term env' r  in
                (match uu____7141 with
                 | (er,uu____7155,gr) ->
                     let uu____7157 = tc_term env1 t  in
                     (match uu____7157 with
                      | (t1,tt,gt1) ->
                          let g = FStar_TypeChecker_Env.conj_guard gr gt1  in
                          let uu____7174 =
                            let uu____7175 =
                              let uu____7180 =
                                let uu____7181 =
                                  FStar_Syntax_Syntax.as_arg t1  in
                                let uu____7190 =
                                  let uu____7201 =
                                    FStar_Syntax_Syntax.as_arg r  in
                                  [uu____7201]  in
                                uu____7181 :: uu____7190  in
                              FStar_Syntax_Syntax.mk_Tm_app head1 uu____7180
                               in
                            uu____7175 FStar_Pervasives_Native.None
                              top.FStar_Syntax_Syntax.pos
                             in
                          (uu____7174, tt, g))))
       | FStar_Syntax_Syntax.Tm_app
           ({
              FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant
                (FStar_Const.Const_range_of );
              FStar_Syntax_Syntax.pos = uu____7234;
              FStar_Syntax_Syntax.vars = uu____7235;_},uu____7236)
           ->
           let uu____7261 =
             let uu____7267 =
               let uu____7269 = FStar_Syntax_Print.term_to_string top  in
               FStar_Util.format1 "Ill-applied constant %s" uu____7269  in
             (FStar_Errors.Fatal_IllAppliedConstant, uu____7267)  in
           FStar_Errors.raise_error uu____7261 e.FStar_Syntax_Syntax.pos
       | FStar_Syntax_Syntax.Tm_app
           ({
              FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant
                (FStar_Const.Const_set_range_of );
              FStar_Syntax_Syntax.pos = uu____7279;
              FStar_Syntax_Syntax.vars = uu____7280;_},uu____7281)
           ->
           let uu____7306 =
             let uu____7312 =
               let uu____7314 = FStar_Syntax_Print.term_to_string top  in
               FStar_Util.format1 "Ill-applied constant %s" uu____7314  in
             (FStar_Errors.Fatal_IllAppliedConstant, uu____7312)  in
           FStar_Errors.raise_error uu____7306 e.FStar_Syntax_Syntax.pos
       | FStar_Syntax_Syntax.Tm_app
           ({
              FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant
                (FStar_Const.Const_reify );
              FStar_Syntax_Syntax.pos = uu____7324;
              FStar_Syntax_Syntax.vars = uu____7325;_},(e1,aqual)::[])
           ->
           (if FStar_Option.isSome aqual
            then
              FStar_Errors.log_issue e1.FStar_Syntax_Syntax.pos
                (FStar_Errors.Warning_IrrelevantQualifierOnArgumentToReify,
                  "Qualifier on argument to reify is irrelevant and will be ignored")
            else ();
            (let uu____7372 = FStar_TypeChecker_Env.clear_expected_typ env1
                in
             match uu____7372 with
             | (env0,uu____7386) ->
                 let uu____7391 = tc_term env0 e1  in
                 (match uu____7391 with
                  | (e2,c,g) ->
                      let uu____7407 = FStar_Syntax_Util.head_and_args top
                         in
                      (match uu____7407 with
                       | (reify_op,uu____7431) ->
                           let u_c =
                             env1.FStar_TypeChecker_Env.universe_of env1
                               c.FStar_TypeChecker_Common.res_typ
                              in
                           let uu____7457 =
                             FStar_TypeChecker_Common.lcomp_comp c  in
                           (match uu____7457 with
                            | (c1,g_c) ->
                                let ef =
                                  FStar_Syntax_Util.comp_effect_name c1  in
                                ((let uu____7472 =
                                    let uu____7474 =
                                      FStar_TypeChecker_Env.is_user_reifiable_effect
                                        env1 ef
                                       in
                                    Prims.op_Negation uu____7474  in
                                  if uu____7472
                                  then
                                    let uu____7477 =
                                      let uu____7483 =
                                        FStar_Util.format1
                                          "Effect %s cannot be reified"
                                          ef.FStar_Ident.str
                                         in
                                      (FStar_Errors.Fatal_EffectCannotBeReified,
                                        uu____7483)
                                       in
                                    FStar_Errors.raise_error uu____7477
                                      e2.FStar_Syntax_Syntax.pos
                                  else ());
                                 (let repr =
                                    FStar_TypeChecker_Env.reify_comp env1 c1
                                      u_c
                                     in
                                  let e3 =
                                    FStar_Syntax_Syntax.mk
                                      (FStar_Syntax_Syntax.Tm_app
                                         (reify_op, [(e2, aqual)]))
                                      FStar_Pervasives_Native.None
                                      top.FStar_Syntax_Syntax.pos
                                     in
                                  let c2 =
                                    let uu____7526 =
                                      (FStar_TypeChecker_Env.is_total_effect
                                         env1 ef)
                                        ||
                                        (let uu____7529 =
                                           FStar_All.pipe_right ef
                                             (FStar_TypeChecker_Env.norm_eff_name
                                                env1)
                                            in
                                         FStar_All.pipe_right uu____7529
                                           (FStar_TypeChecker_Env.is_layered_effect
                                              env1))
                                       in
                                    if uu____7526
                                    then
                                      let uu____7532 =
                                        FStar_Syntax_Syntax.mk_Total repr  in
                                      FStar_All.pipe_right uu____7532
                                        FStar_TypeChecker_Common.lcomp_of_comp
                                    else
                                      (let ct =
                                         {
                                           FStar_Syntax_Syntax.comp_univs =
                                             [u_c];
                                           FStar_Syntax_Syntax.effect_name =
                                             FStar_Parser_Const.effect_Dv_lid;
                                           FStar_Syntax_Syntax.result_typ =
                                             repr;
                                           FStar_Syntax_Syntax.effect_args =
                                             [];
                                           FStar_Syntax_Syntax.flags = []
                                         }  in
                                       let uu____7544 =
                                         FStar_Syntax_Syntax.mk_Comp ct  in
                                       FStar_All.pipe_right uu____7544
                                         FStar_TypeChecker_Common.lcomp_of_comp)
                                     in
                                  let uu____7545 =
                                    comp_check_expected_typ env1 e3 c2  in
                                  match uu____7545 with
                                  | (e4,c3,g') ->
                                      let uu____7561 =
                                        let uu____7562 =
                                          FStar_TypeChecker_Env.conj_guard
                                            g_c g'
                                           in
                                        FStar_TypeChecker_Env.conj_guard g
                                          uu____7562
                                         in
                                      (e4, c3, uu____7561))))))))
       | FStar_Syntax_Syntax.Tm_app
           ({
              FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant
                (FStar_Const.Const_reflect l);
              FStar_Syntax_Syntax.pos = uu____7564;
              FStar_Syntax_Syntax.vars = uu____7565;_},(e1,aqual)::[])
           ->
           (if FStar_Option.isSome aqual
            then
              FStar_Errors.log_issue e1.FStar_Syntax_Syntax.pos
                (FStar_Errors.Warning_IrrelevantQualifierOnArgumentToReflect,
                  "Qualifier on argument to reflect is irrelevant and will be ignored")
            else ();
            (let uu____7613 =
               let uu____7615 =
                 FStar_TypeChecker_Env.is_user_reflectable_effect env1 l  in
               Prims.op_Negation uu____7615  in
             if uu____7613
             then
               let uu____7618 =
                 let uu____7624 =
                   FStar_Util.format1 "Effect %s cannot be reflected"
                     l.FStar_Ident.str
                    in
                 (FStar_Errors.Fatal_EffectCannotBeReified, uu____7624)  in
               FStar_Errors.raise_error uu____7618 e1.FStar_Syntax_Syntax.pos
             else ());
            (let uu____7630 = FStar_Syntax_Util.head_and_args top  in
             match uu____7630 with
             | (reflect_op,uu____7654) ->
                 let uu____7679 =
                   FStar_TypeChecker_Env.effect_decl_opt env1 l  in
                 (match uu____7679 with
                  | FStar_Pervasives_Native.None  ->
                      let uu____7700 =
                        let uu____7706 =
                          let uu____7708 = FStar_Ident.string_of_lid l  in
                          FStar_Util.format1
                            "Effect %s not found (for reflect)" uu____7708
                           in
                        (FStar_Errors.Fatal_EffectNotFound, uu____7706)  in
                      FStar_Errors.raise_error uu____7700
                        e1.FStar_Syntax_Syntax.pos
                  | FStar_Pervasives_Native.Some (ed,qualifiers) ->
                      let uu____7730 =
                        FStar_TypeChecker_Env.clear_expected_typ env1  in
                      (match uu____7730 with
                       | (env_no_ex,uu____7744) ->
                           let uu____7749 =
                             let uu____7758 =
                               tc_tot_or_gtot_term env_no_ex e1  in
                             match uu____7758 with
                             | (e2,c,g) ->
                                 ((let uu____7777 =
                                     let uu____7779 =
                                       FStar_TypeChecker_Common.is_total_lcomp
                                         c
                                        in
                                     FStar_All.pipe_left Prims.op_Negation
                                       uu____7779
                                      in
                                   if uu____7777
                                   then
                                     FStar_TypeChecker_Err.add_errors env1
                                       [(FStar_Errors.Error_UnexpectedGTotComputation,
                                          "Expected Tot, got a GTot computation",
                                          (e2.FStar_Syntax_Syntax.pos))]
                                   else ());
                                  (e2, c, g))
                              in
                           (match uu____7749 with
                            | (e2,c_e,g_e) ->
                                let uu____7817 =
                                  let uu____7832 =
                                    FStar_Syntax_Util.type_u ()  in
                                  match uu____7832 with
                                  | (a,u_a) ->
                                      let uu____7853 =
                                        FStar_TypeChecker_Util.new_implicit_var
                                          "" e2.FStar_Syntax_Syntax.pos
                                          env_no_ex a
                                         in
                                      (match uu____7853 with
                                       | (a_uvar,uu____7882,g_a) ->
                                           let uu____7896 =
                                             FStar_TypeChecker_Util.fresh_effect_repr_en
                                               env_no_ex
                                               e2.FStar_Syntax_Syntax.pos l
                                               u_a a_uvar
                                              in
                                           (uu____7896, u_a, a_uvar, g_a))
                                   in
                                (match uu____7817 with
                                 | ((expected_repr_typ,g_repr),u_a,a,g_a) ->
                                     let g_eq =
                                       FStar_TypeChecker_Rel.teq env_no_ex
                                         c_e.FStar_TypeChecker_Common.res_typ
                                         expected_repr_typ
                                        in
                                     let eff_args =
                                       let uu____7938 =
                                         let uu____7939 =
                                           FStar_Syntax_Subst.compress
                                             expected_repr_typ
                                            in
                                         uu____7939.FStar_Syntax_Syntax.n  in
                                       match uu____7938 with
                                       | FStar_Syntax_Syntax.Tm_app
                                           (uu____7952,uu____7953::args) ->
                                           args
                                       | uu____7995 ->
                                           let uu____7996 =
                                             let uu____8002 =
                                               let uu____8004 =
                                                 FStar_Ident.string_of_lid l
                                                  in
                                               let uu____8006 =
                                                 FStar_Syntax_Print.tag_of_term
                                                   expected_repr_typ
                                                  in
                                               let uu____8008 =
                                                 FStar_Syntax_Print.term_to_string
                                                   expected_repr_typ
                                                  in
                                               FStar_Util.format3
                                                 "Expected repr type for %s is not an application node (%s:%s)"
                                                 uu____8004 uu____8006
                                                 uu____8008
                                                in
                                             (FStar_Errors.Fatal_UnexpectedEffect,
                                               uu____8002)
                                              in
                                           FStar_Errors.raise_error
                                             uu____7996
                                             top.FStar_Syntax_Syntax.pos
                                        in
                                     let c =
                                       let uu____8023 =
                                         FStar_Syntax_Syntax.mk_Comp
                                           {
                                             FStar_Syntax_Syntax.comp_univs =
                                               [u_a];
                                             FStar_Syntax_Syntax.effect_name
                                               =
                                               (ed.FStar_Syntax_Syntax.mname);
                                             FStar_Syntax_Syntax.result_typ =
                                               a;
                                             FStar_Syntax_Syntax.effect_args
                                               = eff_args;
                                             FStar_Syntax_Syntax.flags = []
                                           }
                                          in
                                       FStar_All.pipe_right uu____8023
                                         FStar_TypeChecker_Common.lcomp_of_comp
                                        in
                                     let e3 =
                                       FStar_Syntax_Syntax.mk
                                         (FStar_Syntax_Syntax.Tm_app
                                            (reflect_op, [(e2, aqual)]))
                                         FStar_Pervasives_Native.None
                                         top.FStar_Syntax_Syntax.pos
                                        in
                                     let uu____8059 =
                                       comp_check_expected_typ env1 e3 c  in
                                     (match uu____8059 with
                                      | (e4,c1,g') ->
                                          let e5 =
                                            FStar_Syntax_Syntax.mk
                                              (FStar_Syntax_Syntax.Tm_meta
                                                 (e4,
                                                   (FStar_Syntax_Syntax.Meta_monadic
                                                      ((c1.FStar_TypeChecker_Common.eff_name),
                                                        (c1.FStar_TypeChecker_Common.res_typ)))))
                                              FStar_Pervasives_Native.None
                                              e4.FStar_Syntax_Syntax.pos
                                             in
                                          let uu____8082 =
                                            FStar_TypeChecker_Env.conj_guards
                                              [g_e; g_repr; g_a; g_eq; g']
                                             in
                                          (e5, c1, uu____8082))))))))
       | FStar_Syntax_Syntax.Tm_app
           (head1,(tau,FStar_Pervasives_Native.None )::[]) when
           (FStar_Syntax_Util.is_synth_by_tactic head1) &&
             (Prims.op_Negation env1.FStar_TypeChecker_Env.phase1)
           ->
           let uu____8121 = FStar_Syntax_Util.head_and_args top  in
           (match uu____8121 with
            | (head2,args) ->
                tc_synth head2 env1 args top.FStar_Syntax_Syntax.pos)
       | FStar_Syntax_Syntax.Tm_app
           (head1,(uu____8171,FStar_Pervasives_Native.Some
                   (FStar_Syntax_Syntax.Implicit uu____8172))::(tau,FStar_Pervasives_Native.None
                                                                )::[])
           when
           (FStar_Syntax_Util.is_synth_by_tactic head1) &&
             (Prims.op_Negation env1.FStar_TypeChecker_Env.phase1)
           ->
           let uu____8225 = FStar_Syntax_Util.head_and_args top  in
           (match uu____8225 with
            | (head2,args) ->
                tc_synth head2 env1 args top.FStar_Syntax_Syntax.pos)
       | FStar_Syntax_Syntax.Tm_app (head1,args) when
           (FStar_Syntax_Util.is_synth_by_tactic head1) &&
             (Prims.op_Negation env1.FStar_TypeChecker_Env.phase1)
           ->
           let uu____8300 =
             match args with
             | (tau,FStar_Pervasives_Native.None )::rest ->
                 ([(tau, FStar_Pervasives_Native.None)], rest)
             | (a,FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Implicit
                b))::(tau,FStar_Pervasives_Native.None )::rest ->
                 ([(a,
                     (FStar_Pervasives_Native.Some
                        (FStar_Syntax_Syntax.Implicit b)));
                  (tau, FStar_Pervasives_Native.None)], rest)
             | uu____8510 ->
                 FStar_Errors.raise_error
                   (FStar_Errors.Fatal_SynthByTacticError,
                     "synth_by_tactic: bad application")
                   top.FStar_Syntax_Syntax.pos
              in
           (match uu____8300 with
            | (args1,args2) ->
                let t1 = FStar_Syntax_Util.mk_app head1 args1  in
                let t2 = FStar_Syntax_Util.mk_app t1 args2  in
                tc_term env1 t2)
       | FStar_Syntax_Syntax.Tm_app (head1,args) ->
           let env0 = env1  in
           let env2 =
             let uu____8629 =
               let uu____8630 = FStar_TypeChecker_Env.clear_expected_typ env1
                  in
               FStar_All.pipe_right uu____8630 FStar_Pervasives_Native.fst
                in
             FStar_All.pipe_right uu____8629 instantiate_both  in
           ((let uu____8646 =
               FStar_TypeChecker_Env.debug env2 FStar_Options.High  in
             if uu____8646
             then
               let uu____8649 =
                 FStar_Range.string_of_range top.FStar_Syntax_Syntax.pos  in
               let uu____8651 = FStar_Syntax_Print.term_to_string top  in
               let uu____8653 =
                 let uu____8655 = FStar_TypeChecker_Env.expected_typ env0  in
                 FStar_All.pipe_right uu____8655
                   (fun uu___3_8662  ->
                      match uu___3_8662 with
                      | FStar_Pervasives_Native.None  -> "none"
                      | FStar_Pervasives_Native.Some t ->
                          FStar_Syntax_Print.term_to_string t)
                  in
               FStar_Util.print3
                 "(%s) Checking app %s, expected type is %s\n" uu____8649
                 uu____8651 uu____8653
             else ());
            (let uu____8671 = tc_term (no_inst env2) head1  in
             match uu____8671 with
             | (head2,chead,g_head) ->
                 let uu____8687 =
                   let uu____8692 = FStar_TypeChecker_Common.lcomp_comp chead
                      in
                   FStar_All.pipe_right uu____8692
                     (fun uu____8709  ->
                        match uu____8709 with
                        | (c,g) ->
                            let uu____8720 =
                              FStar_TypeChecker_Env.conj_guard g_head g  in
                            (c, uu____8720))
                    in
                 (match uu____8687 with
                  | (chead1,g_head1) ->
                      let uu____8729 =
                        let uu____8736 =
                          ((Prims.op_Negation env2.FStar_TypeChecker_Env.lax)
                             &&
                             (let uu____8739 = FStar_Options.lax ()  in
                              Prims.op_Negation uu____8739))
                            &&
                            (FStar_TypeChecker_Util.short_circuit_head head2)
                           in
                        if uu____8736
                        then
                          let uu____8748 =
                            let uu____8755 =
                              FStar_TypeChecker_Env.expected_typ env0  in
                            check_short_circuit_args env2 head2 chead1
                              g_head1 args uu____8755
                             in
                          match uu____8748 with | (e1,c,g) -> (e1, c, g)
                        else
                          (let uu____8769 =
                             FStar_TypeChecker_Env.expected_typ env0  in
                           check_application_args env2 head2 chead1 g_head1
                             args uu____8769)
                         in
                      (match uu____8729 with
                       | (e1,c,g) ->
                           let uu____8781 =
                             let uu____8788 =
                               FStar_TypeChecker_Common.is_tot_or_gtot_lcomp
                                 c
                                in
                             if uu____8788
                             then
                               let uu____8797 =
                                 FStar_TypeChecker_Util.maybe_instantiate
                                   env0 e1 c.FStar_TypeChecker_Common.res_typ
                                  in
                               match uu____8797 with
                               | (e2,res_typ,implicits) ->
                                   let uu____8813 =
                                     FStar_TypeChecker_Common.set_result_typ_lc
                                       c res_typ
                                      in
                                   (e2, uu____8813, implicits)
                             else
                               (e1, c, FStar_TypeChecker_Env.trivial_guard)
                              in
                           (match uu____8781 with
                            | (e2,c1,implicits) ->
                                ((let uu____8826 =
                                    FStar_TypeChecker_Env.debug env2
                                      FStar_Options.Extreme
                                     in
                                  if uu____8826
                                  then
                                    let uu____8829 =
                                      FStar_TypeChecker_Rel.print_pending_implicits
                                        g
                                       in
                                    FStar_Util.print1
                                      "Introduced {%s} implicits in application\n"
                                      uu____8829
                                  else ());
                                 (let uu____8834 =
                                    comp_check_expected_typ env0 e2 c1  in
                                  match uu____8834 with
                                  | (e3,c2,g') ->
                                      let gres =
                                        FStar_TypeChecker_Env.conj_guard g g'
                                         in
                                      let gres1 =
                                        FStar_TypeChecker_Env.conj_guard gres
                                          implicits
                                         in
                                      ((let uu____8853 =
                                          FStar_TypeChecker_Env.debug env2
                                            FStar_Options.Extreme
                                           in
                                        if uu____8853
                                        then
                                          let uu____8856 =
                                            FStar_Syntax_Print.term_to_string
                                              e3
                                             in
                                          let uu____8858 =
                                            FStar_TypeChecker_Rel.guard_to_string
                                              env2 gres1
                                             in
                                          FStar_Util.print2
                                            "Guard from application node %s is %s\n"
                                            uu____8856 uu____8858
                                        else ());
                                       (e3, c2, gres1)))))))))
       | FStar_Syntax_Syntax.Tm_match uu____8863 -> tc_match env1 top
       | FStar_Syntax_Syntax.Tm_let
           ((false
             ,{ FStar_Syntax_Syntax.lbname = FStar_Util.Inr uu____8886;
                FStar_Syntax_Syntax.lbunivs = uu____8887;
                FStar_Syntax_Syntax.lbtyp = uu____8888;
                FStar_Syntax_Syntax.lbeff = uu____8889;
                FStar_Syntax_Syntax.lbdef = uu____8890;
                FStar_Syntax_Syntax.lbattrs = uu____8891;
                FStar_Syntax_Syntax.lbpos = uu____8892;_}::[]),uu____8893)
           -> check_top_level_let env1 top
       | FStar_Syntax_Syntax.Tm_let ((false ,uu____8919),uu____8920) ->
           check_inner_let env1 top
       | FStar_Syntax_Syntax.Tm_let
           ((true
             ,{ FStar_Syntax_Syntax.lbname = FStar_Util.Inr uu____8938;
                FStar_Syntax_Syntax.lbunivs = uu____8939;
                FStar_Syntax_Syntax.lbtyp = uu____8940;
                FStar_Syntax_Syntax.lbeff = uu____8941;
                FStar_Syntax_Syntax.lbdef = uu____8942;
                FStar_Syntax_Syntax.lbattrs = uu____8943;
                FStar_Syntax_Syntax.lbpos = uu____8944;_}::uu____8945),uu____8946)
           -> check_top_level_let_rec env1 top
       | FStar_Syntax_Syntax.Tm_let ((true ,uu____8974),uu____8975) ->
           check_inner_let_rec env1 top)

and (tc_match :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term ->
      (FStar_Syntax_Syntax.term * FStar_TypeChecker_Common.lcomp *
        FStar_TypeChecker_Common.guard_t))
  =
  fun env  ->
    fun top  ->
      let uu____9001 =
        let uu____9002 = FStar_Syntax_Subst.compress top  in
        uu____9002.FStar_Syntax_Syntax.n  in
      match uu____9001 with
      | FStar_Syntax_Syntax.Tm_match (e1,eqns) ->
          let uu____9049 = FStar_TypeChecker_Env.clear_expected_typ env  in
          (match uu____9049 with
           | (env1,topt) ->
               let env11 = instantiate_both env1  in
               let uu____9069 = tc_term env11 e1  in
               (match uu____9069 with
                | (e11,c1,g1) ->
                    let uu____9085 =
                      let uu____9096 =
                        FStar_TypeChecker_Util.coerce_views env e11 c1  in
                      match uu____9096 with
                      | FStar_Pervasives_Native.Some (e12,c11) ->
                          (e12, c11, eqns)
                      | FStar_Pervasives_Native.None  -> (e11, c1, eqns)  in
                    (match uu____9085 with
                     | (e12,c11,eqns1) ->
                         let eqns2 = eqns1  in
                         let uu____9151 =
                           match topt with
                           | FStar_Pervasives_Native.Some t -> (env, t, g1)
                           | FStar_Pervasives_Native.None  ->
                               let uu____9165 = FStar_Syntax_Util.type_u ()
                                  in
                               (match uu____9165 with
                                | (k,uu____9177) ->
                                    let uu____9178 =
                                      FStar_TypeChecker_Util.new_implicit_var
                                        "match result"
                                        e12.FStar_Syntax_Syntax.pos env k
                                       in
                                    (match uu____9178 with
                                     | (res_t,uu____9199,g) ->
                                         let uu____9213 =
                                           FStar_TypeChecker_Env.set_expected_typ
                                             env res_t
                                            in
                                         let uu____9214 =
                                           FStar_TypeChecker_Env.conj_guard
                                             g1 g
                                            in
                                         (uu____9213, res_t, uu____9214)))
                            in
                         (match uu____9151 with
                          | (env_branches,res_t,g11) ->
                              ((let uu____9225 =
                                  FStar_TypeChecker_Env.debug env
                                    FStar_Options.Extreme
                                   in
                                if uu____9225
                                then
                                  let uu____9228 =
                                    FStar_Syntax_Print.term_to_string res_t
                                     in
                                  FStar_Util.print1
                                    "Tm_match: expected type of branches is %s\n"
                                    uu____9228
                                else ());
                               (let guard_x =
                                  FStar_Syntax_Syntax.new_bv
                                    (FStar_Pervasives_Native.Some
                                       (e12.FStar_Syntax_Syntax.pos))
                                    c11.FStar_TypeChecker_Common.res_typ
                                   in
                                let t_eqns =
                                  FStar_All.pipe_right eqns2
                                    (FStar_List.map
                                       (tc_eqn guard_x env_branches))
                                   in
                                let uu____9336 =
                                  let uu____9344 =
                                    FStar_List.fold_right
                                      (fun uu____9437  ->
                                         fun uu____9438  ->
                                           match (uu____9437, uu____9438)
                                           with
                                           | ((branch1,f,eff_label,cflags,c,g,erasable_branch),
                                              (caccum,gaccum,erasable1)) ->
                                               let uu____9710 =
                                                 FStar_TypeChecker_Env.conj_guard
                                                   g gaccum
                                                  in
                                               (((f, eff_label, cflags, c) ::
                                                 caccum), uu____9710,
                                                 (erasable1 ||
                                                    erasable_branch))) t_eqns
                                      ([],
                                        FStar_TypeChecker_Env.trivial_guard,
                                        false)
                                     in
                                  match uu____9344 with
                                  | (cases,g,erasable1) ->
                                      let uu____9824 =
                                        let uu____9825 =
                                          let uu____9826 =
                                            let uu____9827 =
                                              FStar_All.pipe_right guard_x
                                                FStar_Syntax_Syntax.mk_binder
                                               in
                                            [uu____9827]  in
                                          FStar_TypeChecker_Env.push_binders
                                            env uu____9826
                                           in
                                        FStar_TypeChecker_Util.bind_cases
                                          uu____9825 res_t cases
                                         in
                                      (uu____9824, g, erasable1)
                                   in
                                match uu____9336 with
                                | (c_branches,g_branches,erasable1) ->
                                    let cres =
                                      FStar_TypeChecker_Util.bind
                                        e12.FStar_Syntax_Syntax.pos env
                                        (FStar_Pervasives_Native.Some e12)
                                        c11
                                        ((FStar_Pervasives_Native.Some
                                            guard_x), c_branches)
                                       in
                                    let cres1 =
                                      if erasable1
                                      then
                                        let e =
                                          FStar_Syntax_Util.exp_true_bool  in
                                        let c =
                                          FStar_Syntax_Syntax.mk_GTotal'
                                            FStar_Syntax_Util.t_bool
                                            (FStar_Pervasives_Native.Some
                                               FStar_Syntax_Syntax.U_zero)
                                           in
                                        let uu____9871 =
                                          FStar_TypeChecker_Common.lcomp_of_comp
                                            c
                                           in
                                        FStar_TypeChecker_Util.bind
                                          e.FStar_Syntax_Syntax.pos env
                                          (FStar_Pervasives_Native.Some e)
                                          uu____9871
                                          (FStar_Pervasives_Native.None,
                                            cres)
                                      else cres  in
                                    let e =
                                      let mk_match scrutinee =
                                        let branches =
                                          FStar_All.pipe_right t_eqns
                                            (FStar_List.map
                                               (fun uu____10013  ->
                                                  match uu____10013 with
                                                  | ((pat,wopt,br),uu____10061,eff_label,uu____10063,uu____10064,uu____10065,uu____10066)
                                                      ->
                                                      let uu____10105 =
                                                        FStar_TypeChecker_Util.maybe_lift
                                                          env br eff_label
                                                          cres1.FStar_TypeChecker_Common.eff_name
                                                          res_t
                                                         in
                                                      (pat, wopt,
                                                        uu____10105)))
                                           in
                                        let e =
                                          FStar_Syntax_Syntax.mk
                                            (FStar_Syntax_Syntax.Tm_match
                                               (scrutinee, branches))
                                            FStar_Pervasives_Native.None
                                            top.FStar_Syntax_Syntax.pos
                                           in
                                        let e2 =
                                          FStar_TypeChecker_Util.maybe_monadic
                                            env e
                                            cres1.FStar_TypeChecker_Common.eff_name
                                            cres1.FStar_TypeChecker_Common.res_typ
                                           in
                                        FStar_Syntax_Syntax.mk
                                          (FStar_Syntax_Syntax.Tm_ascribed
                                             (e2,
                                               ((FStar_Util.Inl
                                                   (cres1.FStar_TypeChecker_Common.res_typ)),
                                                 FStar_Pervasives_Native.None),
                                               (FStar_Pervasives_Native.Some
                                                  (cres1.FStar_TypeChecker_Common.eff_name))))
                                          FStar_Pervasives_Native.None
                                          e2.FStar_Syntax_Syntax.pos
                                         in
                                      let uu____10172 =
                                        FStar_TypeChecker_Util.is_pure_or_ghost_effect
                                          env
                                          c11.FStar_TypeChecker_Common.eff_name
                                         in
                                      if uu____10172
                                      then mk_match e12
                                      else
                                        (let e_match =
                                           let uu____10180 =
                                             FStar_Syntax_Syntax.bv_to_name
                                               guard_x
                                              in
                                           mk_match uu____10180  in
                                         let lb =
                                           let uu____10184 =
                                             FStar_TypeChecker_Env.norm_eff_name
                                               env
                                               c11.FStar_TypeChecker_Common.eff_name
                                              in
                                           FStar_Syntax_Util.mk_letbinding
                                             (FStar_Util.Inl guard_x) []
                                             c11.FStar_TypeChecker_Common.res_typ
                                             uu____10184 e12 []
                                             e12.FStar_Syntax_Syntax.pos
                                            in
                                         let e =
                                           let uu____10190 =
                                             let uu____10197 =
                                               let uu____10198 =
                                                 let uu____10212 =
                                                   let uu____10215 =
                                                     let uu____10216 =
                                                       FStar_Syntax_Syntax.mk_binder
                                                         guard_x
                                                        in
                                                     [uu____10216]  in
                                                   FStar_Syntax_Subst.close
                                                     uu____10215 e_match
                                                    in
                                                 ((false, [lb]), uu____10212)
                                                  in
                                               FStar_Syntax_Syntax.Tm_let
                                                 uu____10198
                                                in
                                             FStar_Syntax_Syntax.mk
                                               uu____10197
                                              in
                                           uu____10190
                                             FStar_Pervasives_Native.None
                                             top.FStar_Syntax_Syntax.pos
                                            in
                                         FStar_TypeChecker_Util.maybe_monadic
                                           env e
                                           cres1.FStar_TypeChecker_Common.eff_name
                                           cres1.FStar_TypeChecker_Common.res_typ)
                                       in
                                    ((let uu____10249 =
                                        FStar_TypeChecker_Env.debug env
                                          FStar_Options.Extreme
                                         in
                                      if uu____10249
                                      then
                                        let uu____10252 =
                                          FStar_Range.string_of_range
                                            top.FStar_Syntax_Syntax.pos
                                           in
                                        let uu____10254 =
                                          FStar_TypeChecker_Common.lcomp_to_string
                                            cres1
                                           in
                                        FStar_Util.print2
                                          "(%s) Typechecked Tm_match, comp type = %s\n"
                                          uu____10252 uu____10254
                                      else ());
                                     (let uu____10259 =
                                        FStar_TypeChecker_Env.conj_guard g11
                                          g_branches
                                         in
                                      (e, cres1, uu____10259)))))))))
      | uu____10260 ->
          let uu____10261 =
            let uu____10263 = FStar_Syntax_Print.tag_of_term top  in
            FStar_Util.format1 "tc_match called on %s\n" uu____10263  in
          failwith uu____10261

and (tc_synth :
  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
    FStar_TypeChecker_Env.env ->
      (FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax *
        FStar_Syntax_Syntax.arg_qualifier FStar_Pervasives_Native.option)
        Prims.list ->
        FStar_Range.range ->
          (FStar_Syntax_Syntax.term * FStar_TypeChecker_Common.lcomp *
            FStar_TypeChecker_Common.guard_t))
  =
  fun head1  ->
    fun env  ->
      fun args  ->
        fun rng  ->
          let uu____10288 =
            match args with
            | (tau,FStar_Pervasives_Native.None )::[] ->
                (tau, FStar_Pervasives_Native.None)
            | (a,FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Implicit
               uu____10327))::(tau,FStar_Pervasives_Native.None )::[] ->
                (tau, (FStar_Pervasives_Native.Some a))
            | uu____10368 ->
                FStar_Errors.raise_error
                  (FStar_Errors.Fatal_SynthByTacticError,
                    "synth_by_tactic: bad application") rng
             in
          match uu____10288 with
          | (tau,atyp) ->
              let typ =
                match atyp with
                | FStar_Pervasives_Native.Some t -> t
                | FStar_Pervasives_Native.None  ->
                    let uu____10401 = FStar_TypeChecker_Env.expected_typ env
                       in
                    (match uu____10401 with
                     | FStar_Pervasives_Native.Some t -> t
                     | FStar_Pervasives_Native.None  ->
                         let uu____10405 =
                           FStar_TypeChecker_Env.get_range env  in
                         FStar_Errors.raise_error
                           (FStar_Errors.Fatal_SynthByTacticError,
                             "synth_by_tactic: need a type annotation when no expected type is present")
                           uu____10405)
                 in
              let uu____10408 =
                let uu____10415 =
                  let uu____10416 =
                    let uu____10417 = FStar_Syntax_Util.type_u ()  in
                    FStar_All.pipe_left FStar_Pervasives_Native.fst
                      uu____10417
                     in
                  FStar_TypeChecker_Env.set_expected_typ env uu____10416  in
                tc_term uu____10415 typ  in
              (match uu____10408 with
               | (typ1,uu____10433,g1) ->
                   (FStar_TypeChecker_Rel.force_trivial_guard env g1;
                    (let uu____10436 =
                       tc_tactic FStar_Syntax_Syntax.t_unit
                         FStar_Syntax_Syntax.t_unit env tau
                        in
                     match uu____10436 with
                     | (tau1,uu____10450,g2) ->
                         (FStar_TypeChecker_Rel.force_trivial_guard env g2;
                          (let t =
                             env.FStar_TypeChecker_Env.synth_hook env typ1
                               (let uu___1324_10455 = tau1  in
                                {
                                  FStar_Syntax_Syntax.n =
                                    (uu___1324_10455.FStar_Syntax_Syntax.n);
                                  FStar_Syntax_Syntax.pos = rng;
                                  FStar_Syntax_Syntax.vars =
                                    (uu___1324_10455.FStar_Syntax_Syntax.vars)
                                })
                              in
                           (let uu____10457 =
                              FStar_All.pipe_left
                                (FStar_TypeChecker_Env.debug env)
                                (FStar_Options.Other "Tac")
                               in
                            if uu____10457
                            then
                              let uu____10462 =
                                FStar_Syntax_Print.term_to_string t  in
                              FStar_Util.print1 "Got %s\n" uu____10462
                            else ());
                           FStar_TypeChecker_Util.check_uvars
                             tau1.FStar_Syntax_Syntax.pos t;
                           (let uu____10468 =
                              let uu____10469 =
                                FStar_Syntax_Syntax.mk_Total typ1  in
                              FStar_All.pipe_left
                                FStar_TypeChecker_Common.lcomp_of_comp
                                uu____10469
                               in
                            (t, uu____10468,
                              FStar_TypeChecker_Env.trivial_guard)))))))

and (tc_tactic :
  FStar_Syntax_Syntax.typ ->
    FStar_Syntax_Syntax.typ ->
      FStar_TypeChecker_Env.env ->
        FStar_Syntax_Syntax.term ->
          (FStar_Syntax_Syntax.term * FStar_TypeChecker_Common.lcomp *
            FStar_TypeChecker_Common.guard_t))
  =
  fun a  ->
    fun b  ->
      fun env  ->
        fun tau  ->
          let env1 =
            let uu___1334_10475 = env  in
            {
              FStar_TypeChecker_Env.solver =
                (uu___1334_10475.FStar_TypeChecker_Env.solver);
              FStar_TypeChecker_Env.range =
                (uu___1334_10475.FStar_TypeChecker_Env.range);
              FStar_TypeChecker_Env.curmodule =
                (uu___1334_10475.FStar_TypeChecker_Env.curmodule);
              FStar_TypeChecker_Env.gamma =
                (uu___1334_10475.FStar_TypeChecker_Env.gamma);
              FStar_TypeChecker_Env.gamma_sig =
                (uu___1334_10475.FStar_TypeChecker_Env.gamma_sig);
              FStar_TypeChecker_Env.gamma_cache =
                (uu___1334_10475.FStar_TypeChecker_Env.gamma_cache);
              FStar_TypeChecker_Env.modules =
                (uu___1334_10475.FStar_TypeChecker_Env.modules);
              FStar_TypeChecker_Env.expected_typ =
                (uu___1334_10475.FStar_TypeChecker_Env.expected_typ);
              FStar_TypeChecker_Env.sigtab =
                (uu___1334_10475.FStar_TypeChecker_Env.sigtab);
              FStar_TypeChecker_Env.attrtab =
                (uu___1334_10475.FStar_TypeChecker_Env.attrtab);
              FStar_TypeChecker_Env.instantiate_imp =
                (uu___1334_10475.FStar_TypeChecker_Env.instantiate_imp);
              FStar_TypeChecker_Env.effects =
                (uu___1334_10475.FStar_TypeChecker_Env.effects);
              FStar_TypeChecker_Env.generalize =
                (uu___1334_10475.FStar_TypeChecker_Env.generalize);
              FStar_TypeChecker_Env.letrecs =
                (uu___1334_10475.FStar_TypeChecker_Env.letrecs);
              FStar_TypeChecker_Env.top_level =
                (uu___1334_10475.FStar_TypeChecker_Env.top_level);
              FStar_TypeChecker_Env.check_uvars =
                (uu___1334_10475.FStar_TypeChecker_Env.check_uvars);
              FStar_TypeChecker_Env.use_eq =
                (uu___1334_10475.FStar_TypeChecker_Env.use_eq);
              FStar_TypeChecker_Env.is_iface =
                (uu___1334_10475.FStar_TypeChecker_Env.is_iface);
              FStar_TypeChecker_Env.admit =
                (uu___1334_10475.FStar_TypeChecker_Env.admit);
              FStar_TypeChecker_Env.lax =
                (uu___1334_10475.FStar_TypeChecker_Env.lax);
              FStar_TypeChecker_Env.lax_universes =
                (uu___1334_10475.FStar_TypeChecker_Env.lax_universes);
              FStar_TypeChecker_Env.phase1 =
                (uu___1334_10475.FStar_TypeChecker_Env.phase1);
              FStar_TypeChecker_Env.failhard = true;
              FStar_TypeChecker_Env.nosynth =
                (uu___1334_10475.FStar_TypeChecker_Env.nosynth);
              FStar_TypeChecker_Env.uvar_subtyping =
                (uu___1334_10475.FStar_TypeChecker_Env.uvar_subtyping);
              FStar_TypeChecker_Env.tc_term =
                (uu___1334_10475.FStar_TypeChecker_Env.tc_term);
              FStar_TypeChecker_Env.type_of =
                (uu___1334_10475.FStar_TypeChecker_Env.type_of);
              FStar_TypeChecker_Env.universe_of =
                (uu___1334_10475.FStar_TypeChecker_Env.universe_of);
              FStar_TypeChecker_Env.check_type_of =
                (uu___1334_10475.FStar_TypeChecker_Env.check_type_of);
              FStar_TypeChecker_Env.use_bv_sorts =
                (uu___1334_10475.FStar_TypeChecker_Env.use_bv_sorts);
              FStar_TypeChecker_Env.qtbl_name_and_index =
                (uu___1334_10475.FStar_TypeChecker_Env.qtbl_name_and_index);
              FStar_TypeChecker_Env.normalized_eff_names =
                (uu___1334_10475.FStar_TypeChecker_Env.normalized_eff_names);
              FStar_TypeChecker_Env.fv_delta_depths =
                (uu___1334_10475.FStar_TypeChecker_Env.fv_delta_depths);
              FStar_TypeChecker_Env.proof_ns =
                (uu___1334_10475.FStar_TypeChecker_Env.proof_ns);
              FStar_TypeChecker_Env.synth_hook =
                (uu___1334_10475.FStar_TypeChecker_Env.synth_hook);
              FStar_TypeChecker_Env.splice =
                (uu___1334_10475.FStar_TypeChecker_Env.splice);
              FStar_TypeChecker_Env.mpreprocess =
                (uu___1334_10475.FStar_TypeChecker_Env.mpreprocess);
              FStar_TypeChecker_Env.postprocess =
                (uu___1334_10475.FStar_TypeChecker_Env.postprocess);
              FStar_TypeChecker_Env.is_native_tactic =
                (uu___1334_10475.FStar_TypeChecker_Env.is_native_tactic);
              FStar_TypeChecker_Env.identifier_info =
                (uu___1334_10475.FStar_TypeChecker_Env.identifier_info);
              FStar_TypeChecker_Env.tc_hooks =
                (uu___1334_10475.FStar_TypeChecker_Env.tc_hooks);
              FStar_TypeChecker_Env.dsenv =
                (uu___1334_10475.FStar_TypeChecker_Env.dsenv);
              FStar_TypeChecker_Env.nbe =
                (uu___1334_10475.FStar_TypeChecker_Env.nbe);
              FStar_TypeChecker_Env.strict_args_tab =
                (uu___1334_10475.FStar_TypeChecker_Env.strict_args_tab);
              FStar_TypeChecker_Env.erasable_types_tab =
                (uu___1334_10475.FStar_TypeChecker_Env.erasable_types_tab)
            }  in
          let uu____10477 = FStar_Syntax_Syntax.t_tac_of a b  in
          tc_check_tot_or_gtot_term env1 tau uu____10477

and (tc_tactic_opt :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax
      FStar_Pervasives_Native.option ->
      (FStar_Syntax_Syntax.term FStar_Pervasives_Native.option *
        FStar_TypeChecker_Common.guard_t))
  =
  fun env  ->
    fun topt  ->
      match topt with
      | FStar_Pervasives_Native.None  ->
          (FStar_Pervasives_Native.None, FStar_TypeChecker_Env.trivial_guard)
      | FStar_Pervasives_Native.Some tactic ->
          let uu____10499 =
            tc_tactic FStar_Syntax_Syntax.t_unit FStar_Syntax_Syntax.t_unit
              env tactic
             in
          (match uu____10499 with
           | (tactic1,uu____10513,g) ->
               ((FStar_Pervasives_Native.Some tactic1), g))

and (tc_value :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term ->
      (FStar_Syntax_Syntax.term * FStar_TypeChecker_Common.lcomp *
        FStar_TypeChecker_Common.guard_t))
  =
  fun env  ->
    fun e  ->
      let check_instantiated_fvar env1 v1 dc e1 t0 =
        let uu____10565 = FStar_TypeChecker_Util.maybe_instantiate env1 e1 t0
           in
        match uu____10565 with
        | (e2,t,implicits) ->
            let tc =
              let uu____10586 = FStar_TypeChecker_Env.should_verify env1  in
              if uu____10586
              then FStar_Util.Inl t
              else
                (let uu____10595 =
                   let uu____10596 = FStar_Syntax_Syntax.mk_Total t  in
                   FStar_All.pipe_left FStar_TypeChecker_Common.lcomp_of_comp
                     uu____10596
                    in
                 FStar_Util.Inr uu____10595)
               in
            let is_data_ctor uu___4_10605 =
              match uu___4_10605 with
              | FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Data_ctor )
                  -> true
              | FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Record_ctor
                  uu____10610) -> true
              | uu____10618 -> false  in
            let uu____10622 =
              (is_data_ctor dc) &&
                (let uu____10625 =
                   FStar_TypeChecker_Env.is_datacon env1
                     v1.FStar_Syntax_Syntax.v
                    in
                 Prims.op_Negation uu____10625)
               in
            if uu____10622
            then
              let uu____10634 =
                let uu____10640 =
                  FStar_Util.format1 "Expected a data constructor; got %s"
                    (v1.FStar_Syntax_Syntax.v).FStar_Ident.str
                   in
                (FStar_Errors.Fatal_MissingDataConstructor, uu____10640)  in
              let uu____10644 = FStar_TypeChecker_Env.get_range env1  in
              FStar_Errors.raise_error uu____10634 uu____10644
            else value_check_expected_typ env1 e2 tc implicits
         in
      let env1 =
        FStar_TypeChecker_Env.set_range env e.FStar_Syntax_Syntax.pos  in
      let top = FStar_Syntax_Subst.compress e  in
      match top.FStar_Syntax_Syntax.n with
      | FStar_Syntax_Syntax.Tm_bvar x ->
          let uu____10662 =
            let uu____10668 =
              let uu____10670 = FStar_Syntax_Print.term_to_string top  in
              FStar_Util.format1
                "Violation of locally nameless convention: %s" uu____10670
               in
            (FStar_Errors.Error_IllScopedTerm, uu____10668)  in
          FStar_Errors.raise_error uu____10662 top.FStar_Syntax_Syntax.pos
      | FStar_Syntax_Syntax.Tm_uvar (u,s) ->
          let uu____10698 =
            let uu____10703 =
              FStar_Syntax_Subst.subst' s u.FStar_Syntax_Syntax.ctx_uvar_typ
               in
            FStar_Util.Inl uu____10703  in
          value_check_expected_typ env1 e uu____10698
            FStar_TypeChecker_Env.trivial_guard
      | FStar_Syntax_Syntax.Tm_unknown  ->
          let r = FStar_TypeChecker_Env.get_range env1  in
          let uu____10705 =
            let uu____10718 = FStar_TypeChecker_Env.expected_typ env1  in
            match uu____10718 with
            | FStar_Pervasives_Native.None  ->
                let uu____10733 = FStar_Syntax_Util.type_u ()  in
                (match uu____10733 with
                 | (k,u) ->
                     FStar_TypeChecker_Util.new_implicit_var
                       "type of user-provided implicit term" r env1 k)
            | FStar_Pervasives_Native.Some t ->
                (t, [], FStar_TypeChecker_Env.trivial_guard)
             in
          (match uu____10705 with
           | (t,uu____10771,g0) ->
               let uu____10785 =
                 let uu____10798 =
                   let uu____10800 = FStar_Range.string_of_range r  in
                   Prims.op_Hat "user-provided implicit term at " uu____10800
                    in
                 FStar_TypeChecker_Util.new_implicit_var uu____10798 r env1 t
                  in
               (match uu____10785 with
                | (e1,uu____10810,g1) ->
                    let uu____10824 =
                      let uu____10825 = FStar_Syntax_Syntax.mk_Total t  in
                      FStar_All.pipe_right uu____10825
                        FStar_TypeChecker_Common.lcomp_of_comp
                       in
                    let uu____10826 = FStar_TypeChecker_Env.conj_guard g0 g1
                       in
                    (e1, uu____10824, uu____10826)))
      | FStar_Syntax_Syntax.Tm_name x ->
          let uu____10828 =
            if env1.FStar_TypeChecker_Env.use_bv_sorts
            then
              let uu____10838 = FStar_Syntax_Syntax.range_of_bv x  in
              ((x.FStar_Syntax_Syntax.sort), uu____10838)
            else FStar_TypeChecker_Env.lookup_bv env1 x  in
          (match uu____10828 with
           | (t,rng) ->
               let x1 =
                 FStar_Syntax_Syntax.set_range_of_bv
                   (let uu___1399_10852 = x  in
                    {
                      FStar_Syntax_Syntax.ppname =
                        (uu___1399_10852.FStar_Syntax_Syntax.ppname);
                      FStar_Syntax_Syntax.index =
                        (uu___1399_10852.FStar_Syntax_Syntax.index);
                      FStar_Syntax_Syntax.sort = t
                    }) rng
                  in
               (FStar_TypeChecker_Env.insert_bv_info env1 x1 t;
                (let e1 = FStar_Syntax_Syntax.bv_to_name x1  in
                 let uu____10855 =
                   FStar_TypeChecker_Util.maybe_instantiate env1 e1 t  in
                 match uu____10855 with
                 | (e2,t1,implicits) ->
                     let tc =
                       let uu____10876 =
                         FStar_TypeChecker_Env.should_verify env1  in
                       if uu____10876
                       then FStar_Util.Inl t1
                       else
                         (let uu____10885 =
                            let uu____10886 = FStar_Syntax_Syntax.mk_Total t1
                               in
                            FStar_All.pipe_left
                              FStar_TypeChecker_Common.lcomp_of_comp
                              uu____10886
                             in
                          FStar_Util.Inr uu____10885)
                        in
                     value_check_expected_typ env1 e2 tc implicits)))
      | FStar_Syntax_Syntax.Tm_uinst
          ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar fv;
             FStar_Syntax_Syntax.pos = uu____10888;
             FStar_Syntax_Syntax.vars = uu____10889;_},uu____10890)
          when
          (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.synth_lid) &&
            (Prims.op_Negation env1.FStar_TypeChecker_Env.phase1)
          ->
          let uu____10895 = FStar_TypeChecker_Env.get_range env1  in
          FStar_Errors.raise_error
            (FStar_Errors.Fatal_BadlyInstantiatedSynthByTactic,
              "Badly instantiated synth_by_tactic") uu____10895
      | FStar_Syntax_Syntax.Tm_fvar fv when
          (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.synth_lid) &&
            (Prims.op_Negation env1.FStar_TypeChecker_Env.phase1)
          ->
          let uu____10905 = FStar_TypeChecker_Env.get_range env1  in
          FStar_Errors.raise_error
            (FStar_Errors.Fatal_BadlyInstantiatedSynthByTactic,
              "Badly instantiated synth_by_tactic") uu____10905
      | FStar_Syntax_Syntax.Tm_uinst
          ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar fv;
             FStar_Syntax_Syntax.pos = uu____10915;
             FStar_Syntax_Syntax.vars = uu____10916;_},us)
          ->
          let us1 = FStar_List.map (tc_universe env1) us  in
          let uu____10925 =
            FStar_TypeChecker_Env.lookup_lid env1
              (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
             in
          (match uu____10925 with
           | ((us',t),range) ->
               (if (FStar_List.length us1) <> (FStar_List.length us')
                then
                  (let uu____10949 =
                     let uu____10955 =
                       let uu____10957 = FStar_Syntax_Print.fv_to_string fv
                          in
                       let uu____10959 =
                         FStar_Util.string_of_int (FStar_List.length us1)  in
                       let uu____10961 =
                         FStar_Util.string_of_int (FStar_List.length us')  in
                       FStar_Util.format3
                         "Unexpected number of universe instantiations for \"%s\" (%s vs %s)"
                         uu____10957 uu____10959 uu____10961
                        in
                     (FStar_Errors.Fatal_UnexpectedNumberOfUniverse,
                       uu____10955)
                      in
                   let uu____10965 = FStar_TypeChecker_Env.get_range env1  in
                   FStar_Errors.raise_error uu____10949 uu____10965)
                else
                  FStar_List.iter2
                    (fun u'  ->
                       fun u  ->
                         match u' with
                         | FStar_Syntax_Syntax.U_unif u'' ->
                             FStar_Syntax_Unionfind.univ_change u'' u
                         | uu____10982 -> failwith "Impossible") us' us1;
                (let fv' = FStar_Syntax_Syntax.set_range_of_fv fv range  in
                 FStar_TypeChecker_Env.insert_fv_info env1 fv' t;
                 (let e1 =
                    let uu____10987 =
                      FStar_Syntax_Syntax.mk
                        (FStar_Syntax_Syntax.Tm_fvar fv')
                        FStar_Pervasives_Native.None
                        e.FStar_Syntax_Syntax.pos
                       in
                    FStar_Syntax_Syntax.mk_Tm_uinst uu____10987 us1  in
                  check_instantiated_fvar env1
                    fv'.FStar_Syntax_Syntax.fv_name
                    fv'.FStar_Syntax_Syntax.fv_qual e1 t))))
      | FStar_Syntax_Syntax.Tm_fvar fv ->
          let uu____10989 =
            FStar_TypeChecker_Env.lookup_lid env1
              (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
             in
          (match uu____10989 with
           | ((us,t),range) ->
               ((let uu____11012 =
                   FStar_All.pipe_left (FStar_TypeChecker_Env.debug env1)
                     (FStar_Options.Other "Range")
                    in
                 if uu____11012
                 then
                   let uu____11017 =
                     let uu____11019 = FStar_Syntax_Syntax.lid_of_fv fv  in
                     FStar_Syntax_Print.lid_to_string uu____11019  in
                   let uu____11020 =
                     FStar_Range.string_of_range e.FStar_Syntax_Syntax.pos
                      in
                   let uu____11022 = FStar_Range.string_of_range range  in
                   let uu____11024 = FStar_Range.string_of_use_range range
                      in
                   let uu____11026 = FStar_Syntax_Print.term_to_string t  in
                   FStar_Util.print5
                     "Lookup up fvar %s at location %s (lid range = defined at %s, used at %s); got universes type %s"
                     uu____11017 uu____11020 uu____11022 uu____11024
                     uu____11026
                 else ());
                (let fv' = FStar_Syntax_Syntax.set_range_of_fv fv range  in
                 FStar_TypeChecker_Env.insert_fv_info env1 fv' t;
                 (let e1 =
                    let uu____11034 =
                      FStar_Syntax_Syntax.mk
                        (FStar_Syntax_Syntax.Tm_fvar fv')
                        FStar_Pervasives_Native.None
                        e.FStar_Syntax_Syntax.pos
                       in
                    FStar_Syntax_Syntax.mk_Tm_uinst uu____11034 us  in
                  check_instantiated_fvar env1
                    fv'.FStar_Syntax_Syntax.fv_name
                    fv'.FStar_Syntax_Syntax.fv_qual e1 t))))
      | FStar_Syntax_Syntax.Tm_constant c ->
          let t = tc_constant env1 top.FStar_Syntax_Syntax.pos c  in
          let e1 =
            FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_constant c)
              FStar_Pervasives_Native.None e.FStar_Syntax_Syntax.pos
             in
          value_check_expected_typ env1 e1 (FStar_Util.Inl t)
            FStar_TypeChecker_Env.trivial_guard
      | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
          let uu____11062 = FStar_Syntax_Subst.open_comp bs c  in
          (match uu____11062 with
           | (bs1,c1) ->
               let env0 = env1  in
               let uu____11076 =
                 FStar_TypeChecker_Env.clear_expected_typ env1  in
               (match uu____11076 with
                | (env2,uu____11090) ->
                    let uu____11095 = tc_binders env2 bs1  in
                    (match uu____11095 with
                     | (bs2,env3,g,us) ->
                         let uu____11114 = tc_comp env3 c1  in
                         (match uu____11114 with
                          | (c2,uc,f) ->
                              let e1 =
                                let uu___1479_11133 =
                                  FStar_Syntax_Util.arrow bs2 c2  in
                                {
                                  FStar_Syntax_Syntax.n =
                                    (uu___1479_11133.FStar_Syntax_Syntax.n);
                                  FStar_Syntax_Syntax.pos =
                                    (top.FStar_Syntax_Syntax.pos);
                                  FStar_Syntax_Syntax.vars =
                                    (uu___1479_11133.FStar_Syntax_Syntax.vars)
                                }  in
                              (check_smt_pat env3 e1 bs2 c2;
                               (let u = FStar_Syntax_Syntax.U_max (uc :: us)
                                   in
                                let t =
                                  FStar_Syntax_Syntax.mk
                                    (FStar_Syntax_Syntax.Tm_type u)
                                    FStar_Pervasives_Native.None
                                    top.FStar_Syntax_Syntax.pos
                                   in
                                let g1 =
                                  let uu____11144 =
                                    FStar_TypeChecker_Env.close_guard_univs
                                      us bs2 f
                                     in
                                  FStar_TypeChecker_Env.conj_guard g
                                    uu____11144
                                   in
                                let g2 =
                                  FStar_TypeChecker_Util.close_guard_implicits
                                    env3 false bs2 g1
                                   in
                                value_check_expected_typ env0 e1
                                  (FStar_Util.Inl t) g2))))))
      | FStar_Syntax_Syntax.Tm_type u ->
          let u1 = tc_universe env1 u  in
          let t =
            FStar_Syntax_Syntax.mk
              (FStar_Syntax_Syntax.Tm_type (FStar_Syntax_Syntax.U_succ u1))
              FStar_Pervasives_Native.None top.FStar_Syntax_Syntax.pos
             in
          let e1 =
            FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_type u1)
              FStar_Pervasives_Native.None top.FStar_Syntax_Syntax.pos
             in
          value_check_expected_typ env1 e1 (FStar_Util.Inl t)
            FStar_TypeChecker_Env.trivial_guard
      | FStar_Syntax_Syntax.Tm_refine (x,phi) ->
          let uu____11161 =
            let uu____11166 =
              let uu____11167 = FStar_Syntax_Syntax.mk_binder x  in
              [uu____11167]  in
            FStar_Syntax_Subst.open_term uu____11166 phi  in
          (match uu____11161 with
           | (x1,phi1) ->
               let env0 = env1  in
               let uu____11195 =
                 FStar_TypeChecker_Env.clear_expected_typ env1  in
               (match uu____11195 with
                | (env2,uu____11209) ->
                    let uu____11214 =
                      let uu____11229 = FStar_List.hd x1  in
                      tc_binder env2 uu____11229  in
                    (match uu____11214 with
                     | (x2,env3,f1,u) ->
                         ((let uu____11265 =
                             FStar_TypeChecker_Env.debug env3
                               FStar_Options.High
                              in
                           if uu____11265
                           then
                             let uu____11268 =
                               FStar_Range.string_of_range
                                 top.FStar_Syntax_Syntax.pos
                                in
                             let uu____11270 =
                               FStar_Syntax_Print.term_to_string phi1  in
                             let uu____11272 =
                               FStar_Syntax_Print.bv_to_string
                                 (FStar_Pervasives_Native.fst x2)
                                in
                             FStar_Util.print3
                               "(%s) Checking refinement formula %s; binder is %s\n"
                               uu____11268 uu____11270 uu____11272
                           else ());
                          (let uu____11279 = FStar_Syntax_Util.type_u ()  in
                           match uu____11279 with
                           | (t_phi,uu____11291) ->
                               let uu____11292 =
                                 tc_check_tot_or_gtot_term env3 phi1 t_phi
                                  in
                               (match uu____11292 with
                                | (phi2,uu____11306,f2) ->
                                    let e1 =
                                      let uu___1517_11311 =
                                        FStar_Syntax_Util.refine
                                          (FStar_Pervasives_Native.fst x2)
                                          phi2
                                         in
                                      {
                                        FStar_Syntax_Syntax.n =
                                          (uu___1517_11311.FStar_Syntax_Syntax.n);
                                        FStar_Syntax_Syntax.pos =
                                          (top.FStar_Syntax_Syntax.pos);
                                        FStar_Syntax_Syntax.vars =
                                          (uu___1517_11311.FStar_Syntax_Syntax.vars)
                                      }  in
                                    let t =
                                      FStar_Syntax_Syntax.mk
                                        (FStar_Syntax_Syntax.Tm_type u)
                                        FStar_Pervasives_Native.None
                                        top.FStar_Syntax_Syntax.pos
                                       in
                                    let g =
                                      let uu____11320 =
                                        FStar_TypeChecker_Env.close_guard_univs
                                          [u] [x2] f2
                                         in
                                      FStar_TypeChecker_Env.conj_guard f1
                                        uu____11320
                                       in
                                    let g1 =
                                      FStar_TypeChecker_Util.close_guard_implicits
                                        env3 false [x2] g
                                       in
                                    value_check_expected_typ env0 e1
                                      (FStar_Util.Inl t) g1))))))
      | FStar_Syntax_Syntax.Tm_abs (bs,body,uu____11349) ->
          let bs1 = FStar_TypeChecker_Util.maybe_add_implicit_binders env1 bs
             in
          ((let uu____11376 =
              FStar_TypeChecker_Env.debug env1 FStar_Options.Medium  in
            if uu____11376
            then
              let uu____11379 =
                FStar_Syntax_Print.term_to_string
                  (let uu___1530_11383 = top  in
                   {
                     FStar_Syntax_Syntax.n =
                       (FStar_Syntax_Syntax.Tm_abs
                          (bs1, body, FStar_Pervasives_Native.None));
                     FStar_Syntax_Syntax.pos =
                       (uu___1530_11383.FStar_Syntax_Syntax.pos);
                     FStar_Syntax_Syntax.vars =
                       (uu___1530_11383.FStar_Syntax_Syntax.vars)
                   })
                 in
              FStar_Util.print1 "Abstraction is: %s\n" uu____11379
            else ());
           (let uu____11399 = FStar_Syntax_Subst.open_term bs1 body  in
            match uu____11399 with | (bs2,body1) -> tc_abs env1 top bs2 body1))
      | uu____11412 ->
          let uu____11413 =
            let uu____11415 = FStar_Syntax_Print.term_to_string top  in
            let uu____11417 = FStar_Syntax_Print.tag_of_term top  in
            FStar_Util.format2 "Unexpected value: %s (%s)" uu____11415
              uu____11417
             in
          failwith uu____11413

and (tc_constant :
  FStar_TypeChecker_Env.env ->
    FStar_Range.range -> FStar_Const.sconst -> FStar_Syntax_Syntax.typ)
  =
  fun env  ->
    fun r  ->
      fun c  ->
        match c with
        | FStar_Const.Const_unit  -> FStar_Syntax_Syntax.t_unit
        | FStar_Const.Const_bool uu____11429 -> FStar_Syntax_Util.t_bool
        | FStar_Const.Const_int (uu____11431,FStar_Pervasives_Native.None )
            -> FStar_Syntax_Syntax.t_int
        | FStar_Const.Const_int
            (uu____11444,FStar_Pervasives_Native.Some msize) ->
            FStar_Syntax_Syntax.tconst
              (match msize with
               | (FStar_Const.Signed ,FStar_Const.Int8 ) ->
                   FStar_Parser_Const.int8_lid
               | (FStar_Const.Signed ,FStar_Const.Int16 ) ->
                   FStar_Parser_Const.int16_lid
               | (FStar_Const.Signed ,FStar_Const.Int32 ) ->
                   FStar_Parser_Const.int32_lid
               | (FStar_Const.Signed ,FStar_Const.Int64 ) ->
                   FStar_Parser_Const.int64_lid
               | (FStar_Const.Unsigned ,FStar_Const.Int8 ) ->
                   FStar_Parser_Const.uint8_lid
               | (FStar_Const.Unsigned ,FStar_Const.Int16 ) ->
                   FStar_Parser_Const.uint16_lid
               | (FStar_Const.Unsigned ,FStar_Const.Int32 ) ->
                   FStar_Parser_Const.uint32_lid
               | (FStar_Const.Unsigned ,FStar_Const.Int64 ) ->
                   FStar_Parser_Const.uint64_lid)
        | FStar_Const.Const_string uu____11462 ->
            FStar_Syntax_Syntax.t_string
        | FStar_Const.Const_real uu____11468 -> FStar_Syntax_Syntax.t_real
        | FStar_Const.Const_float uu____11470 -> FStar_Syntax_Syntax.t_float
        | FStar_Const.Const_char uu____11471 ->
            let uu____11473 =
              FStar_Syntax_DsEnv.try_lookup_lid
                env.FStar_TypeChecker_Env.dsenv FStar_Parser_Const.char_lid
               in
            FStar_All.pipe_right uu____11473 FStar_Util.must
        | FStar_Const.Const_effect  -> FStar_Syntax_Util.ktype0
        | FStar_Const.Const_range uu____11478 -> FStar_Syntax_Syntax.t_range
        | FStar_Const.Const_range_of  ->
            let uu____11479 =
              let uu____11485 =
                let uu____11487 = FStar_Parser_Const.const_to_string c  in
                FStar_Util.format1
                  "Ill-typed %s: this constant must be fully applied"
                  uu____11487
                 in
              (FStar_Errors.Fatal_IllTyped, uu____11485)  in
            FStar_Errors.raise_error uu____11479 r
        | FStar_Const.Const_set_range_of  ->
            let uu____11491 =
              let uu____11497 =
                let uu____11499 = FStar_Parser_Const.const_to_string c  in
                FStar_Util.format1
                  "Ill-typed %s: this constant must be fully applied"
                  uu____11499
                 in
              (FStar_Errors.Fatal_IllTyped, uu____11497)  in
            FStar_Errors.raise_error uu____11491 r
        | FStar_Const.Const_reify  ->
            let uu____11503 =
              let uu____11509 =
                let uu____11511 = FStar_Parser_Const.const_to_string c  in
                FStar_Util.format1
                  "Ill-typed %s: this constant must be fully applied"
                  uu____11511
                 in
              (FStar_Errors.Fatal_IllTyped, uu____11509)  in
            FStar_Errors.raise_error uu____11503 r
        | FStar_Const.Const_reflect uu____11515 ->
            let uu____11516 =
              let uu____11522 =
                let uu____11524 = FStar_Parser_Const.const_to_string c  in
                FStar_Util.format1
                  "Ill-typed %s: this constant must be fully applied"
                  uu____11524
                 in
              (FStar_Errors.Fatal_IllTyped, uu____11522)  in
            FStar_Errors.raise_error uu____11516 r
        | uu____11528 ->
            FStar_Errors.raise_error
              (FStar_Errors.Fatal_UnsupportedConstant,
                "Unsupported constant") r

and (tc_comp :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.comp ->
      (FStar_Syntax_Syntax.comp * FStar_Syntax_Syntax.universe *
        FStar_TypeChecker_Common.guard_t))
  =
  fun env  ->
    fun c  ->
      let c0 = c  in
      match c.FStar_Syntax_Syntax.n with
      | FStar_Syntax_Syntax.Total (t,uu____11547) ->
          let uu____11556 = FStar_Syntax_Util.type_u ()  in
          (match uu____11556 with
           | (k,u) ->
               let uu____11569 = tc_check_tot_or_gtot_term env t k  in
               (match uu____11569 with
                | (t1,uu____11583,g) ->
                    let uu____11585 =
                      FStar_Syntax_Syntax.mk_Total' t1
                        (FStar_Pervasives_Native.Some u)
                       in
                    (uu____11585, u, g)))
      | FStar_Syntax_Syntax.GTotal (t,uu____11587) ->
          let uu____11596 = FStar_Syntax_Util.type_u ()  in
          (match uu____11596 with
           | (k,u) ->
               let uu____11609 = tc_check_tot_or_gtot_term env t k  in
               (match uu____11609 with
                | (t1,uu____11623,g) ->
                    let uu____11625 =
                      FStar_Syntax_Syntax.mk_GTotal' t1
                        (FStar_Pervasives_Native.Some u)
                       in
                    (uu____11625, u, g)))
      | FStar_Syntax_Syntax.Comp c1 ->
          let head1 =
            FStar_Syntax_Syntax.fvar c1.FStar_Syntax_Syntax.effect_name
              FStar_Syntax_Syntax.delta_constant FStar_Pervasives_Native.None
             in
          let head2 =
            match c1.FStar_Syntax_Syntax.comp_univs with
            | [] -> head1
            | us ->
                FStar_Syntax_Syntax.mk
                  (FStar_Syntax_Syntax.Tm_uinst (head1, us))
                  FStar_Pervasives_Native.None c0.FStar_Syntax_Syntax.pos
             in
          let tc =
            let uu____11635 =
              let uu____11640 =
                let uu____11641 =
                  FStar_Syntax_Syntax.as_arg
                    c1.FStar_Syntax_Syntax.result_typ
                   in
                uu____11641 :: (c1.FStar_Syntax_Syntax.effect_args)  in
              FStar_Syntax_Syntax.mk_Tm_app head2 uu____11640  in
            uu____11635 FStar_Pervasives_Native.None
              (c1.FStar_Syntax_Syntax.result_typ).FStar_Syntax_Syntax.pos
             in
          let uu____11658 =
            tc_check_tot_or_gtot_term env tc FStar_Syntax_Syntax.teff  in
          (match uu____11658 with
           | (tc1,uu____11672,f) ->
               let uu____11674 = FStar_Syntax_Util.head_and_args tc1  in
               (match uu____11674 with
                | (head3,args) ->
                    let comp_univs =
                      let uu____11724 =
                        let uu____11725 = FStar_Syntax_Subst.compress head3
                           in
                        uu____11725.FStar_Syntax_Syntax.n  in
                      match uu____11724 with
                      | FStar_Syntax_Syntax.Tm_uinst (uu____11728,us) -> us
                      | uu____11734 -> []  in
                    let uu____11735 = FStar_Syntax_Util.head_and_args tc1  in
                    (match uu____11735 with
                     | (uu____11758,args1) ->
                         let uu____11784 =
                           let uu____11807 = FStar_List.hd args1  in
                           let uu____11824 = FStar_List.tl args1  in
                           (uu____11807, uu____11824)  in
                         (match uu____11784 with
                          | (res,args2) ->
                              let uu____11905 =
                                let uu____11914 =
                                  FStar_All.pipe_right
                                    c1.FStar_Syntax_Syntax.flags
                                    (FStar_List.map
                                       (fun uu___5_11942  ->
                                          match uu___5_11942 with
                                          | FStar_Syntax_Syntax.DECREASES e
                                              ->
                                              let uu____11950 =
                                                FStar_TypeChecker_Env.clear_expected_typ
                                                  env
                                                 in
                                              (match uu____11950 with
                                               | (env1,uu____11962) ->
                                                   let uu____11967 =
                                                     tc_tot_or_gtot_term env1
                                                       e
                                                      in
                                                   (match uu____11967 with
                                                    | (e1,uu____11979,g) ->
                                                        ((FStar_Syntax_Syntax.DECREASES
                                                            e1), g)))
                                          | f1 ->
                                              (f1,
                                                FStar_TypeChecker_Env.trivial_guard)))
                                   in
                                FStar_All.pipe_right uu____11914
                                  FStar_List.unzip
                                 in
                              (match uu____11905 with
                               | (flags,guards) ->
                                   let u =
                                     env.FStar_TypeChecker_Env.universe_of
                                       env (FStar_Pervasives_Native.fst res)
                                      in
                                   let c2 =
                                     FStar_Syntax_Syntax.mk_Comp
                                       (let uu___1659_12020 = c1  in
                                        {
                                          FStar_Syntax_Syntax.comp_univs =
                                            comp_univs;
                                          FStar_Syntax_Syntax.effect_name =
                                            (uu___1659_12020.FStar_Syntax_Syntax.effect_name);
                                          FStar_Syntax_Syntax.result_typ =
                                            (FStar_Pervasives_Native.fst res);
                                          FStar_Syntax_Syntax.effect_args =
                                            args2;
                                          FStar_Syntax_Syntax.flags = flags
                                        })
                                      in
                                   let u_c =
                                     FStar_All.pipe_right c2
                                       (FStar_TypeChecker_Util.universe_of_comp
                                          env u)
                                      in
                                   let uu____12026 =
                                     FStar_List.fold_left
                                       FStar_TypeChecker_Env.conj_guard f
                                       guards
                                      in
                                   (c2, u_c, uu____12026))))))

and (tc_universe :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.universe -> FStar_Syntax_Syntax.universe)
  =
  fun env  ->
    fun u  ->
      let rec aux u1 =
        let u2 = FStar_Syntax_Subst.compress_univ u1  in
        match u2 with
        | FStar_Syntax_Syntax.U_bvar uu____12036 ->
            failwith "Impossible: locally nameless"
        | FStar_Syntax_Syntax.U_unknown  -> failwith "Unknown universe"
        | FStar_Syntax_Syntax.U_unif uu____12040 -> u2
        | FStar_Syntax_Syntax.U_zero  -> u2
        | FStar_Syntax_Syntax.U_succ u3 ->
            let uu____12050 = aux u3  in
            FStar_Syntax_Syntax.U_succ uu____12050
        | FStar_Syntax_Syntax.U_max us ->
            let uu____12054 = FStar_List.map aux us  in
            FStar_Syntax_Syntax.U_max uu____12054
        | FStar_Syntax_Syntax.U_name x ->
            let uu____12058 =
              env.FStar_TypeChecker_Env.use_bv_sorts ||
                (FStar_TypeChecker_Env.lookup_univ env x)
               in
            if uu____12058
            then u2
            else
              (let uu____12063 =
                 let uu____12065 =
                   let uu____12067 = FStar_Syntax_Print.univ_to_string u2  in
                   Prims.op_Hat uu____12067 " not found"  in
                 Prims.op_Hat "Universe variable " uu____12065  in
               failwith uu____12063)
         in
      if env.FStar_TypeChecker_Env.lax_universes
      then FStar_Syntax_Syntax.U_zero
      else
        (match u with
         | FStar_Syntax_Syntax.U_unknown  ->
             let uu____12074 = FStar_Syntax_Util.type_u ()  in
             FStar_All.pipe_right uu____12074 FStar_Pervasives_Native.snd
         | uu____12083 -> aux u)

and (tc_abs :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term ->
      FStar_Syntax_Syntax.binders ->
        FStar_Syntax_Syntax.term ->
          (FStar_Syntax_Syntax.term * FStar_TypeChecker_Common.lcomp *
            FStar_TypeChecker_Common.guard_t))
  =
  fun env  ->
    fun top  ->
      fun bs  ->
        fun body  ->
          let fail1 msg t =
            let uu____12114 =
              FStar_TypeChecker_Err.expected_a_term_of_type_t_got_a_function
                env msg t top
               in
            FStar_Errors.raise_error uu____12114 top.FStar_Syntax_Syntax.pos
             in
          let check_binders env1 bs1 bs_expected =
            let rec aux uu____12203 bs2 bs_expected1 =
              match uu____12203 with
              | (env2,subst1) ->
                  (match (bs2, bs_expected1) with
                   | ([],[]) ->
                       (env2, [], FStar_Pervasives_Native.None,
                         FStar_TypeChecker_Env.trivial_guard, subst1)
                   | ((hd1,imp)::bs3,(hd_expected,imp')::bs_expected2) ->
                       ((let special q1 q2 =
                           match (q1, q2) with
                           | (FStar_Pervasives_Native.Some
                              (FStar_Syntax_Syntax.Meta
                              uu____12394),FStar_Pervasives_Native.Some
                              (FStar_Syntax_Syntax.Meta uu____12395)) -> true
                           | (FStar_Pervasives_Native.None
                              ,FStar_Pervasives_Native.Some
                              (FStar_Syntax_Syntax.Equality )) -> true
                           | (FStar_Pervasives_Native.Some
                              (FStar_Syntax_Syntax.Implicit
                              uu____12410),FStar_Pervasives_Native.Some
                              (FStar_Syntax_Syntax.Meta uu____12411)) -> true
                           | uu____12420 -> false  in
                         let uu____12430 =
                           (Prims.op_Negation (special imp imp')) &&
                             (let uu____12433 =
                                FStar_Syntax_Util.eq_aqual imp imp'  in
                              uu____12433 <> FStar_Syntax_Util.Equal)
                            in
                         if uu____12430
                         then
                           let uu____12435 =
                             let uu____12441 =
                               let uu____12443 =
                                 FStar_Syntax_Print.bv_to_string hd1  in
                               FStar_Util.format1
                                 "Inconsistent implicit argument annotation on argument %s"
                                 uu____12443
                                in
                             (FStar_Errors.Fatal_InconsistentImplicitArgumentAnnotation,
                               uu____12441)
                              in
                           let uu____12447 =
                             FStar_Syntax_Syntax.range_of_bv hd1  in
                           FStar_Errors.raise_error uu____12435 uu____12447
                         else ());
                        (let expected_t =
                           FStar_Syntax_Subst.subst subst1
                             hd_expected.FStar_Syntax_Syntax.sort
                            in
                         let uu____12451 =
                           let uu____12458 =
                             let uu____12459 =
                               FStar_Syntax_Util.unmeta
                                 hd1.FStar_Syntax_Syntax.sort
                                in
                             uu____12459.FStar_Syntax_Syntax.n  in
                           match uu____12458 with
                           | FStar_Syntax_Syntax.Tm_unknown  ->
                               (expected_t,
                                 FStar_TypeChecker_Env.trivial_guard)
                           | uu____12470 ->
                               ((let uu____12472 =
                                   FStar_TypeChecker_Env.debug env2
                                     FStar_Options.High
                                    in
                                 if uu____12472
                                 then
                                   let uu____12475 =
                                     FStar_Syntax_Print.bv_to_string hd1  in
                                   FStar_Util.print1 "Checking binder %s\n"
                                     uu____12475
                                 else ());
                                (let uu____12480 =
                                   tc_tot_or_gtot_term env2
                                     hd1.FStar_Syntax_Syntax.sort
                                    in
                                 match uu____12480 with
                                 | (t,uu____12494,g1_env) ->
                                     let g2_env =
                                       let uu____12497 =
                                         FStar_TypeChecker_Rel.teq_nosmt env2
                                           t expected_t
                                          in
                                       match uu____12497 with
                                       | FStar_Pervasives_Native.Some g ->
                                           FStar_All.pipe_right g
                                             (FStar_TypeChecker_Rel.resolve_implicits
                                                env2)
                                       | FStar_Pervasives_Native.None  ->
                                           let uu____12501 =
                                             FStar_TypeChecker_Rel.get_subtyping_prop
                                               env2 expected_t t
                                              in
                                           (match uu____12501 with
                                            | FStar_Pervasives_Native.None 
                                                ->
                                                let uu____12504 =
                                                  FStar_TypeChecker_Err.basic_type_error
                                                    env2
                                                    FStar_Pervasives_Native.None
                                                    expected_t t
                                                   in
                                                let uu____12510 =
                                                  FStar_TypeChecker_Env.get_range
                                                    env2
                                                   in
                                                FStar_Errors.raise_error
                                                  uu____12504 uu____12510
                                            | FStar_Pervasives_Native.Some
                                                g_env ->
                                                FStar_TypeChecker_Util.label_guard
                                                  (hd1.FStar_Syntax_Syntax.sort).FStar_Syntax_Syntax.pos
                                                  "Type annotation on parameter incompatible with the expected type"
                                                  g_env)
                                        in
                                     let uu____12513 =
                                       FStar_TypeChecker_Env.conj_guard
                                         g1_env g2_env
                                        in
                                     (t, uu____12513)))
                            in
                         match uu____12451 with
                         | (t,g_env) ->
                             let hd2 =
                               let uu___1759_12539 = hd1  in
                               {
                                 FStar_Syntax_Syntax.ppname =
                                   (uu___1759_12539.FStar_Syntax_Syntax.ppname);
                                 FStar_Syntax_Syntax.index =
                                   (uu___1759_12539.FStar_Syntax_Syntax.index);
                                 FStar_Syntax_Syntax.sort = t
                               }  in
                             let b = (hd2, imp)  in
                             let b_expected = (hd_expected, imp')  in
                             let env_b = push_binding env2 b  in
                             let subst2 =
                               let uu____12562 =
                                 FStar_Syntax_Syntax.bv_to_name hd2  in
                               maybe_extend_subst subst1 b_expected
                                 uu____12562
                                in
                             let uu____12565 =
                               aux (env_b, subst2) bs3 bs_expected2  in
                             (match uu____12565 with
                              | (env_bs,bs4,rest,g'_env_b,subst3) ->
                                  let g'_env =
                                    FStar_TypeChecker_Env.close_guard env_bs
                                      [b] g'_env_b
                                     in
                                  let uu____12630 =
                                    FStar_TypeChecker_Env.conj_guard g_env
                                      g'_env
                                     in
                                  (env_bs, (b :: bs4), rest, uu____12630,
                                    subst3))))
                   | (rest,[]) ->
                       (env2, [],
                         (FStar_Pervasives_Native.Some (FStar_Util.Inl rest)),
                         FStar_TypeChecker_Env.trivial_guard, subst1)
                   | ([],rest) ->
                       (env2, [],
                         (FStar_Pervasives_Native.Some (FStar_Util.Inr rest)),
                         FStar_TypeChecker_Env.trivial_guard, subst1))
               in
            aux (env1, []) bs1 bs_expected  in
          let rec expected_function_typ1 env1 t0 body1 =
            match t0 with
            | FStar_Pervasives_Native.None  ->
                ((match env1.FStar_TypeChecker_Env.letrecs with
                  | [] -> ()
                  | uu____12802 ->
                      failwith
                        "Impossible: Can't have a let rec annotation but no expected type");
                 (let uu____12812 = tc_binders env1 bs  in
                  match uu____12812 with
                  | (bs1,envbody,g_env,uu____12842) ->
                      (FStar_Pervasives_Native.None, bs1, [],
                        FStar_Pervasives_Native.None, envbody, body1, g_env)))
            | FStar_Pervasives_Native.Some t ->
                let t1 = FStar_Syntax_Subst.compress t  in
                let rec as_function_typ norm1 t2 =
                  let uu____12898 =
                    let uu____12899 = FStar_Syntax_Subst.compress t2  in
                    uu____12899.FStar_Syntax_Syntax.n  in
                  match uu____12898 with
                  | FStar_Syntax_Syntax.Tm_uvar uu____12932 ->
                      ((match env1.FStar_TypeChecker_Env.letrecs with
                        | [] -> ()
                        | uu____12952 -> failwith "Impossible");
                       (let uu____12962 = tc_binders env1 bs  in
                        match uu____12962 with
                        | (bs1,envbody,g_env,uu____13004) ->
                            let uu____13005 =
                              FStar_TypeChecker_Env.clear_expected_typ
                                envbody
                               in
                            (match uu____13005 with
                             | (envbody1,uu____13043) ->
                                 ((FStar_Pervasives_Native.Some t2), bs1, [],
                                   FStar_Pervasives_Native.None, envbody1,
                                   body1, g_env))))
                  | FStar_Syntax_Syntax.Tm_app
                      ({
                         FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                           uu____13064;
                         FStar_Syntax_Syntax.pos = uu____13065;
                         FStar_Syntax_Syntax.vars = uu____13066;_},uu____13067)
                      ->
                      ((match env1.FStar_TypeChecker_Env.letrecs with
                        | [] -> ()
                        | uu____13111 -> failwith "Impossible");
                       (let uu____13121 = tc_binders env1 bs  in
                        match uu____13121 with
                        | (bs1,envbody,g_env,uu____13163) ->
                            let uu____13164 =
                              FStar_TypeChecker_Env.clear_expected_typ
                                envbody
                               in
                            (match uu____13164 with
                             | (envbody1,uu____13202) ->
                                 ((FStar_Pervasives_Native.Some t2), bs1, [],
                                   FStar_Pervasives_Native.None, envbody1,
                                   body1, g_env))))
                  | FStar_Syntax_Syntax.Tm_refine (b,uu____13224) ->
                      let uu____13229 =
                        as_function_typ norm1 b.FStar_Syntax_Syntax.sort  in
                      (match uu____13229 with
                       | (uu____13290,bs1,bs',copt,env_body,body2,g_env) ->
                           ((FStar_Pervasives_Native.Some t2), bs1, bs',
                             copt, env_body, body2, g_env))
                  | FStar_Syntax_Syntax.Tm_arrow (bs_expected,c_expected) ->
                      let uu____13367 =
                        FStar_Syntax_Subst.open_comp bs_expected c_expected
                         in
                      (match uu____13367 with
                       | (bs_expected1,c_expected1) ->
                           let check_actuals_against_formals env2 bs1
                             bs_expected2 body2 =
                             let rec handle_more uu____13512 c_expected2
                               body3 =
                               match uu____13512 with
                               | (env_bs,bs2,more,guard_env,subst1) ->
                                   (match more with
                                    | FStar_Pervasives_Native.None  ->
                                        let uu____13626 =
                                          FStar_Syntax_Subst.subst_comp
                                            subst1 c_expected2
                                           in
                                        (env_bs, bs2, guard_env, uu____13626,
                                          body3)
                                    | FStar_Pervasives_Native.Some
                                        (FStar_Util.Inr more_bs_expected) ->
                                        let c =
                                          let uu____13643 =
                                            FStar_Syntax_Util.arrow
                                              more_bs_expected c_expected2
                                             in
                                          FStar_Syntax_Syntax.mk_Total
                                            uu____13643
                                           in
                                        let uu____13644 =
                                          FStar_Syntax_Subst.subst_comp
                                            subst1 c
                                           in
                                        (env_bs, bs2, guard_env, uu____13644,
                                          body3)
                                    | FStar_Pervasives_Native.Some
                                        (FStar_Util.Inl more_bs) ->
                                        let c =
                                          FStar_Syntax_Subst.subst_comp
                                            subst1 c_expected2
                                           in
                                        let uu____13661 =
                                          (FStar_Options.ml_ish ()) ||
                                            (FStar_Syntax_Util.is_named_tot c)
                                           in
                                        if uu____13661
                                        then
                                          let t3 =
                                            FStar_TypeChecker_Normalize.unfold_whnf
                                              env_bs
                                              (FStar_Syntax_Util.comp_result
                                                 c)
                                             in
                                          (match t3.FStar_Syntax_Syntax.n
                                           with
                                           | FStar_Syntax_Syntax.Tm_arrow
                                               (bs_expected3,c_expected3) ->
                                               let uu____13727 =
                                                 FStar_Syntax_Subst.open_comp
                                                   bs_expected3 c_expected3
                                                  in
                                               (match uu____13727 with
                                                | (bs_expected4,c_expected4)
                                                    ->
                                                    let uu____13754 =
                                                      check_binders env_bs
                                                        more_bs bs_expected4
                                                       in
                                                    (match uu____13754 with
                                                     | (env_bs_bs',bs',more1,guard'_env_bs,subst2)
                                                         ->
                                                         let guard'_env =
                                                           FStar_TypeChecker_Env.close_guard
                                                             env_bs bs2
                                                             guard'_env_bs
                                                            in
                                                         let uu____13809 =
                                                           let uu____13836 =
                                                             FStar_TypeChecker_Env.conj_guard
                                                               guard_env
                                                               guard'_env
                                                              in
                                                           (env_bs_bs',
                                                             (FStar_List.append
                                                                bs2 bs'),
                                                             more1,
                                                             uu____13836,
                                                             subst2)
                                                            in
                                                         handle_more
                                                           uu____13809
                                                           c_expected4 body3))
                                           | uu____13859 ->
                                               let body4 =
                                                 FStar_Syntax_Util.abs
                                                   more_bs body3
                                                   FStar_Pervasives_Native.None
                                                  in
                                               (env_bs, bs2, guard_env, c,
                                                 body4))
                                        else
                                          (let body4 =
                                             FStar_Syntax_Util.abs more_bs
                                               body3
                                               FStar_Pervasives_Native.None
                                              in
                                           (env_bs, bs2, guard_env, c, body4)))
                                in
                             let uu____13888 =
                               check_binders env2 bs1 bs_expected2  in
                             handle_more uu____13888 c_expected1 body2  in
                           let mk_letrec_env envbody bs1 c =
                             let letrecs = guard_letrecs envbody bs1 c  in
                             let envbody1 =
                               let uu___1885_13953 = envbody  in
                               {
                                 FStar_TypeChecker_Env.solver =
                                   (uu___1885_13953.FStar_TypeChecker_Env.solver);
                                 FStar_TypeChecker_Env.range =
                                   (uu___1885_13953.FStar_TypeChecker_Env.range);
                                 FStar_TypeChecker_Env.curmodule =
                                   (uu___1885_13953.FStar_TypeChecker_Env.curmodule);
                                 FStar_TypeChecker_Env.gamma =
                                   (uu___1885_13953.FStar_TypeChecker_Env.gamma);
                                 FStar_TypeChecker_Env.gamma_sig =
                                   (uu___1885_13953.FStar_TypeChecker_Env.gamma_sig);
                                 FStar_TypeChecker_Env.gamma_cache =
                                   (uu___1885_13953.FStar_TypeChecker_Env.gamma_cache);
                                 FStar_TypeChecker_Env.modules =
                                   (uu___1885_13953.FStar_TypeChecker_Env.modules);
                                 FStar_TypeChecker_Env.expected_typ =
                                   (uu___1885_13953.FStar_TypeChecker_Env.expected_typ);
                                 FStar_TypeChecker_Env.sigtab =
                                   (uu___1885_13953.FStar_TypeChecker_Env.sigtab);
                                 FStar_TypeChecker_Env.attrtab =
                                   (uu___1885_13953.FStar_TypeChecker_Env.attrtab);
                                 FStar_TypeChecker_Env.instantiate_imp =
                                   (uu___1885_13953.FStar_TypeChecker_Env.instantiate_imp);
                                 FStar_TypeChecker_Env.effects =
                                   (uu___1885_13953.FStar_TypeChecker_Env.effects);
                                 FStar_TypeChecker_Env.generalize =
                                   (uu___1885_13953.FStar_TypeChecker_Env.generalize);
                                 FStar_TypeChecker_Env.letrecs = [];
                                 FStar_TypeChecker_Env.top_level =
                                   (uu___1885_13953.FStar_TypeChecker_Env.top_level);
                                 FStar_TypeChecker_Env.check_uvars =
                                   (uu___1885_13953.FStar_TypeChecker_Env.check_uvars);
                                 FStar_TypeChecker_Env.use_eq =
                                   (uu___1885_13953.FStar_TypeChecker_Env.use_eq);
                                 FStar_TypeChecker_Env.is_iface =
                                   (uu___1885_13953.FStar_TypeChecker_Env.is_iface);
                                 FStar_TypeChecker_Env.admit =
                                   (uu___1885_13953.FStar_TypeChecker_Env.admit);
                                 FStar_TypeChecker_Env.lax =
                                   (uu___1885_13953.FStar_TypeChecker_Env.lax);
                                 FStar_TypeChecker_Env.lax_universes =
                                   (uu___1885_13953.FStar_TypeChecker_Env.lax_universes);
                                 FStar_TypeChecker_Env.phase1 =
                                   (uu___1885_13953.FStar_TypeChecker_Env.phase1);
                                 FStar_TypeChecker_Env.failhard =
                                   (uu___1885_13953.FStar_TypeChecker_Env.failhard);
                                 FStar_TypeChecker_Env.nosynth =
                                   (uu___1885_13953.FStar_TypeChecker_Env.nosynth);
                                 FStar_TypeChecker_Env.uvar_subtyping =
                                   (uu___1885_13953.FStar_TypeChecker_Env.uvar_subtyping);
                                 FStar_TypeChecker_Env.tc_term =
                                   (uu___1885_13953.FStar_TypeChecker_Env.tc_term);
                                 FStar_TypeChecker_Env.type_of =
                                   (uu___1885_13953.FStar_TypeChecker_Env.type_of);
                                 FStar_TypeChecker_Env.universe_of =
                                   (uu___1885_13953.FStar_TypeChecker_Env.universe_of);
                                 FStar_TypeChecker_Env.check_type_of =
                                   (uu___1885_13953.FStar_TypeChecker_Env.check_type_of);
                                 FStar_TypeChecker_Env.use_bv_sorts =
                                   (uu___1885_13953.FStar_TypeChecker_Env.use_bv_sorts);
                                 FStar_TypeChecker_Env.qtbl_name_and_index =
                                   (uu___1885_13953.FStar_TypeChecker_Env.qtbl_name_and_index);
                                 FStar_TypeChecker_Env.normalized_eff_names =
                                   (uu___1885_13953.FStar_TypeChecker_Env.normalized_eff_names);
                                 FStar_TypeChecker_Env.fv_delta_depths =
                                   (uu___1885_13953.FStar_TypeChecker_Env.fv_delta_depths);
                                 FStar_TypeChecker_Env.proof_ns =
                                   (uu___1885_13953.FStar_TypeChecker_Env.proof_ns);
                                 FStar_TypeChecker_Env.synth_hook =
                                   (uu___1885_13953.FStar_TypeChecker_Env.synth_hook);
                                 FStar_TypeChecker_Env.splice =
                                   (uu___1885_13953.FStar_TypeChecker_Env.splice);
                                 FStar_TypeChecker_Env.mpreprocess =
                                   (uu___1885_13953.FStar_TypeChecker_Env.mpreprocess);
                                 FStar_TypeChecker_Env.postprocess =
                                   (uu___1885_13953.FStar_TypeChecker_Env.postprocess);
                                 FStar_TypeChecker_Env.is_native_tactic =
                                   (uu___1885_13953.FStar_TypeChecker_Env.is_native_tactic);
                                 FStar_TypeChecker_Env.identifier_info =
                                   (uu___1885_13953.FStar_TypeChecker_Env.identifier_info);
                                 FStar_TypeChecker_Env.tc_hooks =
                                   (uu___1885_13953.FStar_TypeChecker_Env.tc_hooks);
                                 FStar_TypeChecker_Env.dsenv =
                                   (uu___1885_13953.FStar_TypeChecker_Env.dsenv);
                                 FStar_TypeChecker_Env.nbe =
                                   (uu___1885_13953.FStar_TypeChecker_Env.nbe);
                                 FStar_TypeChecker_Env.strict_args_tab =
                                   (uu___1885_13953.FStar_TypeChecker_Env.strict_args_tab);
                                 FStar_TypeChecker_Env.erasable_types_tab =
                                   (uu___1885_13953.FStar_TypeChecker_Env.erasable_types_tab)
                               }  in
                             let uu____13960 =
                               FStar_All.pipe_right letrecs
                                 (FStar_List.fold_left
                                    (fun uu____14026  ->
                                       fun uu____14027  ->
                                         match (uu____14026, uu____14027)
                                         with
                                         | ((env2,letrec_binders,g),(l,t3,u_names))
                                             ->
                                             let uu____14118 =
                                               let uu____14125 =
                                                 let uu____14126 =
                                                   FStar_TypeChecker_Env.clear_expected_typ
                                                     env2
                                                    in
                                                 FStar_All.pipe_right
                                                   uu____14126
                                                   FStar_Pervasives_Native.fst
                                                  in
                                               tc_term uu____14125 t3  in
                                             (match uu____14118 with
                                              | (t4,uu____14150,g') ->
                                                  let env3 =
                                                    FStar_TypeChecker_Env.push_let_binding
                                                      env2 l (u_names, t4)
                                                     in
                                                  let lb =
                                                    match l with
                                                    | FStar_Util.Inl x ->
                                                        let uu____14163 =
                                                          FStar_Syntax_Syntax.mk_binder
                                                            (let uu___1903_14166
                                                               = x  in
                                                             {
                                                               FStar_Syntax_Syntax.ppname
                                                                 =
                                                                 (uu___1903_14166.FStar_Syntax_Syntax.ppname);
                                                               FStar_Syntax_Syntax.index
                                                                 =
                                                                 (uu___1903_14166.FStar_Syntax_Syntax.index);
                                                               FStar_Syntax_Syntax.sort
                                                                 = t4
                                                             })
                                                           in
                                                        uu____14163 ::
                                                          letrec_binders
                                                    | uu____14167 ->
                                                        letrec_binders
                                                     in
                                                  let uu____14172 =
                                                    FStar_TypeChecker_Env.conj_guard
                                                      g g'
                                                     in
                                                  (env3, lb, uu____14172)))
                                    (envbody1, [],
                                      FStar_TypeChecker_Env.trivial_guard))
                                in
                             match uu____13960 with
                             | (envbody2,letrec_binders,g) ->
                                 let uu____14192 =
                                   FStar_TypeChecker_Env.close_guard envbody2
                                     bs1 g
                                    in
                                 (envbody2, letrec_binders, uu____14192)
                              in
                           let uu____14195 =
                             check_actuals_against_formals env1 bs
                               bs_expected1 body1
                              in
                           (match uu____14195 with
                            | (envbody,bs1,g_env,c,body2) ->
                                let uu____14271 = mk_letrec_env envbody bs1 c
                                   in
                                (match uu____14271 with
                                 | (envbody1,letrecs,g_annots) ->
                                     let envbody2 =
                                       FStar_TypeChecker_Env.set_expected_typ
                                         envbody1
                                         (FStar_Syntax_Util.comp_result c)
                                        in
                                     let uu____14318 =
                                       FStar_TypeChecker_Env.conj_guard g_env
                                         g_annots
                                        in
                                     ((FStar_Pervasives_Native.Some t2), bs1,
                                       letrecs,
                                       (FStar_Pervasives_Native.Some c),
                                       envbody2, body2, uu____14318))))
                  | uu____14335 ->
                      if Prims.op_Negation norm1
                      then
                        let uu____14367 =
                          let uu____14368 =
                            FStar_All.pipe_right t2
                              (FStar_TypeChecker_Normalize.unfold_whnf env1)
                             in
                          FStar_All.pipe_right uu____14368
                            FStar_Syntax_Util.unascribe
                           in
                        as_function_typ true uu____14367
                      else
                        (let uu____14372 =
                           expected_function_typ1 env1
                             FStar_Pervasives_Native.None body1
                            in
                         match uu____14372 with
                         | (uu____14421,bs1,uu____14423,c_opt,envbody,body2,g_env)
                             ->
                             ((FStar_Pervasives_Native.Some t2), bs1, [],
                               c_opt, envbody, body2, g_env))
                   in
                as_function_typ false t1
             in
          let use_eq = env.FStar_TypeChecker_Env.use_eq  in
          let uu____14455 = FStar_TypeChecker_Env.clear_expected_typ env  in
          match uu____14455 with
          | (env1,topt) ->
              ((let uu____14475 =
                  FStar_TypeChecker_Env.debug env1 FStar_Options.High  in
                if uu____14475
                then
                  let uu____14478 =
                    match topt with
                    | FStar_Pervasives_Native.None  -> "None"
                    | FStar_Pervasives_Native.Some t ->
                        FStar_Syntax_Print.term_to_string t
                     in
                  FStar_Util.print2
                    "!!!!!!!!!!!!!!!Expected type is %s, top_level=%s\n"
                    uu____14478
                    (if env1.FStar_TypeChecker_Env.top_level
                     then "true"
                     else "false")
                else ());
               (let uu____14492 = expected_function_typ1 env1 topt body  in
                match uu____14492 with
                | (tfun_opt,bs1,letrec_binders,c_opt,envbody,body1,g_env) ->
                    ((let uu____14533 =
                        FStar_TypeChecker_Env.debug env1
                          FStar_Options.Extreme
                         in
                      if uu____14533
                      then
                        let uu____14536 =
                          match tfun_opt with
                          | FStar_Pervasives_Native.None  -> "None"
                          | FStar_Pervasives_Native.Some t ->
                              FStar_Syntax_Print.term_to_string t
                           in
                        let uu____14541 =
                          match c_opt with
                          | FStar_Pervasives_Native.None  -> "None"
                          | FStar_Pervasives_Native.Some t ->
                              FStar_Syntax_Print.comp_to_string t
                           in
                        let uu____14546 =
                          let uu____14548 =
                            FStar_TypeChecker_Env.expected_typ envbody  in
                          match uu____14548 with
                          | FStar_Pervasives_Native.None  -> "None"
                          | FStar_Pervasives_Native.Some t ->
                              FStar_Syntax_Print.term_to_string t
                           in
                        FStar_Util.print3
                          "After expected_function_typ, tfun_opt: %s, c_opt: %s, and expected type in envbody: %s\n"
                          uu____14536 uu____14541 uu____14546
                      else ());
                     (let uu____14558 =
                        FStar_All.pipe_left
                          (FStar_TypeChecker_Env.debug env1)
                          (FStar_Options.Other "NYC")
                         in
                      if uu____14558
                      then
                        let uu____14563 =
                          FStar_Syntax_Print.binders_to_string ", " bs1  in
                        let uu____14566 =
                          FStar_TypeChecker_Rel.guard_to_string env1 g_env
                           in
                        FStar_Util.print2
                          "!!!!!!!!!!!!!!!Guard for function with binders %s is %s\n"
                          uu____14563 uu____14566
                      else ());
                     (let envbody1 =
                        FStar_TypeChecker_Env.set_range envbody
                          body1.FStar_Syntax_Syntax.pos
                         in
                      let uu____14572 =
                        let should_check_expected_effect =
                          let uu____14585 =
                            let uu____14592 =
                              let uu____14593 =
                                FStar_Syntax_Subst.compress body1  in
                              uu____14593.FStar_Syntax_Syntax.n  in
                            (c_opt, uu____14592)  in
                          match uu____14585 with
                          | (FStar_Pervasives_Native.None
                             ,FStar_Syntax_Syntax.Tm_ascribed
                             (uu____14599,(FStar_Util.Inr
                                           expected_c,uu____14601),uu____14602))
                              -> false
                          | uu____14652 -> true  in
                        let uu____14660 =
                          tc_term
                            (let uu___1976_14669 = envbody1  in
                             {
                               FStar_TypeChecker_Env.solver =
                                 (uu___1976_14669.FStar_TypeChecker_Env.solver);
                               FStar_TypeChecker_Env.range =
                                 (uu___1976_14669.FStar_TypeChecker_Env.range);
                               FStar_TypeChecker_Env.curmodule =
                                 (uu___1976_14669.FStar_TypeChecker_Env.curmodule);
                               FStar_TypeChecker_Env.gamma =
                                 (uu___1976_14669.FStar_TypeChecker_Env.gamma);
                               FStar_TypeChecker_Env.gamma_sig =
                                 (uu___1976_14669.FStar_TypeChecker_Env.gamma_sig);
                               FStar_TypeChecker_Env.gamma_cache =
                                 (uu___1976_14669.FStar_TypeChecker_Env.gamma_cache);
                               FStar_TypeChecker_Env.modules =
                                 (uu___1976_14669.FStar_TypeChecker_Env.modules);
                               FStar_TypeChecker_Env.expected_typ =
                                 (uu___1976_14669.FStar_TypeChecker_Env.expected_typ);
                               FStar_TypeChecker_Env.sigtab =
                                 (uu___1976_14669.FStar_TypeChecker_Env.sigtab);
                               FStar_TypeChecker_Env.attrtab =
                                 (uu___1976_14669.FStar_TypeChecker_Env.attrtab);
                               FStar_TypeChecker_Env.instantiate_imp =
                                 (uu___1976_14669.FStar_TypeChecker_Env.instantiate_imp);
                               FStar_TypeChecker_Env.effects =
                                 (uu___1976_14669.FStar_TypeChecker_Env.effects);
                               FStar_TypeChecker_Env.generalize =
                                 (uu___1976_14669.FStar_TypeChecker_Env.generalize);
                               FStar_TypeChecker_Env.letrecs =
                                 (uu___1976_14669.FStar_TypeChecker_Env.letrecs);
                               FStar_TypeChecker_Env.top_level = false;
                               FStar_TypeChecker_Env.check_uvars =
                                 (uu___1976_14669.FStar_TypeChecker_Env.check_uvars);
                               FStar_TypeChecker_Env.use_eq = use_eq;
                               FStar_TypeChecker_Env.is_iface =
                                 (uu___1976_14669.FStar_TypeChecker_Env.is_iface);
                               FStar_TypeChecker_Env.admit =
                                 (uu___1976_14669.FStar_TypeChecker_Env.admit);
                               FStar_TypeChecker_Env.lax =
                                 (uu___1976_14669.FStar_TypeChecker_Env.lax);
                               FStar_TypeChecker_Env.lax_universes =
                                 (uu___1976_14669.FStar_TypeChecker_Env.lax_universes);
                               FStar_TypeChecker_Env.phase1 =
                                 (uu___1976_14669.FStar_TypeChecker_Env.phase1);
                               FStar_TypeChecker_Env.failhard =
                                 (uu___1976_14669.FStar_TypeChecker_Env.failhard);
                               FStar_TypeChecker_Env.nosynth =
                                 (uu___1976_14669.FStar_TypeChecker_Env.nosynth);
                               FStar_TypeChecker_Env.uvar_subtyping =
                                 (uu___1976_14669.FStar_TypeChecker_Env.uvar_subtyping);
                               FStar_TypeChecker_Env.tc_term =
                                 (uu___1976_14669.FStar_TypeChecker_Env.tc_term);
                               FStar_TypeChecker_Env.type_of =
                                 (uu___1976_14669.FStar_TypeChecker_Env.type_of);
                               FStar_TypeChecker_Env.universe_of =
                                 (uu___1976_14669.FStar_TypeChecker_Env.universe_of);
                               FStar_TypeChecker_Env.check_type_of =
                                 (uu___1976_14669.FStar_TypeChecker_Env.check_type_of);
                               FStar_TypeChecker_Env.use_bv_sorts =
                                 (uu___1976_14669.FStar_TypeChecker_Env.use_bv_sorts);
                               FStar_TypeChecker_Env.qtbl_name_and_index =
                                 (uu___1976_14669.FStar_TypeChecker_Env.qtbl_name_and_index);
                               FStar_TypeChecker_Env.normalized_eff_names =
                                 (uu___1976_14669.FStar_TypeChecker_Env.normalized_eff_names);
                               FStar_TypeChecker_Env.fv_delta_depths =
                                 (uu___1976_14669.FStar_TypeChecker_Env.fv_delta_depths);
                               FStar_TypeChecker_Env.proof_ns =
                                 (uu___1976_14669.FStar_TypeChecker_Env.proof_ns);
                               FStar_TypeChecker_Env.synth_hook =
                                 (uu___1976_14669.FStar_TypeChecker_Env.synth_hook);
                               FStar_TypeChecker_Env.splice =
                                 (uu___1976_14669.FStar_TypeChecker_Env.splice);
                               FStar_TypeChecker_Env.mpreprocess =
                                 (uu___1976_14669.FStar_TypeChecker_Env.mpreprocess);
                               FStar_TypeChecker_Env.postprocess =
                                 (uu___1976_14669.FStar_TypeChecker_Env.postprocess);
                               FStar_TypeChecker_Env.is_native_tactic =
                                 (uu___1976_14669.FStar_TypeChecker_Env.is_native_tactic);
                               FStar_TypeChecker_Env.identifier_info =
                                 (uu___1976_14669.FStar_TypeChecker_Env.identifier_info);
                               FStar_TypeChecker_Env.tc_hooks =
                                 (uu___1976_14669.FStar_TypeChecker_Env.tc_hooks);
                               FStar_TypeChecker_Env.dsenv =
                                 (uu___1976_14669.FStar_TypeChecker_Env.dsenv);
                               FStar_TypeChecker_Env.nbe =
                                 (uu___1976_14669.FStar_TypeChecker_Env.nbe);
                               FStar_TypeChecker_Env.strict_args_tab =
                                 (uu___1976_14669.FStar_TypeChecker_Env.strict_args_tab);
                               FStar_TypeChecker_Env.erasable_types_tab =
                                 (uu___1976_14669.FStar_TypeChecker_Env.erasable_types_tab)
                             }) body1
                           in
                        match uu____14660 with
                        | (body2,cbody,guard_body) ->
                            let guard_body1 =
                              FStar_TypeChecker_Rel.solve_deferred_constraints
                                envbody1 guard_body
                               in
                            if should_check_expected_effect
                            then
                              let uu____14696 =
                                FStar_TypeChecker_Common.lcomp_comp cbody  in
                              (match uu____14696 with
                               | (cbody1,g_lc) ->
                                   let uu____14713 =
                                     check_expected_effect
                                       (let uu___1987_14722 = envbody1  in
                                        {
                                          FStar_TypeChecker_Env.solver =
                                            (uu___1987_14722.FStar_TypeChecker_Env.solver);
                                          FStar_TypeChecker_Env.range =
                                            (uu___1987_14722.FStar_TypeChecker_Env.range);
                                          FStar_TypeChecker_Env.curmodule =
                                            (uu___1987_14722.FStar_TypeChecker_Env.curmodule);
                                          FStar_TypeChecker_Env.gamma =
                                            (uu___1987_14722.FStar_TypeChecker_Env.gamma);
                                          FStar_TypeChecker_Env.gamma_sig =
                                            (uu___1987_14722.FStar_TypeChecker_Env.gamma_sig);
                                          FStar_TypeChecker_Env.gamma_cache =
                                            (uu___1987_14722.FStar_TypeChecker_Env.gamma_cache);
                                          FStar_TypeChecker_Env.modules =
                                            (uu___1987_14722.FStar_TypeChecker_Env.modules);
                                          FStar_TypeChecker_Env.expected_typ
                                            =
                                            (uu___1987_14722.FStar_TypeChecker_Env.expected_typ);
                                          FStar_TypeChecker_Env.sigtab =
                                            (uu___1987_14722.FStar_TypeChecker_Env.sigtab);
                                          FStar_TypeChecker_Env.attrtab =
                                            (uu___1987_14722.FStar_TypeChecker_Env.attrtab);
                                          FStar_TypeChecker_Env.instantiate_imp
                                            =
                                            (uu___1987_14722.FStar_TypeChecker_Env.instantiate_imp);
                                          FStar_TypeChecker_Env.effects =
                                            (uu___1987_14722.FStar_TypeChecker_Env.effects);
                                          FStar_TypeChecker_Env.generalize =
                                            (uu___1987_14722.FStar_TypeChecker_Env.generalize);
                                          FStar_TypeChecker_Env.letrecs =
                                            (uu___1987_14722.FStar_TypeChecker_Env.letrecs);
                                          FStar_TypeChecker_Env.top_level =
                                            (uu___1987_14722.FStar_TypeChecker_Env.top_level);
                                          FStar_TypeChecker_Env.check_uvars =
                                            (uu___1987_14722.FStar_TypeChecker_Env.check_uvars);
                                          FStar_TypeChecker_Env.use_eq =
                                            use_eq;
                                          FStar_TypeChecker_Env.is_iface =
                                            (uu___1987_14722.FStar_TypeChecker_Env.is_iface);
                                          FStar_TypeChecker_Env.admit =
                                            (uu___1987_14722.FStar_TypeChecker_Env.admit);
                                          FStar_TypeChecker_Env.lax =
                                            (uu___1987_14722.FStar_TypeChecker_Env.lax);
                                          FStar_TypeChecker_Env.lax_universes
                                            =
                                            (uu___1987_14722.FStar_TypeChecker_Env.lax_universes);
                                          FStar_TypeChecker_Env.phase1 =
                                            (uu___1987_14722.FStar_TypeChecker_Env.phase1);
                                          FStar_TypeChecker_Env.failhard =
                                            (uu___1987_14722.FStar_TypeChecker_Env.failhard);
                                          FStar_TypeChecker_Env.nosynth =
                                            (uu___1987_14722.FStar_TypeChecker_Env.nosynth);
                                          FStar_TypeChecker_Env.uvar_subtyping
                                            =
                                            (uu___1987_14722.FStar_TypeChecker_Env.uvar_subtyping);
                                          FStar_TypeChecker_Env.tc_term =
                                            (uu___1987_14722.FStar_TypeChecker_Env.tc_term);
                                          FStar_TypeChecker_Env.type_of =
                                            (uu___1987_14722.FStar_TypeChecker_Env.type_of);
                                          FStar_TypeChecker_Env.universe_of =
                                            (uu___1987_14722.FStar_TypeChecker_Env.universe_of);
                                          FStar_TypeChecker_Env.check_type_of
                                            =
                                            (uu___1987_14722.FStar_TypeChecker_Env.check_type_of);
                                          FStar_TypeChecker_Env.use_bv_sorts
                                            =
                                            (uu___1987_14722.FStar_TypeChecker_Env.use_bv_sorts);
                                          FStar_TypeChecker_Env.qtbl_name_and_index
                                            =
                                            (uu___1987_14722.FStar_TypeChecker_Env.qtbl_name_and_index);
                                          FStar_TypeChecker_Env.normalized_eff_names
                                            =
                                            (uu___1987_14722.FStar_TypeChecker_Env.normalized_eff_names);
                                          FStar_TypeChecker_Env.fv_delta_depths
                                            =
                                            (uu___1987_14722.FStar_TypeChecker_Env.fv_delta_depths);
                                          FStar_TypeChecker_Env.proof_ns =
                                            (uu___1987_14722.FStar_TypeChecker_Env.proof_ns);
                                          FStar_TypeChecker_Env.synth_hook =
                                            (uu___1987_14722.FStar_TypeChecker_Env.synth_hook);
                                          FStar_TypeChecker_Env.splice =
                                            (uu___1987_14722.FStar_TypeChecker_Env.splice);
                                          FStar_TypeChecker_Env.mpreprocess =
                                            (uu___1987_14722.FStar_TypeChecker_Env.mpreprocess);
                                          FStar_TypeChecker_Env.postprocess =
                                            (uu___1987_14722.FStar_TypeChecker_Env.postprocess);
                                          FStar_TypeChecker_Env.is_native_tactic
                                            =
                                            (uu___1987_14722.FStar_TypeChecker_Env.is_native_tactic);
                                          FStar_TypeChecker_Env.identifier_info
                                            =
                                            (uu___1987_14722.FStar_TypeChecker_Env.identifier_info);
                                          FStar_TypeChecker_Env.tc_hooks =
                                            (uu___1987_14722.FStar_TypeChecker_Env.tc_hooks);
                                          FStar_TypeChecker_Env.dsenv =
                                            (uu___1987_14722.FStar_TypeChecker_Env.dsenv);
                                          FStar_TypeChecker_Env.nbe =
                                            (uu___1987_14722.FStar_TypeChecker_Env.nbe);
                                          FStar_TypeChecker_Env.strict_args_tab
                                            =
                                            (uu___1987_14722.FStar_TypeChecker_Env.strict_args_tab);
                                          FStar_TypeChecker_Env.erasable_types_tab
                                            =
                                            (uu___1987_14722.FStar_TypeChecker_Env.erasable_types_tab)
                                        }) c_opt (body2, cbody1)
                                      in
                                   (match uu____14713 with
                                    | (body3,cbody2,guard) ->
                                        let uu____14736 =
                                          let uu____14737 =
                                            FStar_TypeChecker_Env.conj_guard
                                              g_lc guard
                                             in
                                          FStar_TypeChecker_Env.conj_guard
                                            guard_body1 uu____14737
                                           in
                                        (body3, cbody2, uu____14736)))
                            else
                              (let uu____14744 =
                                 FStar_TypeChecker_Common.lcomp_comp cbody
                                  in
                               match uu____14744 with
                               | (cbody1,g_lc) ->
                                   let uu____14761 =
                                     FStar_TypeChecker_Env.conj_guard
                                       guard_body1 g_lc
                                      in
                                   (body2, cbody1, uu____14761))
                         in
                      match uu____14572 with
                      | (body2,cbody,guard_body) ->
                          let guard =
                            let uu____14784 =
                              env1.FStar_TypeChecker_Env.top_level ||
                                (let uu____14787 =
                                   FStar_TypeChecker_Env.should_verify env1
                                    in
                                 Prims.op_Negation uu____14787)
                               in
                            if uu____14784
                            then
                              let uu____14790 =
                                FStar_TypeChecker_Rel.discharge_guard env1
                                  g_env
                                 in
                              let uu____14791 =
                                FStar_TypeChecker_Rel.discharge_guard
                                  envbody1 guard_body
                                 in
                              FStar_TypeChecker_Env.conj_guard uu____14790
                                uu____14791
                            else
                              (let guard =
                                 let uu____14795 =
                                   FStar_TypeChecker_Env.close_guard env1
                                     (FStar_List.append bs1 letrec_binders)
                                     guard_body
                                    in
                                 FStar_TypeChecker_Env.conj_guard g_env
                                   uu____14795
                                  in
                               guard)
                             in
                          let guard1 =
                            FStar_TypeChecker_Util.close_guard_implicits env1
                              false bs1 guard
                             in
                          let tfun_computed =
                            FStar_Syntax_Util.arrow bs1 cbody  in
                          let e =
                            FStar_Syntax_Util.abs bs1 body2
                              (FStar_Pervasives_Native.Some
                                 (FStar_Syntax_Util.residual_comp_of_comp
                                    (FStar_Util.dflt cbody c_opt)))
                             in
                          let uu____14810 =
                            match tfun_opt with
                            | FStar_Pervasives_Native.Some t ->
                                let t1 = FStar_Syntax_Subst.compress t  in
                                let t_annot =
                                  match topt with
                                  | FStar_Pervasives_Native.Some t2 -> t2
                                  | FStar_Pervasives_Native.None  ->
                                      failwith
                                        "Impossible! tc_abs: if tfun_computed is Some, expected topt to also be Some"
                                   in
                                (match t1.FStar_Syntax_Syntax.n with
                                 | FStar_Syntax_Syntax.Tm_arrow uu____14834
                                     -> (e, t_annot, guard1)
                                 | uu____14849 ->
                                     let lc =
                                       let uu____14851 =
                                         FStar_Syntax_Syntax.mk_Total
                                           tfun_computed
                                          in
                                       FStar_All.pipe_right uu____14851
                                         FStar_TypeChecker_Common.lcomp_of_comp
                                        in
                                     let uu____14852 =
                                       FStar_TypeChecker_Util.check_and_ascribe
                                         env1 e lc t1
                                        in
                                     (match uu____14852 with
                                      | (e1,uu____14866,guard') ->
                                          let uu____14868 =
                                            FStar_TypeChecker_Env.conj_guard
                                              guard1 guard'
                                             in
                                          (e1, t_annot, uu____14868)))
                            | FStar_Pervasives_Native.None  ->
                                (e, tfun_computed, guard1)
                             in
                          (match uu____14810 with
                           | (e1,tfun,guard2) ->
                               let c = FStar_Syntax_Syntax.mk_Total tfun  in
                               let uu____14879 =
                                 let uu____14884 =
                                   FStar_TypeChecker_Common.lcomp_of_comp c
                                    in
                                 FStar_TypeChecker_Util.strengthen_precondition
                                   FStar_Pervasives_Native.None env1 e1
                                   uu____14884 guard2
                                  in
                               (match uu____14879 with
                                | (c1,g) -> (e1, c1, g)))))))

and (check_application_args :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term ->
      FStar_Syntax_Syntax.comp ->
        FStar_TypeChecker_Env.guard_t ->
          (FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax *
            FStar_Syntax_Syntax.arg_qualifier FStar_Pervasives_Native.option)
            Prims.list ->
            FStar_Syntax_Syntax.typ FStar_Pervasives_Native.option ->
              (FStar_Syntax_Syntax.term * FStar_TypeChecker_Common.lcomp *
                FStar_TypeChecker_Common.guard_t))
  =
  fun env  ->
    fun head1  ->
      fun chead  ->
        fun ghead  ->
          fun args  ->
            fun expected_topt  ->
              let n_args = FStar_List.length args  in
              let r = FStar_TypeChecker_Env.get_range env  in
              let thead = FStar_Syntax_Util.comp_result chead  in
              (let uu____14935 =
                 FStar_TypeChecker_Env.debug env FStar_Options.High  in
               if uu____14935
               then
                 let uu____14938 =
                   FStar_Range.string_of_range head1.FStar_Syntax_Syntax.pos
                    in
                 let uu____14940 = FStar_Syntax_Print.term_to_string thead
                    in
                 FStar_Util.print2 "(%s) Type of head is %s\n" uu____14938
                   uu____14940
               else ());
              (let monadic_application uu____15022 subst1 arg_comps_rev
                 arg_rets_rev guard fvs bs =
                 match uu____15022 with
                 | (head2,chead1,ghead1,cres) ->
                     let uu____15091 =
                       check_no_escape (FStar_Pervasives_Native.Some head2)
                         env fvs (FStar_Syntax_Util.comp_result cres)
                        in
                     (match uu____15091 with
                      | (rt,g0) ->
                          let cres1 =
                            FStar_Syntax_Util.set_result_typ cres rt  in
                          let uu____15105 =
                            match bs with
                            | [] ->
                                let g =
                                  let uu____15121 =
                                    FStar_TypeChecker_Env.conj_guard ghead1
                                      guard
                                     in
                                  FStar_All.pipe_left
                                    (FStar_TypeChecker_Env.conj_guard g0)
                                    uu____15121
                                   in
                                (cres1, g)
                            | uu____15122 ->
                                let g =
                                  let uu____15132 =
                                    let uu____15133 =
                                      FStar_TypeChecker_Env.conj_guard ghead1
                                        guard
                                       in
                                    FStar_All.pipe_right uu____15133
                                      (FStar_TypeChecker_Rel.solve_deferred_constraints
                                         env)
                                     in
                                  FStar_TypeChecker_Env.conj_guard g0
                                    uu____15132
                                   in
                                let uu____15134 =
                                  let uu____15135 =
                                    FStar_Syntax_Util.arrow bs cres1  in
                                  FStar_Syntax_Syntax.mk_Total uu____15135
                                   in
                                (uu____15134, g)
                             in
                          (match uu____15105 with
                           | (cres2,guard1) ->
                               ((let uu____15145 =
                                   FStar_TypeChecker_Env.debug env
                                     FStar_Options.Medium
                                    in
                                 if uu____15145
                                 then
                                   let uu____15148 =
                                     FStar_Syntax_Print.comp_to_string cres2
                                      in
                                   FStar_Util.print1
                                     "\t Type of result cres is %s\n"
                                     uu____15148
                                 else ());
                                (let uu____15153 =
                                   let uu____15158 =
                                     let uu____15159 =
                                       FStar_Syntax_Subst.subst_comp subst1
                                         chead1
                                        in
                                     FStar_All.pipe_right uu____15159
                                       FStar_TypeChecker_Common.lcomp_of_comp
                                      in
                                   let uu____15160 =
                                     let uu____15161 =
                                       FStar_Syntax_Subst.subst_comp subst1
                                         cres2
                                        in
                                     FStar_All.pipe_right uu____15161
                                       FStar_TypeChecker_Common.lcomp_of_comp
                                      in
                                   (uu____15158, uu____15160)  in
                                 match uu____15153 with
                                 | (chead2,cres3) ->
                                     let cres4 =
                                       let head_is_pure_and_some_arg_is_effectful
                                         =
                                         (FStar_TypeChecker_Common.is_pure_or_ghost_lcomp
                                            chead2)
                                           &&
                                           (FStar_Util.for_some
                                              (fun uu____15185  ->
                                                 match uu____15185 with
                                                 | (uu____15195,uu____15196,lc)
                                                     ->
                                                     (let uu____15204 =
                                                        FStar_TypeChecker_Common.is_pure_or_ghost_lcomp
                                                          lc
                                                         in
                                                      Prims.op_Negation
                                                        uu____15204)
                                                       ||
                                                       (FStar_TypeChecker_Util.should_not_inline_lc
                                                          lc)) arg_comps_rev)
                                          in
                                       let term =
                                         FStar_Syntax_Syntax.mk_Tm_app head2
                                           (FStar_List.rev arg_rets_rev)
                                           FStar_Pervasives_Native.None
                                           head2.FStar_Syntax_Syntax.pos
                                          in
                                       let uu____15217 =
                                         (FStar_TypeChecker_Common.is_pure_or_ghost_lcomp
                                            cres3)
                                           &&
                                           head_is_pure_and_some_arg_is_effectful
                                          in
                                       if uu____15217
                                       then
                                         ((let uu____15221 =
                                             FStar_TypeChecker_Env.debug env
                                               FStar_Options.Extreme
                                              in
                                           if uu____15221
                                           then
                                             let uu____15224 =
                                               FStar_Syntax_Print.term_to_string
                                                 term
                                                in
                                             FStar_Util.print1
                                               "(a) Monadic app: Return inserted in monadic application: %s\n"
                                               uu____15224
                                           else ());
                                          FStar_TypeChecker_Util.maybe_assume_result_eq_pure_term
                                            env term cres3)
                                       else
                                         ((let uu____15232 =
                                             FStar_TypeChecker_Env.debug env
                                               FStar_Options.Extreme
                                              in
                                           if uu____15232
                                           then
                                             let uu____15235 =
                                               FStar_Syntax_Print.term_to_string
                                                 term
                                                in
                                             FStar_Util.print1
                                               "(a) Monadic app: No return inserted in monadic application: %s\n"
                                               uu____15235
                                           else ());
                                          cres3)
                                        in
                                     let comp =
                                       FStar_List.fold_left
                                         (fun out_c  ->
                                            fun uu____15266  ->
                                              match uu____15266 with
                                              | ((e,q),x,c) ->
                                                  ((let uu____15308 =
                                                      FStar_TypeChecker_Env.debug
                                                        env
                                                        FStar_Options.Extreme
                                                       in
                                                    if uu____15308
                                                    then
                                                      let uu____15311 =
                                                        match x with
                                                        | FStar_Pervasives_Native.None
                                                             -> "_"
                                                        | FStar_Pervasives_Native.Some
                                                            x1 ->
                                                            FStar_Syntax_Print.bv_to_string
                                                              x1
                                                         in
                                                      let uu____15316 =
                                                        FStar_Syntax_Print.term_to_string
                                                          e
                                                         in
                                                      let uu____15318 =
                                                        FStar_TypeChecker_Common.lcomp_to_string
                                                          c
                                                         in
                                                      FStar_Util.print3
                                                        "(b) Monadic app: Binding argument %s : %s of type (%s)\n"
                                                        uu____15311
                                                        uu____15316
                                                        uu____15318
                                                    else ());
                                                   (let uu____15323 =
                                                      FStar_TypeChecker_Common.is_pure_or_ghost_lcomp
                                                        c
                                                       in
                                                    if uu____15323
                                                    then
                                                      FStar_TypeChecker_Util.bind
                                                        e.FStar_Syntax_Syntax.pos
                                                        env
                                                        (FStar_Pervasives_Native.Some
                                                           e) c (x, out_c)
                                                    else
                                                      FStar_TypeChecker_Util.bind
                                                        e.FStar_Syntax_Syntax.pos
                                                        env
                                                        FStar_Pervasives_Native.None
                                                        c (x, out_c)))) cres4
                                         arg_comps_rev
                                        in
                                     let comp1 =
                                       (let uu____15334 =
                                          FStar_TypeChecker_Env.debug env
                                            FStar_Options.Extreme
                                           in
                                        if uu____15334
                                        then
                                          let uu____15337 =
                                            FStar_Syntax_Print.term_to_string
                                              head2
                                             in
                                          FStar_Util.print1
                                            "(c) Monadic app: Binding head %s\n"
                                            uu____15337
                                        else ());
                                       (let uu____15342 =
                                          FStar_TypeChecker_Common.is_pure_or_ghost_lcomp
                                            chead2
                                           in
                                        if uu____15342
                                        then
                                          FStar_TypeChecker_Util.bind
                                            head2.FStar_Syntax_Syntax.pos env
                                            (FStar_Pervasives_Native.Some
                                               head2) chead2
                                            (FStar_Pervasives_Native.None,
                                              comp)
                                        else
                                          FStar_TypeChecker_Util.bind
                                            head2.FStar_Syntax_Syntax.pos env
                                            FStar_Pervasives_Native.None
                                            chead2
                                            (FStar_Pervasives_Native.None,
                                              comp))
                                        in
                                     let shortcuts_evaluation_order =
                                       let uu____15353 =
                                         let uu____15354 =
                                           FStar_Syntax_Subst.compress head2
                                            in
                                         uu____15354.FStar_Syntax_Syntax.n
                                          in
                                       match uu____15353 with
                                       | FStar_Syntax_Syntax.Tm_fvar fv ->
                                           (FStar_Syntax_Syntax.fv_eq_lid fv
                                              FStar_Parser_Const.op_And)
                                             ||
                                             (FStar_Syntax_Syntax.fv_eq_lid
                                                fv FStar_Parser_Const.op_Or)
                                       | uu____15359 -> false  in
                                     let app =
                                       if shortcuts_evaluation_order
                                       then
                                         let args1 =
                                           FStar_List.fold_left
                                             (fun args1  ->
                                                fun uu____15382  ->
                                                  match uu____15382 with
                                                  | (arg,uu____15396,uu____15397)
                                                      -> arg :: args1) []
                                             arg_comps_rev
                                            in
                                         let app =
                                           FStar_Syntax_Syntax.mk_Tm_app
                                             head2 args1
                                             FStar_Pervasives_Native.None r
                                            in
                                         let app1 =
                                           FStar_TypeChecker_Util.maybe_lift
                                             env app
                                             cres4.FStar_TypeChecker_Common.eff_name
                                             comp1.FStar_TypeChecker_Common.eff_name
                                             comp1.FStar_TypeChecker_Common.res_typ
                                            in
                                         FStar_TypeChecker_Util.maybe_monadic
                                           env app1
                                           comp1.FStar_TypeChecker_Common.eff_name
                                           comp1.FStar_TypeChecker_Common.res_typ
                                       else
                                         (let uu____15408 =
                                            let map_fun uu____15474 =
                                              match uu____15474 with
                                              | ((e,q),uu____15515,c) ->
                                                  ((let uu____15538 =
                                                      FStar_TypeChecker_Env.debug
                                                        env
                                                        FStar_Options.Extreme
                                                       in
                                                    if uu____15538
                                                    then
                                                      let uu____15541 =
                                                        FStar_Syntax_Print.term_to_string
                                                          e
                                                         in
                                                      let uu____15543 =
                                                        FStar_TypeChecker_Common.lcomp_to_string
                                                          c
                                                         in
                                                      FStar_Util.print2
                                                        "For arg e=(%s) c=(%s)... "
                                                        uu____15541
                                                        uu____15543
                                                    else ());
                                                   (let uu____15548 =
                                                      FStar_TypeChecker_Common.is_pure_or_ghost_lcomp
                                                        c
                                                       in
                                                    if uu____15548
                                                    then
                                                      ((let uu____15574 =
                                                          FStar_TypeChecker_Env.debug
                                                            env
                                                            FStar_Options.Extreme
                                                           in
                                                        if uu____15574
                                                        then
                                                          FStar_Util.print_string
                                                            "... not lifting\n"
                                                        else ());
                                                       (FStar_Pervasives_Native.None,
                                                         (e, q)))
                                                    else
                                                      (let warn_effectful_args
                                                         =
                                                         (FStar_TypeChecker_Util.must_erase_for_extraction
                                                            env
                                                            chead2.FStar_TypeChecker_Common.res_typ)
                                                           &&
                                                           (let uu____15615 =
                                                              let uu____15617
                                                                =
                                                                let uu____15618
                                                                  =
                                                                  FStar_Syntax_Util.un_uinst
                                                                    head2
                                                                   in
                                                                uu____15618.FStar_Syntax_Syntax.n
                                                                 in
                                                              match uu____15617
                                                              with
                                                              | FStar_Syntax_Syntax.Tm_fvar
                                                                  fv ->
                                                                  let uu____15623
                                                                    =
                                                                    FStar_Parser_Const.psconst
                                                                    "ignore"
                                                                     in
                                                                  FStar_Syntax_Syntax.fv_eq_lid
                                                                    fv
                                                                    uu____15623
                                                              | uu____15625
                                                                  -> true
                                                               in
                                                            Prims.op_Negation
                                                              uu____15615)
                                                          in
                                                       if warn_effectful_args
                                                       then
                                                         (let uu____15629 =
                                                            let uu____15635 =
                                                              let uu____15637
                                                                =
                                                                FStar_Syntax_Print.term_to_string
                                                                  e
                                                                 in
                                                              let uu____15639
                                                                =
                                                                FStar_Syntax_Print.term_to_string
                                                                  head2
                                                                 in
                                                              FStar_Util.format3
                                                                "Effectful argument %s (%s) to erased function %s, consider let binding it"
                                                                uu____15637
                                                                (c.FStar_TypeChecker_Common.eff_name).FStar_Ident.str
                                                                uu____15639
                                                               in
                                                            (FStar_Errors.Warning_EffectfulArgumentToErasedFunction,
                                                              uu____15635)
                                                             in
                                                          FStar_Errors.log_issue
                                                            e.FStar_Syntax_Syntax.pos
                                                            uu____15629)
                                                       else ();
                                                       (let uu____15646 =
                                                          FStar_TypeChecker_Env.debug
                                                            env
                                                            FStar_Options.Extreme
                                                           in
                                                        if uu____15646
                                                        then
                                                          FStar_Util.print_string
                                                            "... lifting!\n"
                                                        else ());
                                                       (let x =
                                                          FStar_Syntax_Syntax.new_bv
                                                            FStar_Pervasives_Native.None
                                                            c.FStar_TypeChecker_Common.res_typ
                                                           in
                                                        let e1 =
                                                          FStar_TypeChecker_Util.maybe_lift
                                                            env e
                                                            c.FStar_TypeChecker_Common.eff_name
                                                            comp1.FStar_TypeChecker_Common.eff_name
                                                            c.FStar_TypeChecker_Common.res_typ
                                                           in
                                                        let uu____15654 =
                                                          let uu____15663 =
                                                            FStar_Syntax_Syntax.bv_to_name
                                                              x
                                                             in
                                                          (uu____15663, q)
                                                           in
                                                        ((FStar_Pervasives_Native.Some
                                                            (x,
                                                              (c.FStar_TypeChecker_Common.eff_name),
                                                              (c.FStar_TypeChecker_Common.res_typ),
                                                              e1)),
                                                          uu____15654)))))
                                               in
                                            let uu____15692 =
                                              let uu____15723 =
                                                let uu____15752 =
                                                  let uu____15763 =
                                                    let uu____15772 =
                                                      FStar_Syntax_Syntax.as_arg
                                                        head2
                                                       in
                                                    (uu____15772,
                                                      FStar_Pervasives_Native.None,
                                                      chead2)
                                                     in
                                                  uu____15763 ::
                                                    arg_comps_rev
                                                   in
                                                FStar_List.map map_fun
                                                  uu____15752
                                                 in
                                              FStar_All.pipe_left
                                                FStar_List.split uu____15723
                                               in
                                            match uu____15692 with
                                            | (lifted_args,reverse_args) ->
                                                let uu____15973 =
                                                  let uu____15974 =
                                                    FStar_List.hd
                                                      reverse_args
                                                     in
                                                  FStar_Pervasives_Native.fst
                                                    uu____15974
                                                   in
                                                let uu____15995 =
                                                  let uu____15996 =
                                                    FStar_List.tl
                                                      reverse_args
                                                     in
                                                  FStar_List.rev uu____15996
                                                   in
                                                (lifted_args, uu____15973,
                                                  uu____15995)
                                             in
                                          match uu____15408 with
                                          | (lifted_args,head3,args1) ->
                                              let app =
                                                FStar_Syntax_Syntax.mk_Tm_app
                                                  head3 args1
                                                  FStar_Pervasives_Native.None
                                                  r
                                                 in
                                              let app1 =
                                                FStar_TypeChecker_Util.maybe_lift
                                                  env app
                                                  cres4.FStar_TypeChecker_Common.eff_name
                                                  comp1.FStar_TypeChecker_Common.eff_name
                                                  comp1.FStar_TypeChecker_Common.res_typ
                                                 in
                                              let app2 =
                                                FStar_TypeChecker_Util.maybe_monadic
                                                  env app1
                                                  comp1.FStar_TypeChecker_Common.eff_name
                                                  comp1.FStar_TypeChecker_Common.res_typ
                                                 in
                                              let bind_lifted_args e
                                                uu___6_16107 =
                                                match uu___6_16107 with
                                                | FStar_Pervasives_Native.None
                                                     -> e
                                                | FStar_Pervasives_Native.Some
                                                    (x,m,t,e1) ->
                                                    let lb =
                                                      FStar_Syntax_Util.mk_letbinding
                                                        (FStar_Util.Inl x) []
                                                        t m e1 []
                                                        e1.FStar_Syntax_Syntax.pos
                                                       in
                                                    let letbinding =
                                                      let uu____16168 =
                                                        let uu____16175 =
                                                          let uu____16176 =
                                                            let uu____16190 =
                                                              let uu____16193
                                                                =
                                                                let uu____16194
                                                                  =
                                                                  FStar_Syntax_Syntax.mk_binder
                                                                    x
                                                                   in
                                                                [uu____16194]
                                                                 in
                                                              FStar_Syntax_Subst.close
                                                                uu____16193 e
                                                               in
                                                            ((false, [lb]),
                                                              uu____16190)
                                                             in
                                                          FStar_Syntax_Syntax.Tm_let
                                                            uu____16176
                                                           in
                                                        FStar_Syntax_Syntax.mk
                                                          uu____16175
                                                         in
                                                      uu____16168
                                                        FStar_Pervasives_Native.None
                                                        e.FStar_Syntax_Syntax.pos
                                                       in
                                                    FStar_Syntax_Syntax.mk
                                                      (FStar_Syntax_Syntax.Tm_meta
                                                         (letbinding,
                                                           (FStar_Syntax_Syntax.Meta_monadic
                                                              (m,
                                                                (comp1.FStar_TypeChecker_Common.res_typ)))))
                                                      FStar_Pervasives_Native.None
                                                      e.FStar_Syntax_Syntax.pos
                                                 in
                                              FStar_List.fold_left
                                                bind_lifted_args app2
                                                lifted_args)
                                        in
                                     let uu____16246 =
                                       FStar_TypeChecker_Util.strengthen_precondition
                                         FStar_Pervasives_Native.None env app
                                         comp1 guard1
                                        in
                                     (match uu____16246 with
                                      | (comp2,g) ->
                                          ((let uu____16264 =
                                              FStar_TypeChecker_Env.debug env
                                                FStar_Options.Extreme
                                               in
                                            if uu____16264
                                            then
                                              let uu____16267 =
                                                FStar_Syntax_Print.term_to_string
                                                  app
                                                 in
                                              let uu____16269 =
                                                FStar_TypeChecker_Common.lcomp_to_string
                                                  comp2
                                                 in
                                              FStar_Util.print2
                                                "(d) Monadic app: type of app\n\t(%s)\n\t: %s\n"
                                                uu____16267 uu____16269
                                            else ());
                                           (app, comp2, g)))))))
                  in
               let rec tc_args head_info uu____16350 bs args1 =
                 match uu____16350 with
                 | (subst1,outargs,arg_rets,g,fvs) ->
                     (match (bs, args1) with
                      | ((x,FStar_Pervasives_Native.Some
                          (FStar_Syntax_Syntax.Implicit uu____16489))::rest,
                         (uu____16491,FStar_Pervasives_Native.None )::uu____16492)
                          ->
                          let t =
                            FStar_Syntax_Subst.subst subst1
                              x.FStar_Syntax_Syntax.sort
                             in
                          let uu____16553 =
                            check_no_escape
                              (FStar_Pervasives_Native.Some head1) env fvs t
                             in
                          (match uu____16553 with
                           | (t1,g_ex) ->
                               let uu____16566 =
                                 FStar_TypeChecker_Util.new_implicit_var
                                   "Instantiating implicit argument in application"
                                   head1.FStar_Syntax_Syntax.pos env t1
                                  in
                               (match uu____16566 with
                                | (varg,uu____16587,implicits) ->
                                    let subst2 =
                                      (FStar_Syntax_Syntax.NT (x, varg)) ::
                                      subst1  in
                                    let arg =
                                      let uu____16615 =
                                        FStar_Syntax_Syntax.as_implicit true
                                         in
                                      (varg, uu____16615)  in
                                    let guard =
                                      FStar_List.fold_right
                                        FStar_TypeChecker_Env.conj_guard
                                        [g_ex; g] implicits
                                       in
                                    let uu____16624 =
                                      let uu____16659 =
                                        let uu____16670 =
                                          let uu____16679 =
                                            let uu____16680 =
                                              FStar_Syntax_Syntax.mk_Total t1
                                               in
                                            FStar_All.pipe_right uu____16680
                                              FStar_TypeChecker_Common.lcomp_of_comp
                                             in
                                          (arg, FStar_Pervasives_Native.None,
                                            uu____16679)
                                           in
                                        uu____16670 :: outargs  in
                                      (subst2, uu____16659, (arg ::
                                        arg_rets), guard, fvs)
                                       in
                                    tc_args head_info uu____16624 rest args1))
                      | ((x,FStar_Pervasives_Native.Some
                          (FStar_Syntax_Syntax.Meta tau))::rest,(uu____16726,FStar_Pervasives_Native.None
                                                                 )::uu____16727)
                          ->
                          let tau1 = FStar_Syntax_Subst.subst subst1 tau  in
                          let uu____16789 =
                            tc_tactic FStar_Syntax_Syntax.t_unit
                              FStar_Syntax_Syntax.t_unit env tau1
                             in
                          (match uu____16789 with
                           | (tau2,uu____16803,g_tau) ->
                               let t =
                                 FStar_Syntax_Subst.subst subst1
                                   x.FStar_Syntax_Syntax.sort
                                  in
                               let uu____16806 =
                                 check_no_escape
                                   (FStar_Pervasives_Native.Some head1) env
                                   fvs t
                                  in
                               (match uu____16806 with
                                | (t1,g_ex) ->
                                    let uu____16819 =
                                      let uu____16832 =
                                        let uu____16839 =
                                          let uu____16844 =
                                            FStar_Dyn.mkdyn env  in
                                          (uu____16844, tau2)  in
                                        FStar_Pervasives_Native.Some
                                          uu____16839
                                         in
                                      FStar_TypeChecker_Env.new_implicit_var_aux
                                        "Instantiating meta argument in application"
                                        head1.FStar_Syntax_Syntax.pos env t1
                                        FStar_Syntax_Syntax.Strict
                                        uu____16832
                                       in
                                    (match uu____16819 with
                                     | (varg,uu____16857,implicits) ->
                                         let subst2 =
                                           (FStar_Syntax_Syntax.NT (x, varg))
                                           :: subst1  in
                                         let arg =
                                           let uu____16885 =
                                             FStar_Syntax_Syntax.as_implicit
                                               true
                                              in
                                           (varg, uu____16885)  in
                                         let guard =
                                           FStar_List.fold_right
                                             FStar_TypeChecker_Env.conj_guard
                                             [g_ex; g; g_tau] implicits
                                            in
                                         let uu____16894 =
                                           let uu____16929 =
                                             let uu____16940 =
                                               let uu____16949 =
                                                 let uu____16950 =
                                                   FStar_Syntax_Syntax.mk_Total
                                                     t1
                                                    in
                                                 FStar_All.pipe_right
                                                   uu____16950
                                                   FStar_TypeChecker_Common.lcomp_of_comp
                                                  in
                                               (arg,
                                                 FStar_Pervasives_Native.None,
                                                 uu____16949)
                                                in
                                             uu____16940 :: outargs  in
                                           (subst2, uu____16929, (arg ::
                                             arg_rets), guard, fvs)
                                            in
                                         tc_args head_info uu____16894 rest
                                           args1)))
                      | ((x,aqual)::rest,(e,aq)::rest') ->
                          ((match (aqual, aq) with
                            | (uu____17066,FStar_Pervasives_Native.Some
                               (FStar_Syntax_Syntax.Meta uu____17067)) ->
                                FStar_Errors.raise_error
                                  (FStar_Errors.Fatal_InconsistentImplicitQualifier,
                                    "Inconsistent implicit qualifier; cannot apply meta arguments, just use #")
                                  e.FStar_Syntax_Syntax.pos
                            | (FStar_Pervasives_Native.Some
                               (FStar_Syntax_Syntax.Meta
                               uu____17078),FStar_Pervasives_Native.Some
                               (FStar_Syntax_Syntax.Implicit uu____17079)) ->
                                ()
                            | (FStar_Pervasives_Native.Some
                               (FStar_Syntax_Syntax.Implicit
                               uu____17087),FStar_Pervasives_Native.Some
                               (FStar_Syntax_Syntax.Implicit uu____17088)) ->
                                ()
                            | (FStar_Pervasives_Native.None
                               ,FStar_Pervasives_Native.None ) -> ()
                            | (FStar_Pervasives_Native.Some
                               (FStar_Syntax_Syntax.Equality
                               ),FStar_Pervasives_Native.None ) -> ()
                            | uu____17103 ->
                                let uu____17112 =
                                  let uu____17118 =
                                    let uu____17120 =
                                      FStar_Syntax_Print.aqual_to_string
                                        aqual
                                       in
                                    let uu____17122 =
                                      FStar_Syntax_Print.aqual_to_string aq
                                       in
                                    let uu____17124 =
                                      FStar_Syntax_Print.bv_to_string x  in
                                    let uu____17126 =
                                      FStar_Syntax_Print.term_to_string e  in
                                    FStar_Util.format4
                                      "Inconsistent implicit qualifier; %s vs %s\nfor bvar %s and term %s"
                                      uu____17120 uu____17122 uu____17124
                                      uu____17126
                                     in
                                  (FStar_Errors.Fatal_InconsistentImplicitQualifier,
                                    uu____17118)
                                   in
                                FStar_Errors.raise_error uu____17112
                                  e.FStar_Syntax_Syntax.pos);
                           (let targ =
                              FStar_Syntax_Subst.subst subst1
                                x.FStar_Syntax_Syntax.sort
                               in
                            let aqual1 =
                              FStar_Syntax_Subst.subst_imp subst1 aqual  in
                            let x1 =
                              let uu___2266_17133 = x  in
                              {
                                FStar_Syntax_Syntax.ppname =
                                  (uu___2266_17133.FStar_Syntax_Syntax.ppname);
                                FStar_Syntax_Syntax.index =
                                  (uu___2266_17133.FStar_Syntax_Syntax.index);
                                FStar_Syntax_Syntax.sort = targ
                              }  in
                            (let uu____17135 =
                               FStar_TypeChecker_Env.debug env
                                 FStar_Options.Extreme
                                in
                             if uu____17135
                             then
                               let uu____17138 =
                                 FStar_Syntax_Print.bv_to_string x1  in
                               let uu____17140 =
                                 FStar_Syntax_Print.term_to_string
                                   x1.FStar_Syntax_Syntax.sort
                                  in
                               let uu____17142 =
                                 FStar_Syntax_Print.term_to_string e  in
                               let uu____17144 =
                                 FStar_Syntax_Print.subst_to_string subst1
                                  in
                               let uu____17146 =
                                 FStar_Syntax_Print.term_to_string targ  in
                               FStar_Util.print5
                                 "\tFormal is %s : %s\tType of arg %s (after subst %s) = %s\n"
                                 uu____17138 uu____17140 uu____17142
                                 uu____17144 uu____17146
                             else ());
                            (let uu____17151 =
                               check_no_escape
                                 (FStar_Pervasives_Native.Some head1) env fvs
                                 targ
                                in
                             match uu____17151 with
                             | (targ1,g_ex) ->
                                 let env1 =
                                   FStar_TypeChecker_Env.set_expected_typ env
                                     targ1
                                    in
                                 let env2 =
                                   let uu___2275_17166 = env1  in
                                   {
                                     FStar_TypeChecker_Env.solver =
                                       (uu___2275_17166.FStar_TypeChecker_Env.solver);
                                     FStar_TypeChecker_Env.range =
                                       (uu___2275_17166.FStar_TypeChecker_Env.range);
                                     FStar_TypeChecker_Env.curmodule =
                                       (uu___2275_17166.FStar_TypeChecker_Env.curmodule);
                                     FStar_TypeChecker_Env.gamma =
                                       (uu___2275_17166.FStar_TypeChecker_Env.gamma);
                                     FStar_TypeChecker_Env.gamma_sig =
                                       (uu___2275_17166.FStar_TypeChecker_Env.gamma_sig);
                                     FStar_TypeChecker_Env.gamma_cache =
                                       (uu___2275_17166.FStar_TypeChecker_Env.gamma_cache);
                                     FStar_TypeChecker_Env.modules =
                                       (uu___2275_17166.FStar_TypeChecker_Env.modules);
                                     FStar_TypeChecker_Env.expected_typ =
                                       (uu___2275_17166.FStar_TypeChecker_Env.expected_typ);
                                     FStar_TypeChecker_Env.sigtab =
                                       (uu___2275_17166.FStar_TypeChecker_Env.sigtab);
                                     FStar_TypeChecker_Env.attrtab =
                                       (uu___2275_17166.FStar_TypeChecker_Env.attrtab);
                                     FStar_TypeChecker_Env.instantiate_imp =
                                       (uu___2275_17166.FStar_TypeChecker_Env.instantiate_imp);
                                     FStar_TypeChecker_Env.effects =
                                       (uu___2275_17166.FStar_TypeChecker_Env.effects);
                                     FStar_TypeChecker_Env.generalize =
                                       (uu___2275_17166.FStar_TypeChecker_Env.generalize);
                                     FStar_TypeChecker_Env.letrecs =
                                       (uu___2275_17166.FStar_TypeChecker_Env.letrecs);
                                     FStar_TypeChecker_Env.top_level =
                                       (uu___2275_17166.FStar_TypeChecker_Env.top_level);
                                     FStar_TypeChecker_Env.check_uvars =
                                       (uu___2275_17166.FStar_TypeChecker_Env.check_uvars);
                                     FStar_TypeChecker_Env.use_eq =
                                       (is_eq aqual1);
                                     FStar_TypeChecker_Env.is_iface =
                                       (uu___2275_17166.FStar_TypeChecker_Env.is_iface);
                                     FStar_TypeChecker_Env.admit =
                                       (uu___2275_17166.FStar_TypeChecker_Env.admit);
                                     FStar_TypeChecker_Env.lax =
                                       (uu___2275_17166.FStar_TypeChecker_Env.lax);
                                     FStar_TypeChecker_Env.lax_universes =
                                       (uu___2275_17166.FStar_TypeChecker_Env.lax_universes);
                                     FStar_TypeChecker_Env.phase1 =
                                       (uu___2275_17166.FStar_TypeChecker_Env.phase1);
                                     FStar_TypeChecker_Env.failhard =
                                       (uu___2275_17166.FStar_TypeChecker_Env.failhard);
                                     FStar_TypeChecker_Env.nosynth =
                                       (uu___2275_17166.FStar_TypeChecker_Env.nosynth);
                                     FStar_TypeChecker_Env.uvar_subtyping =
                                       (uu___2275_17166.FStar_TypeChecker_Env.uvar_subtyping);
                                     FStar_TypeChecker_Env.tc_term =
                                       (uu___2275_17166.FStar_TypeChecker_Env.tc_term);
                                     FStar_TypeChecker_Env.type_of =
                                       (uu___2275_17166.FStar_TypeChecker_Env.type_of);
                                     FStar_TypeChecker_Env.universe_of =
                                       (uu___2275_17166.FStar_TypeChecker_Env.universe_of);
                                     FStar_TypeChecker_Env.check_type_of =
                                       (uu___2275_17166.FStar_TypeChecker_Env.check_type_of);
                                     FStar_TypeChecker_Env.use_bv_sorts =
                                       (uu___2275_17166.FStar_TypeChecker_Env.use_bv_sorts);
                                     FStar_TypeChecker_Env.qtbl_name_and_index
                                       =
                                       (uu___2275_17166.FStar_TypeChecker_Env.qtbl_name_and_index);
                                     FStar_TypeChecker_Env.normalized_eff_names
                                       =
                                       (uu___2275_17166.FStar_TypeChecker_Env.normalized_eff_names);
                                     FStar_TypeChecker_Env.fv_delta_depths =
                                       (uu___2275_17166.FStar_TypeChecker_Env.fv_delta_depths);
                                     FStar_TypeChecker_Env.proof_ns =
                                       (uu___2275_17166.FStar_TypeChecker_Env.proof_ns);
                                     FStar_TypeChecker_Env.synth_hook =
                                       (uu___2275_17166.FStar_TypeChecker_Env.synth_hook);
                                     FStar_TypeChecker_Env.splice =
                                       (uu___2275_17166.FStar_TypeChecker_Env.splice);
                                     FStar_TypeChecker_Env.mpreprocess =
                                       (uu___2275_17166.FStar_TypeChecker_Env.mpreprocess);
                                     FStar_TypeChecker_Env.postprocess =
                                       (uu___2275_17166.FStar_TypeChecker_Env.postprocess);
                                     FStar_TypeChecker_Env.is_native_tactic =
                                       (uu___2275_17166.FStar_TypeChecker_Env.is_native_tactic);
                                     FStar_TypeChecker_Env.identifier_info =
                                       (uu___2275_17166.FStar_TypeChecker_Env.identifier_info);
                                     FStar_TypeChecker_Env.tc_hooks =
                                       (uu___2275_17166.FStar_TypeChecker_Env.tc_hooks);
                                     FStar_TypeChecker_Env.dsenv =
                                       (uu___2275_17166.FStar_TypeChecker_Env.dsenv);
                                     FStar_TypeChecker_Env.nbe =
                                       (uu___2275_17166.FStar_TypeChecker_Env.nbe);
                                     FStar_TypeChecker_Env.strict_args_tab =
                                       (uu___2275_17166.FStar_TypeChecker_Env.strict_args_tab);
                                     FStar_TypeChecker_Env.erasable_types_tab
                                       =
                                       (uu___2275_17166.FStar_TypeChecker_Env.erasable_types_tab)
                                   }  in
                                 ((let uu____17168 =
                                     FStar_TypeChecker_Env.debug env2
                                       FStar_Options.High
                                      in
                                   if uu____17168
                                   then
                                     let uu____17171 =
                                       FStar_Syntax_Print.tag_of_term e  in
                                     let uu____17173 =
                                       FStar_Syntax_Print.term_to_string e
                                        in
                                     let uu____17175 =
                                       FStar_Syntax_Print.term_to_string
                                         targ1
                                        in
                                     FStar_Util.print3
                                       "Checking arg (%s) %s at type %s\n"
                                       uu____17171 uu____17173 uu____17175
                                   else ());
                                  (let uu____17180 = tc_term env2 e  in
                                   match uu____17180 with
                                   | (e1,c,g_e) ->
                                       let g1 =
                                         let uu____17197 =
                                           FStar_TypeChecker_Env.conj_guard g
                                             g_e
                                            in
                                         FStar_All.pipe_left
                                           (FStar_TypeChecker_Env.conj_guard
                                              g_ex) uu____17197
                                          in
                                       let arg = (e1, aq)  in
                                       let xterm =
                                         let uu____17220 =
                                           let uu____17223 =
                                             let uu____17232 =
                                               FStar_Syntax_Syntax.bv_to_name
                                                 x1
                                                in
                                             FStar_Syntax_Syntax.as_arg
                                               uu____17232
                                              in
                                           FStar_Pervasives_Native.fst
                                             uu____17223
                                            in
                                         (uu____17220, aq)  in
                                       let uu____17241 =
                                         (FStar_TypeChecker_Common.is_tot_or_gtot_lcomp
                                            c)
                                           ||
                                           (FStar_TypeChecker_Util.is_pure_or_ghost_effect
                                              env2
                                              c.FStar_TypeChecker_Common.eff_name)
                                          in
                                       if uu____17241
                                       then
                                         let subst2 =
                                           let uu____17251 = FStar_List.hd bs
                                              in
                                           maybe_extend_subst subst1
                                             uu____17251 e1
                                            in
                                         tc_args head_info
                                           (subst2,
                                             ((arg,
                                                (FStar_Pervasives_Native.Some
                                                   x1), c) :: outargs),
                                             (xterm :: arg_rets), g1, fvs)
                                           rest rest'
                                       else
                                         tc_args head_info
                                           (subst1,
                                             ((arg,
                                                (FStar_Pervasives_Native.Some
                                                   x1), c) :: outargs),
                                             (xterm :: arg_rets), g1, (x1 ::
                                             fvs)) rest rest')))))
                      | (uu____17350,[]) ->
                          monadic_application head_info subst1 outargs
                            arg_rets g fvs bs
                      | ([],arg::uu____17386) ->
                          let uu____17437 =
                            monadic_application head_info subst1 outargs
                              arg_rets g fvs []
                             in
                          (match uu____17437 with
                           | (head2,chead1,ghead1) ->
                               let uu____17459 =
                                 let uu____17464 =
                                   FStar_TypeChecker_Common.lcomp_comp chead1
                                    in
                                 FStar_All.pipe_right uu____17464
                                   (fun uu____17481  ->
                                      match uu____17481 with
                                      | (c,g1) ->
                                          let uu____17492 =
                                            FStar_TypeChecker_Env.conj_guard
                                              ghead1 g1
                                             in
                                          (c, uu____17492))
                                  in
                               (match uu____17459 with
                                | (chead2,ghead2) ->
                                    let rec aux norm1 solve ghead3 tres =
                                      let tres1 =
                                        let uu____17535 =
                                          FStar_Syntax_Subst.compress tres
                                           in
                                        FStar_All.pipe_right uu____17535
                                          FStar_Syntax_Util.unrefine
                                         in
                                      match tres1.FStar_Syntax_Syntax.n with
                                      | FStar_Syntax_Syntax.Tm_arrow
                                          (bs1,cres') ->
                                          let uu____17566 =
                                            FStar_Syntax_Subst.open_comp bs1
                                              cres'
                                             in
                                          (match uu____17566 with
                                           | (bs2,cres'1) ->
                                               let head_info1 =
                                                 (head2, chead2, ghead3,
                                                   cres'1)
                                                  in
                                               ((let uu____17589 =
                                                   FStar_TypeChecker_Env.debug
                                                     env FStar_Options.Low
                                                    in
                                                 if uu____17589
                                                 then
                                                   FStar_Errors.log_issue
                                                     tres1.FStar_Syntax_Syntax.pos
                                                     (FStar_Errors.Warning_RedundantExplicitCurrying,
                                                       "Potentially redundant explicit currying of a function type")
                                                 else ());
                                                tc_args head_info1
                                                  ([], [], [],
                                                    FStar_TypeChecker_Env.trivial_guard,
                                                    []) bs2 args1))
                                      | uu____17636 when
                                          Prims.op_Negation norm1 ->
                                          let rec norm_tres tres2 =
                                            let tres3 =
                                              let uu____17644 =
                                                FStar_All.pipe_right tres2
                                                  (FStar_TypeChecker_Normalize.unfold_whnf
                                                     env)
                                                 in
                                              FStar_All.pipe_right
                                                uu____17644
                                                FStar_Syntax_Util.unascribe
                                               in
                                            let uu____17645 =
                                              let uu____17646 =
                                                FStar_Syntax_Subst.compress
                                                  tres3
                                                 in
                                              uu____17646.FStar_Syntax_Syntax.n
                                               in
                                            match uu____17645 with
                                            | FStar_Syntax_Syntax.Tm_refine
                                                ({
                                                   FStar_Syntax_Syntax.ppname
                                                     = uu____17649;
                                                   FStar_Syntax_Syntax.index
                                                     = uu____17650;
                                                   FStar_Syntax_Syntax.sort =
                                                     tres4;_},uu____17652)
                                                -> norm_tres tres4
                                            | uu____17660 -> tres3  in
                                          let uu____17661 = norm_tres tres1
                                             in
                                          aux true solve ghead3 uu____17661
                                      | uu____17663 when
                                          Prims.op_Negation solve ->
                                          let ghead4 =
                                            FStar_TypeChecker_Rel.solve_deferred_constraints
                                              env ghead3
                                             in
                                          aux norm1 true ghead4 tres1
                                      | uu____17666 ->
                                          let uu____17667 =
                                            let uu____17673 =
                                              let uu____17675 =
                                                FStar_TypeChecker_Normalize.term_to_string
                                                  env thead
                                                 in
                                              let uu____17677 =
                                                FStar_Util.string_of_int
                                                  n_args
                                                 in
                                              let uu____17679 =
                                                FStar_Syntax_Print.term_to_string
                                                  tres1
                                                 in
                                              FStar_Util.format3
                                                "Too many arguments to function of type %s; got %s arguments, remaining type is %s"
                                                uu____17675 uu____17677
                                                uu____17679
                                               in
                                            (FStar_Errors.Fatal_ToManyArgumentToFunction,
                                              uu____17673)
                                             in
                                          let uu____17683 =
                                            FStar_Syntax_Syntax.argpos arg
                                             in
                                          FStar_Errors.raise_error
                                            uu____17667 uu____17683
                                       in
                                    aux false false ghead2
                                      (FStar_Syntax_Util.comp_result chead2))))
                  in
               let rec check_function_app tf guard =
                 let uu____17713 =
                   let uu____17714 =
                     FStar_TypeChecker_Normalize.unfold_whnf env tf  in
                   uu____17714.FStar_Syntax_Syntax.n  in
                 match uu____17713 with
                 | FStar_Syntax_Syntax.Tm_uvar uu____17723 ->
                     let uu____17736 =
                       FStar_List.fold_right
                         (fun uu____17767  ->
                            fun uu____17768  ->
                              match uu____17768 with
                              | (bs,guard1) ->
                                  let uu____17795 =
                                    let uu____17808 =
                                      let uu____17809 =
                                        FStar_Syntax_Util.type_u ()  in
                                      FStar_All.pipe_right uu____17809
                                        FStar_Pervasives_Native.fst
                                       in
                                    FStar_TypeChecker_Util.new_implicit_var
                                      "formal parameter"
                                      tf.FStar_Syntax_Syntax.pos env
                                      uu____17808
                                     in
                                  (match uu____17795 with
                                   | (t,uu____17826,g) ->
                                       let uu____17840 =
                                         let uu____17843 =
                                           FStar_Syntax_Syntax.null_binder t
                                            in
                                         uu____17843 :: bs  in
                                       let uu____17844 =
                                         FStar_TypeChecker_Env.conj_guard g
                                           guard1
                                          in
                                       (uu____17840, uu____17844))) args
                         ([], guard)
                        in
                     (match uu____17736 with
                      | (bs,guard1) ->
                          let uu____17861 =
                            let uu____17868 =
                              let uu____17881 =
                                let uu____17882 = FStar_Syntax_Util.type_u ()
                                   in
                                FStar_All.pipe_right uu____17882
                                  FStar_Pervasives_Native.fst
                                 in
                              FStar_TypeChecker_Util.new_implicit_var
                                "result type" tf.FStar_Syntax_Syntax.pos env
                                uu____17881
                               in
                            match uu____17868 with
                            | (t,uu____17899,g) ->
                                let uu____17913 = FStar_Options.ml_ish ()  in
                                if uu____17913
                                then
                                  let uu____17922 =
                                    FStar_Syntax_Util.ml_comp t r  in
                                  let uu____17925 =
                                    FStar_TypeChecker_Env.conj_guard guard1 g
                                     in
                                  (uu____17922, uu____17925)
                                else
                                  (let uu____17930 =
                                     FStar_Syntax_Syntax.mk_Total t  in
                                   let uu____17933 =
                                     FStar_TypeChecker_Env.conj_guard guard1
                                       g
                                      in
                                   (uu____17930, uu____17933))
                             in
                          (match uu____17861 with
                           | (cres,guard2) ->
                               let bs_cres = FStar_Syntax_Util.arrow bs cres
                                  in
                               ((let uu____17952 =
                                   FStar_All.pipe_left
                                     (FStar_TypeChecker_Env.debug env)
                                     FStar_Options.Extreme
                                    in
                                 if uu____17952
                                 then
                                   let uu____17956 =
                                     FStar_Syntax_Print.term_to_string head1
                                      in
                                   let uu____17958 =
                                     FStar_Syntax_Print.term_to_string tf  in
                                   let uu____17960 =
                                     FStar_Syntax_Print.term_to_string
                                       bs_cres
                                      in
                                   FStar_Util.print3
                                     "Forcing the type of %s from %s to %s\n"
                                     uu____17956 uu____17958 uu____17960
                                 else ());
                                (let g =
                                   let uu____17966 =
                                     FStar_TypeChecker_Rel.teq env tf bs_cres
                                      in
                                   FStar_TypeChecker_Rel.solve_deferred_constraints
                                     env uu____17966
                                    in
                                 let uu____17967 =
                                   FStar_TypeChecker_Env.conj_guard g guard2
                                    in
                                 check_function_app bs_cres uu____17967))))
                 | FStar_Syntax_Syntax.Tm_app
                     ({
                        FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                          uu____17968;
                        FStar_Syntax_Syntax.pos = uu____17969;
                        FStar_Syntax_Syntax.vars = uu____17970;_},uu____17971)
                     ->
                     let uu____18008 =
                       FStar_List.fold_right
                         (fun uu____18039  ->
                            fun uu____18040  ->
                              match uu____18040 with
                              | (bs,guard1) ->
                                  let uu____18067 =
                                    let uu____18080 =
                                      let uu____18081 =
                                        FStar_Syntax_Util.type_u ()  in
                                      FStar_All.pipe_right uu____18081
                                        FStar_Pervasives_Native.fst
                                       in
                                    FStar_TypeChecker_Util.new_implicit_var
                                      "formal parameter"
                                      tf.FStar_Syntax_Syntax.pos env
                                      uu____18080
                                     in
                                  (match uu____18067 with
                                   | (t,uu____18098,g) ->
                                       let uu____18112 =
                                         let uu____18115 =
                                           FStar_Syntax_Syntax.null_binder t
                                            in
                                         uu____18115 :: bs  in
                                       let uu____18116 =
                                         FStar_TypeChecker_Env.conj_guard g
                                           guard1
                                          in
                                       (uu____18112, uu____18116))) args
                         ([], guard)
                        in
                     (match uu____18008 with
                      | (bs,guard1) ->
                          let uu____18133 =
                            let uu____18140 =
                              let uu____18153 =
                                let uu____18154 = FStar_Syntax_Util.type_u ()
                                   in
                                FStar_All.pipe_right uu____18154
                                  FStar_Pervasives_Native.fst
                                 in
                              FStar_TypeChecker_Util.new_implicit_var
                                "result type" tf.FStar_Syntax_Syntax.pos env
                                uu____18153
                               in
                            match uu____18140 with
                            | (t,uu____18171,g) ->
                                let uu____18185 = FStar_Options.ml_ish ()  in
                                if uu____18185
                                then
                                  let uu____18194 =
                                    FStar_Syntax_Util.ml_comp t r  in
                                  let uu____18197 =
                                    FStar_TypeChecker_Env.conj_guard guard1 g
                                     in
                                  (uu____18194, uu____18197)
                                else
                                  (let uu____18202 =
                                     FStar_Syntax_Syntax.mk_Total t  in
                                   let uu____18205 =
                                     FStar_TypeChecker_Env.conj_guard guard1
                                       g
                                      in
                                   (uu____18202, uu____18205))
                             in
                          (match uu____18133 with
                           | (cres,guard2) ->
                               let bs_cres = FStar_Syntax_Util.arrow bs cres
                                  in
                               ((let uu____18224 =
                                   FStar_All.pipe_left
                                     (FStar_TypeChecker_Env.debug env)
                                     FStar_Options.Extreme
                                    in
                                 if uu____18224
                                 then
                                   let uu____18228 =
                                     FStar_Syntax_Print.term_to_string head1
                                      in
                                   let uu____18230 =
                                     FStar_Syntax_Print.term_to_string tf  in
                                   let uu____18232 =
                                     FStar_Syntax_Print.term_to_string
                                       bs_cres
                                      in
                                   FStar_Util.print3
                                     "Forcing the type of %s from %s to %s\n"
                                     uu____18228 uu____18230 uu____18232
                                 else ());
                                (let g =
                                   let uu____18238 =
                                     FStar_TypeChecker_Rel.teq env tf bs_cres
                                      in
                                   FStar_TypeChecker_Rel.solve_deferred_constraints
                                     env uu____18238
                                    in
                                 let uu____18239 =
                                   FStar_TypeChecker_Env.conj_guard g guard2
                                    in
                                 check_function_app bs_cres uu____18239))))
                 | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
                     let uu____18262 = FStar_Syntax_Subst.open_comp bs c  in
                     (match uu____18262 with
                      | (bs1,c1) ->
                          let head_info = (head1, chead, ghead, c1)  in
                          ((let uu____18285 =
                              FStar_TypeChecker_Env.debug env
                                FStar_Options.Extreme
                               in
                            if uu____18285
                            then
                              let uu____18288 =
                                FStar_Syntax_Print.term_to_string head1  in
                              let uu____18290 =
                                FStar_Syntax_Print.term_to_string tf  in
                              let uu____18292 =
                                FStar_Syntax_Print.binders_to_string ", " bs1
                                 in
                              let uu____18295 =
                                FStar_Syntax_Print.comp_to_string c1  in
                              FStar_Util.print4
                                "######tc_args of head %s @ %s with formals=%s and result type=%s\n"
                                uu____18288 uu____18290 uu____18292
                                uu____18295
                            else ());
                           tc_args head_info ([], [], [], guard, []) bs1 args))
                 | FStar_Syntax_Syntax.Tm_refine (bv,uu____18341) ->
                     check_function_app bv.FStar_Syntax_Syntax.sort guard
                 | FStar_Syntax_Syntax.Tm_ascribed
                     (t,uu____18347,uu____18348) ->
                     check_function_app t guard
                 | uu____18389 ->
                     let uu____18390 =
                       FStar_TypeChecker_Err.expected_function_typ env tf  in
                     FStar_Errors.raise_error uu____18390
                       head1.FStar_Syntax_Syntax.pos
                  in
               check_function_app thead FStar_TypeChecker_Env.trivial_guard)

and (check_short_circuit_args :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term ->
      FStar_Syntax_Syntax.comp ->
        FStar_TypeChecker_Env.guard_t ->
          (FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax *
            FStar_Syntax_Syntax.arg_qualifier FStar_Pervasives_Native.option)
            Prims.list ->
            FStar_Syntax_Syntax.typ FStar_Pervasives_Native.option ->
              (FStar_Syntax_Syntax.term * FStar_TypeChecker_Common.lcomp *
                FStar_TypeChecker_Common.guard_t))
  =
  fun env  ->
    fun head1  ->
      fun chead  ->
        fun g_head  ->
          fun args  ->
            fun expected_topt  ->
              let r = FStar_TypeChecker_Env.get_range env  in
              let tf =
                FStar_Syntax_Subst.compress
                  (FStar_Syntax_Util.comp_result chead)
                 in
              match tf.FStar_Syntax_Syntax.n with
              | FStar_Syntax_Syntax.Tm_arrow (bs,c) when
                  (FStar_Syntax_Util.is_total_comp c) &&
                    ((FStar_List.length bs) = (FStar_List.length args))
                  ->
                  let res_t = FStar_Syntax_Util.comp_result c  in
                  let uu____18473 =
                    FStar_List.fold_left2
                      (fun uu____18542  ->
                         fun uu____18543  ->
                           fun uu____18544  ->
                             match (uu____18542, uu____18543, uu____18544)
                             with
                             | ((seen,guard,ghost),(e,aq),(b,aq')) ->
                                 ((let uu____18697 =
                                     let uu____18699 =
                                       FStar_Syntax_Util.eq_aqual aq aq'  in
                                     uu____18699 <> FStar_Syntax_Util.Equal
                                      in
                                   if uu____18697
                                   then
                                     FStar_Errors.raise_error
                                       (FStar_Errors.Fatal_InconsistentImplicitQualifier,
                                         "Inconsistent implicit qualifiers")
                                       e.FStar_Syntax_Syntax.pos
                                   else ());
                                  (let uu____18705 =
                                     tc_check_tot_or_gtot_term env e
                                       b.FStar_Syntax_Syntax.sort
                                      in
                                   match uu____18705 with
                                   | (e1,c1,g) ->
                                       let short =
                                         FStar_TypeChecker_Util.short_circuit
                                           head1 seen
                                          in
                                       let g1 =
                                         let uu____18734 =
                                           FStar_TypeChecker_Env.guard_of_guard_formula
                                             short
                                            in
                                         FStar_TypeChecker_Env.imp_guard
                                           uu____18734 g
                                          in
                                       let ghost1 =
                                         ghost ||
                                           ((let uu____18739 =
                                               FStar_TypeChecker_Common.is_total_lcomp
                                                 c1
                                                in
                                             Prims.op_Negation uu____18739)
                                              &&
                                              (let uu____18742 =
                                                 FStar_TypeChecker_Util.is_pure_effect
                                                   env
                                                   c1.FStar_TypeChecker_Common.eff_name
                                                  in
                                               Prims.op_Negation uu____18742))
                                          in
                                       let uu____18744 =
                                         let uu____18755 =
                                           let uu____18766 =
                                             FStar_Syntax_Syntax.as_arg e1
                                              in
                                           [uu____18766]  in
                                         FStar_List.append seen uu____18755
                                          in
                                       let uu____18799 =
                                         FStar_TypeChecker_Env.conj_guard
                                           guard g1
                                          in
                                       (uu____18744, uu____18799, ghost1))))
                      ([], g_head, false) args bs
                     in
                  (match uu____18473 with
                   | (args1,guard,ghost) ->
                       let e =
                         FStar_Syntax_Syntax.mk_Tm_app head1 args1
                           FStar_Pervasives_Native.None r
                          in
                       let c1 =
                         if ghost
                         then
                           let uu____18867 =
                             FStar_Syntax_Syntax.mk_GTotal res_t  in
                           FStar_All.pipe_right uu____18867
                             FStar_TypeChecker_Common.lcomp_of_comp
                         else FStar_TypeChecker_Common.lcomp_of_comp c  in
                       let uu____18870 =
                         FStar_TypeChecker_Util.strengthen_precondition
                           FStar_Pervasives_Native.None env e c1 guard
                          in
                       (match uu____18870 with | (c2,g) -> (e, c2, g)))
              | uu____18887 ->
                  check_application_args env head1 chead g_head args
                    expected_topt

and (tc_pat :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.typ ->
      FStar_Syntax_Syntax.pat ->
        (FStar_Syntax_Syntax.pat * FStar_Syntax_Syntax.bv Prims.list *
          FStar_Syntax_Syntax.term Prims.list * FStar_TypeChecker_Env.env *
          FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.term *
          FStar_TypeChecker_Common.guard_t * Prims.bool))
  =
  fun env  ->
    fun pat_t  ->
      fun p0  ->
        let fail1 msg =
          FStar_Errors.raise_error
            (FStar_Errors.Fatal_MismatchedPatternType, msg)
            p0.FStar_Syntax_Syntax.p
           in
        let expected_pat_typ env1 pos scrutinee_t =
          let rec aux norm1 t =
            let t1 = FStar_Syntax_Util.unrefine t  in
            let uu____18985 = FStar_Syntax_Util.head_and_args t1  in
            match uu____18985 with
            | (head1,args) ->
                let uu____19028 =
                  let uu____19029 = FStar_Syntax_Subst.compress head1  in
                  uu____19029.FStar_Syntax_Syntax.n  in
                (match uu____19028 with
                 | FStar_Syntax_Syntax.Tm_uinst
                     ({
                        FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar f;
                        FStar_Syntax_Syntax.pos = uu____19033;
                        FStar_Syntax_Syntax.vars = uu____19034;_},us)
                     -> unfold_once t1 f us args
                 | FStar_Syntax_Syntax.Tm_fvar f -> unfold_once t1 f [] args
                 | uu____19041 ->
                     if norm1
                     then t1
                     else
                       (let uu____19045 =
                          FStar_TypeChecker_Normalize.normalize
                            [FStar_TypeChecker_Env.HNF;
                            FStar_TypeChecker_Env.Unmeta;
                            FStar_TypeChecker_Env.Unascribe;
                            FStar_TypeChecker_Env.UnfoldUntil
                              FStar_Syntax_Syntax.delta_constant] env1 t1
                           in
                        aux true uu____19045))
          
          and unfold_once t f us args =
            let uu____19063 =
              FStar_TypeChecker_Env.is_type_constructor env1
                (f.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
               in
            if uu____19063
            then t
            else
              (let uu____19068 =
                 FStar_TypeChecker_Env.lookup_definition
                   [FStar_TypeChecker_Env.Unfold
                      FStar_Syntax_Syntax.delta_constant] env1
                   (f.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                  in
               match uu____19068 with
               | FStar_Pervasives_Native.None  -> t
               | FStar_Pervasives_Native.Some head_def_ts ->
                   let uu____19088 =
                     FStar_TypeChecker_Env.inst_tscheme_with head_def_ts us
                      in
                   (match uu____19088 with
                    | (uu____19093,head_def) ->
                        let t' =
                          FStar_Syntax_Syntax.mk_Tm_app head_def args
                            FStar_Pervasives_Native.None
                            t.FStar_Syntax_Syntax.pos
                           in
                        let t'1 =
                          FStar_TypeChecker_Normalize.normalize
                            [FStar_TypeChecker_Env.Beta;
                            FStar_TypeChecker_Env.Iota] env1 t'
                           in
                        aux false t'1))
           in
          let uu____19100 =
            FStar_TypeChecker_Normalize.normalize
              [FStar_TypeChecker_Env.Beta; FStar_TypeChecker_Env.Iota] env1
              scrutinee_t
             in
          aux false uu____19100  in
        let pat_typ_ok env1 pat_t1 scrutinee_t =
          (let uu____19119 =
             FStar_All.pipe_left (FStar_TypeChecker_Env.debug env1)
               (FStar_Options.Other "Patterns")
              in
           if uu____19119
           then
             let uu____19124 = FStar_Syntax_Print.term_to_string pat_t1  in
             let uu____19126 = FStar_Syntax_Print.term_to_string scrutinee_t
                in
             FStar_Util.print2 "$$$$$$$$$$$$pat_typ_ok? %s vs. %s\n"
               uu____19124 uu____19126
           else ());
          (let fail2 msg =
             let msg1 =
               let uu____19146 = FStar_Syntax_Print.term_to_string pat_t1  in
               let uu____19148 =
                 FStar_Syntax_Print.term_to_string scrutinee_t  in
               FStar_Util.format3
                 "Type of pattern (%s) does not match type of scrutinee (%s)%s"
                 uu____19146 uu____19148 msg
                in
             FStar_Errors.raise_error
               (FStar_Errors.Fatal_MismatchedPatternType, msg1)
               p0.FStar_Syntax_Syntax.p
              in
           let uu____19152 = FStar_Syntax_Util.head_and_args scrutinee_t  in
           match uu____19152 with
           | (head_s,args_s) ->
               let pat_t2 =
                 FStar_TypeChecker_Normalize.normalize
                   [FStar_TypeChecker_Env.Beta] env1 pat_t1
                  in
               let uu____19196 = FStar_Syntax_Util.un_uinst head_s  in
               (match uu____19196 with
                | {
                    FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar
                      uu____19197;
                    FStar_Syntax_Syntax.pos = uu____19198;
                    FStar_Syntax_Syntax.vars = uu____19199;_} ->
                    let uu____19202 = FStar_Syntax_Util.head_and_args pat_t2
                       in
                    (match uu____19202 with
                     | (head_p,args_p) ->
                         let uu____19245 =
                           FStar_TypeChecker_Rel.teq_nosmt_force env1 head_p
                             head_s
                            in
                         if uu____19245
                         then
                           let uu____19248 =
                             let uu____19249 =
                               FStar_Syntax_Util.un_uinst head_p  in
                             uu____19249.FStar_Syntax_Syntax.n  in
                           (match uu____19248 with
                            | FStar_Syntax_Syntax.Tm_fvar f ->
                                ((let uu____19254 =
                                    let uu____19256 =
                                      let uu____19258 =
                                        FStar_Syntax_Syntax.lid_of_fv f  in
                                      FStar_TypeChecker_Env.is_type_constructor
                                        env1 uu____19258
                                       in
                                    FStar_All.pipe_left Prims.op_Negation
                                      uu____19256
                                     in
                                  if uu____19254
                                  then
                                    fail2
                                      "Pattern matching a non-inductive type"
                                  else ());
                                 if
                                   (FStar_List.length args_p) <>
                                     (FStar_List.length args_s)
                                 then fail2 ""
                                 else ();
                                 (let uu____19286 =
                                    let uu____19311 =
                                      let uu____19315 =
                                        FStar_Syntax_Syntax.lid_of_fv f  in
                                      FStar_TypeChecker_Env.num_inductive_ty_params
                                        env1 uu____19315
                                       in
                                    match uu____19311 with
                                    | FStar_Pervasives_Native.None  ->
                                        (args_p, args_s)
                                    | FStar_Pervasives_Native.Some n1 ->
                                        let uu____19364 =
                                          FStar_Util.first_N n1 args_p  in
                                        (match uu____19364 with
                                         | (params_p,uu____19422) ->
                                             let uu____19463 =
                                               FStar_Util.first_N n1 args_s
                                                in
                                             (match uu____19463 with
                                              | (params_s,uu____19521) ->
                                                  (params_p, params_s)))
                                     in
                                  match uu____19286 with
                                  | (params_p,params_s) ->
                                      FStar_List.fold_left2
                                        (fun out  ->
                                           fun uu____19650  ->
                                             fun uu____19651  ->
                                               match (uu____19650,
                                                       uu____19651)
                                               with
                                               | ((p,uu____19685),(s,uu____19687))
                                                   ->
                                                   let uu____19720 =
                                                     FStar_TypeChecker_Rel.teq_nosmt
                                                       env1 p s
                                                      in
                                                   (match uu____19720 with
                                                    | FStar_Pervasives_Native.None
                                                         ->
                                                        let uu____19723 =
                                                          let uu____19725 =
                                                            FStar_Syntax_Print.term_to_string
                                                              p
                                                             in
                                                          let uu____19727 =
                                                            FStar_Syntax_Print.term_to_string
                                                              s
                                                             in
                                                          FStar_Util.format2
                                                            "; parameter %s <> parameter %s"
                                                            uu____19725
                                                            uu____19727
                                                           in
                                                        fail2 uu____19723
                                                    | FStar_Pervasives_Native.Some
                                                        g ->
                                                        let g1 =
                                                          FStar_TypeChecker_Rel.discharge_guard_no_smt
                                                            env1 g
                                                           in
                                                        FStar_TypeChecker_Env.conj_guard
                                                          g1 out))
                                        FStar_TypeChecker_Env.trivial_guard
                                        params_p params_s))
                            | uu____19732 ->
                                fail2 "Pattern matching a non-inductive type")
                         else
                           (let uu____19736 =
                              let uu____19738 =
                                FStar_Syntax_Print.term_to_string head_p  in
                              let uu____19740 =
                                FStar_Syntax_Print.term_to_string head_s  in
                              FStar_Util.format2 "; head mismatch %s vs %s"
                                uu____19738 uu____19740
                               in
                            fail2 uu____19736))
                | uu____19743 ->
                    let uu____19744 =
                      FStar_TypeChecker_Rel.teq_nosmt env1 pat_t2 scrutinee_t
                       in
                    (match uu____19744 with
                     | FStar_Pervasives_Native.None  -> fail2 ""
                     | FStar_Pervasives_Native.Some g ->
                         let g1 =
                           FStar_TypeChecker_Rel.discharge_guard_no_smt env1
                             g
                            in
                         g1)))
           in
        let type_of_simple_pat env1 e =
          let uu____19787 = FStar_Syntax_Util.head_and_args e  in
          match uu____19787 with
          | (head1,args) ->
              (match head1.FStar_Syntax_Syntax.n with
               | FStar_Syntax_Syntax.Tm_fvar f ->
                   let uu____19857 =
                     FStar_TypeChecker_Env.lookup_datacon env1
                       (f.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                      in
                   (match uu____19857 with
                    | (us,t_f) ->
                        let uu____19877 = FStar_Syntax_Util.arrow_formals t_f
                           in
                        (match uu____19877 with
                         | (formals,t) ->
                             let erasable1 =
                               FStar_TypeChecker_Env.non_informative env1 t
                                in
                             (if
                                (FStar_List.length formals) <>
                                  (FStar_List.length args)
                              then
                                fail1
                                  "Pattern is not a fully-applied data constructor"
                              else ();
                              (let rec aux uu____20014 formals1 args1 =
                                 match uu____20014 with
                                 | (subst1,args_out,bvs,guard) ->
                                     (match (formals1, args1) with
                                      | ([],[]) ->
                                          let head2 =
                                            FStar_Syntax_Syntax.mk_Tm_uinst
                                              head1 us
                                             in
                                          let pat_e =
                                            FStar_Syntax_Syntax.mk_Tm_app
                                              head2 args_out
                                              FStar_Pervasives_Native.None
                                              e.FStar_Syntax_Syntax.pos
                                             in
                                          let uu____20165 =
                                            FStar_Syntax_Subst.subst subst1 t
                                             in
                                          (pat_e, uu____20165, bvs, guard,
                                            erasable1)
                                      | ((f1,uu____20172)::formals2,(a,imp_a)::args2)
                                          ->
                                          let t_f1 =
                                            FStar_Syntax_Subst.subst subst1
                                              f1.FStar_Syntax_Syntax.sort
                                             in
                                          let uu____20230 =
                                            let uu____20251 =
                                              let uu____20252 =
                                                FStar_Syntax_Subst.compress a
                                                 in
                                              uu____20252.FStar_Syntax_Syntax.n
                                               in
                                            match uu____20251 with
                                            | FStar_Syntax_Syntax.Tm_name x
                                                ->
                                                let x1 =
                                                  let uu___2582_20277 = x  in
                                                  {
                                                    FStar_Syntax_Syntax.ppname
                                                      =
                                                      (uu___2582_20277.FStar_Syntax_Syntax.ppname);
                                                    FStar_Syntax_Syntax.index
                                                      =
                                                      (uu___2582_20277.FStar_Syntax_Syntax.index);
                                                    FStar_Syntax_Syntax.sort
                                                      = t_f1
                                                  }  in
                                                let a1 =
                                                  FStar_Syntax_Syntax.bv_to_name
                                                    x1
                                                   in
                                                let subst2 =
                                                  (FStar_Syntax_Syntax.NT
                                                     (f1, a1))
                                                  :: subst1  in
                                                ((a1, imp_a), subst2,
                                                  (FStar_List.append bvs [x1]),
                                                  FStar_TypeChecker_Env.trivial_guard)
                                            | FStar_Syntax_Syntax.Tm_uvar
                                                uu____20300 ->
                                                let env2 =
                                                  FStar_TypeChecker_Env.set_expected_typ
                                                    env1 t_f1
                                                   in
                                                let uu____20314 =
                                                  tc_tot_or_gtot_term env2 a
                                                   in
                                                (match uu____20314 with
                                                 | (a1,uu____20342,g) ->
                                                     let g1 =
                                                       FStar_TypeChecker_Rel.discharge_guard_no_smt
                                                         env2 g
                                                        in
                                                     let subst2 =
                                                       (FStar_Syntax_Syntax.NT
                                                          (f1, a1))
                                                       :: subst1  in
                                                     ((a1, imp_a), subst2,
                                                       bvs, g1))
                                            | uu____20366 ->
                                                fail1 "Not a simple pattern"
                                             in
                                          (match uu____20230 with
                                           | (a1,subst2,bvs1,g) ->
                                               let uu____20431 =
                                                 let uu____20454 =
                                                   FStar_TypeChecker_Env.conj_guard
                                                     g guard
                                                    in
                                                 (subst2,
                                                   (FStar_List.append
                                                      args_out [a1]), bvs1,
                                                   uu____20454)
                                                  in
                                               aux uu____20431 formals2 args2)
                                      | uu____20493 ->
                                          fail1 "Not a fully applued pattern")
                                  in
                               aux
                                 ([], [], [],
                                   FStar_TypeChecker_Env.trivial_guard)
                                 formals args))))
               | uu____20552 -> fail1 "Not a simple pattern")
           in
        let rec check_nested_pattern env1 p t =
          (let uu____20618 =
             FStar_All.pipe_left (FStar_TypeChecker_Env.debug env1)
               (FStar_Options.Other "Patterns")
              in
           if uu____20618
           then
             let uu____20623 = FStar_Syntax_Print.pat_to_string p  in
             let uu____20625 = FStar_Syntax_Print.term_to_string t  in
             FStar_Util.print2 "Checking pattern %s at type %s\n" uu____20623
               uu____20625
           else ());
          (let id1 =
             FStar_Syntax_Syntax.fvar FStar_Parser_Const.id_lid
               (FStar_Syntax_Syntax.Delta_constant_at_level Prims.int_one)
               FStar_Pervasives_Native.None
              in
           let mk_disc_t disc inner_t =
             let x_b =
               let uu____20650 =
                 FStar_Syntax_Syntax.gen_bv "x" FStar_Pervasives_Native.None
                   t
                  in
               FStar_All.pipe_right uu____20650 FStar_Syntax_Syntax.mk_binder
                in
             let tm =
               let uu____20661 =
                 let uu____20666 =
                   let uu____20667 =
                     let uu____20676 =
                       let uu____20677 =
                         FStar_All.pipe_right x_b FStar_Pervasives_Native.fst
                          in
                       FStar_All.pipe_right uu____20677
                         FStar_Syntax_Syntax.bv_to_name
                        in
                     FStar_All.pipe_right uu____20676
                       FStar_Syntax_Syntax.as_arg
                      in
                   [uu____20667]  in
                 FStar_Syntax_Syntax.mk_Tm_app disc uu____20666  in
               uu____20661 FStar_Pervasives_Native.None
                 FStar_Range.dummyRange
                in
             let tm1 =
               let uu____20713 =
                 let uu____20718 =
                   let uu____20719 =
                     FStar_All.pipe_right tm FStar_Syntax_Syntax.as_arg  in
                   [uu____20719]  in
                 FStar_Syntax_Syntax.mk_Tm_app inner_t uu____20718  in
               uu____20713 FStar_Pervasives_Native.None
                 FStar_Range.dummyRange
                in
             FStar_Syntax_Util.abs [x_b] tm1 FStar_Pervasives_Native.None  in
           match p.FStar_Syntax_Syntax.v with
           | FStar_Syntax_Syntax.Pat_dot_term uu____20781 ->
               let uu____20788 =
                 let uu____20790 = FStar_Syntax_Print.pat_to_string p  in
                 FStar_Util.format1
                   "Impossible: Expected an undecorated pattern, got %s"
                   uu____20790
                  in
               failwith uu____20788
           | FStar_Syntax_Syntax.Pat_wild x ->
               let x1 =
                 let uu___2621_20812 = x  in
                 {
                   FStar_Syntax_Syntax.ppname =
                     (uu___2621_20812.FStar_Syntax_Syntax.ppname);
                   FStar_Syntax_Syntax.index =
                     (uu___2621_20812.FStar_Syntax_Syntax.index);
                   FStar_Syntax_Syntax.sort = t
                 }  in
               let uu____20813 = FStar_Syntax_Syntax.bv_to_name x1  in
               ([x1], [id1], uu____20813,
                 (let uu___2624_20820 = p  in
                  {
                    FStar_Syntax_Syntax.v = (FStar_Syntax_Syntax.Pat_wild x1);
                    FStar_Syntax_Syntax.p =
                      (uu___2624_20820.FStar_Syntax_Syntax.p)
                  }), FStar_TypeChecker_Env.trivial_guard, false)
           | FStar_Syntax_Syntax.Pat_var x ->
               let x1 =
                 let uu___2628_20824 = x  in
                 {
                   FStar_Syntax_Syntax.ppname =
                     (uu___2628_20824.FStar_Syntax_Syntax.ppname);
                   FStar_Syntax_Syntax.index =
                     (uu___2628_20824.FStar_Syntax_Syntax.index);
                   FStar_Syntax_Syntax.sort = t
                 }  in
               let uu____20825 = FStar_Syntax_Syntax.bv_to_name x1  in
               ([x1], [id1], uu____20825,
                 (let uu___2631_20832 = p  in
                  {
                    FStar_Syntax_Syntax.v = (FStar_Syntax_Syntax.Pat_var x1);
                    FStar_Syntax_Syntax.p =
                      (uu___2631_20832.FStar_Syntax_Syntax.p)
                  }), FStar_TypeChecker_Env.trivial_guard, false)
           | FStar_Syntax_Syntax.Pat_constant uu____20834 ->
               let uu____20835 =
                 FStar_TypeChecker_PatternUtils.pat_as_exp false env1 p  in
               (match uu____20835 with
                | (uu____20864,e_c,uu____20866,uu____20867) ->
                    let uu____20872 = tc_tot_or_gtot_term env1 e_c  in
                    (match uu____20872 with
                     | (e_c1,lc,g) ->
                         (FStar_TypeChecker_Rel.force_trivial_guard env1 g;
                          (let expected_t =
                             expected_pat_typ env1 p0.FStar_Syntax_Syntax.p t
                              in
                           (let uu____20902 =
                              let uu____20904 =
                                FStar_TypeChecker_Rel.teq_nosmt_force env1
                                  lc.FStar_TypeChecker_Common.res_typ
                                  expected_t
                                 in
                              Prims.op_Negation uu____20904  in
                            if uu____20902
                            then
                              let uu____20907 =
                                let uu____20909 =
                                  FStar_Syntax_Print.term_to_string
                                    lc.FStar_TypeChecker_Common.res_typ
                                   in
                                let uu____20911 =
                                  FStar_Syntax_Print.term_to_string
                                    expected_t
                                   in
                                FStar_Util.format2
                                  "Type of pattern (%s) does not match type of scrutinee (%s)"
                                  uu____20909 uu____20911
                                 in
                              fail1 uu____20907
                            else ());
                           ([], [], e_c1, p,
                             FStar_TypeChecker_Env.trivial_guard, false)))))
           | FStar_Syntax_Syntax.Pat_cons (fv,sub_pats) ->
               let simple_pat =
                 let simple_sub_pats =
                   FStar_List.map
                     (fun uu____20973  ->
                        match uu____20973 with
                        | (p1,b) ->
                            (match p1.FStar_Syntax_Syntax.v with
                             | FStar_Syntax_Syntax.Pat_dot_term uu____21003
                                 -> (p1, b)
                             | uu____21013 ->
                                 let uu____21014 =
                                   let uu____21017 =
                                     let uu____21018 =
                                       FStar_Syntax_Syntax.new_bv
                                         (FStar_Pervasives_Native.Some
                                            (p1.FStar_Syntax_Syntax.p))
                                         FStar_Syntax_Syntax.tun
                                        in
                                     FStar_Syntax_Syntax.Pat_var uu____21018
                                      in
                                   FStar_Syntax_Syntax.withinfo uu____21017
                                     p1.FStar_Syntax_Syntax.p
                                    in
                                 (uu____21014, b))) sub_pats
                    in
                 let uu___2659_21022 = p  in
                 {
                   FStar_Syntax_Syntax.v =
                     (FStar_Syntax_Syntax.Pat_cons (fv, simple_sub_pats));
                   FStar_Syntax_Syntax.p =
                     (uu___2659_21022.FStar_Syntax_Syntax.p)
                 }  in
               let sub_pats1 =
                 FStar_All.pipe_right sub_pats
                   (FStar_List.filter
                      (fun uu____21067  ->
                         match uu____21067 with
                         | (x,uu____21077) ->
                             (match x.FStar_Syntax_Syntax.v with
                              | FStar_Syntax_Syntax.Pat_dot_term uu____21085
                                  -> false
                              | uu____21093 -> true)))
                  in
               let uu____21095 =
                 FStar_TypeChecker_PatternUtils.pat_as_exp false env1
                   simple_pat
                  in
               (match uu____21095 with
                | (simple_bvs,simple_pat_e,g0,simple_pat_elab) ->
                    (if
                       (FStar_List.length simple_bvs) <>
                         (FStar_List.length sub_pats1)
                     then
                       (let uu____21139 =
                          let uu____21141 =
                            FStar_Range.string_of_range
                              p.FStar_Syntax_Syntax.p
                             in
                          let uu____21143 =
                            FStar_Syntax_Print.pat_to_string simple_pat  in
                          let uu____21145 =
                            FStar_Util.string_of_int
                              (FStar_List.length sub_pats1)
                             in
                          let uu____21152 =
                            FStar_Util.string_of_int
                              (FStar_List.length simple_bvs)
                             in
                          FStar_Util.format4
                            "(%s) Impossible: pattern bvar mismatch: %s; expected %s sub pats; got %s"
                            uu____21141 uu____21143 uu____21145 uu____21152
                           in
                        failwith uu____21139)
                     else ();
                     (let uu____21157 =
                        let uu____21169 =
                          type_of_simple_pat env1 simple_pat_e  in
                        match uu____21169 with
                        | (simple_pat_e1,simple_pat_t,simple_bvs1,guard,erasable1)
                            ->
                            let g' =
                              let uu____21206 =
                                expected_pat_typ env1
                                  p0.FStar_Syntax_Syntax.p t
                                 in
                              pat_typ_ok env1 simple_pat_t uu____21206  in
                            let guard1 =
                              FStar_TypeChecker_Env.conj_guard guard g'  in
                            ((let uu____21209 =
                                FStar_All.pipe_left
                                  (FStar_TypeChecker_Env.debug env1)
                                  (FStar_Options.Other "Patterns")
                                 in
                              if uu____21209
                              then
                                let uu____21214 =
                                  FStar_Syntax_Print.term_to_string
                                    simple_pat_e1
                                   in
                                let uu____21216 =
                                  FStar_Syntax_Print.term_to_string
                                    simple_pat_t
                                   in
                                let uu____21218 =
                                  let uu____21220 =
                                    FStar_List.map
                                      (fun x  ->
                                         let uu____21228 =
                                           let uu____21230 =
                                             FStar_Syntax_Print.bv_to_string
                                               x
                                              in
                                           let uu____21232 =
                                             let uu____21234 =
                                               let uu____21236 =
                                                 FStar_Syntax_Print.term_to_string
                                                   x.FStar_Syntax_Syntax.sort
                                                  in
                                               Prims.op_Hat uu____21236 ")"
                                                in
                                             Prims.op_Hat " : " uu____21234
                                              in
                                           Prims.op_Hat uu____21230
                                             uu____21232
                                            in
                                         Prims.op_Hat "(" uu____21228)
                                      simple_bvs1
                                     in
                                  FStar_All.pipe_right uu____21220
                                    (FStar_String.concat " ")
                                   in
                                FStar_Util.print3
                                  "$$$$$$$$$$$$Checked simple pattern %s at type %s with bvs=%s\n"
                                  uu____21214 uu____21216 uu____21218
                              else ());
                             (simple_pat_e1, simple_bvs1, guard1, erasable1))
                         in
                      match uu____21157 with
                      | (simple_pat_e1,simple_bvs1,g1,erasable1) ->
                          let uu____21279 =
                            let uu____21311 =
                              let uu____21343 =
                                FStar_TypeChecker_Env.conj_guard g0 g1  in
                              (env1, [], [], [], [], uu____21343, erasable1,
                                Prims.int_zero)
                               in
                            FStar_List.fold_left2
                              (fun uu____21425  ->
                                 fun uu____21426  ->
                                   fun x  ->
                                     match (uu____21425, uu____21426) with
                                     | ((env2,bvs,tms,pats,subst1,g,erasable2,i),
                                        (p1,b)) ->
                                         let expected_t =
                                           FStar_Syntax_Subst.subst subst1
                                             x.FStar_Syntax_Syntax.sort
                                            in
                                         let uu____21610 =
                                           check_nested_pattern env2 p1
                                             expected_t
                                            in
                                         (match uu____21610 with
                                          | (bvs_p,tms_p,e_p,p2,g',erasable_p)
                                              ->
                                              let env3 =
                                                FStar_TypeChecker_Env.push_bvs
                                                  env2 bvs_p
                                                 in
                                              let tms_p1 =
                                                let disc_tm =
                                                  let uu____21680 =
                                                    FStar_Syntax_Syntax.lid_of_fv
                                                      fv
                                                     in
                                                  FStar_TypeChecker_Util.get_field_projector_name
                                                    env3 uu____21680 i
                                                   in
                                                let uu____21681 =
                                                  let uu____21690 =
                                                    let uu____21695 =
                                                      FStar_Syntax_Syntax.fvar
                                                        disc_tm
                                                        (FStar_Syntax_Syntax.Delta_constant_at_level
                                                           Prims.int_one)
                                                        FStar_Pervasives_Native.None
                                                       in
                                                    mk_disc_t uu____21695  in
                                                  FStar_List.map uu____21690
                                                   in
                                                FStar_All.pipe_right tms_p
                                                  uu____21681
                                                 in
                                              let uu____21701 =
                                                FStar_TypeChecker_Env.conj_guard
                                                  g g'
                                                 in
                                              (env3,
                                                (FStar_List.append bvs bvs_p),
                                                (FStar_List.append tms tms_p1),
                                                (FStar_List.append pats
                                                   [(p2, b)]),
                                                ((FStar_Syntax_Syntax.NT
                                                    (x, e_p)) :: subst1),
                                                uu____21701,
                                                (erasable2 || erasable_p),
                                                (i + Prims.int_one))))
                              uu____21311 sub_pats1 simple_bvs1
                             in
                          (match uu____21279 with
                           | (_env,bvs,tms,checked_sub_pats,subst1,g,erasable2,uu____21760)
                               ->
                               let pat_e =
                                 FStar_Syntax_Subst.subst subst1
                                   simple_pat_e1
                                  in
                               let reconstruct_nested_pat pat =
                                 let rec aux simple_pats bvs1 sub_pats2 =
                                   match simple_pats with
                                   | [] -> []
                                   | (hd1,b)::simple_pats1 ->
                                       (match hd1.FStar_Syntax_Syntax.v with
                                        | FStar_Syntax_Syntax.Pat_dot_term
                                            (x,e) ->
                                            let e1 =
                                              FStar_Syntax_Subst.subst subst1
                                                e
                                               in
                                            let hd2 =
                                              let uu___2743_21936 = hd1  in
                                              {
                                                FStar_Syntax_Syntax.v =
                                                  (FStar_Syntax_Syntax.Pat_dot_term
                                                     (x, e1));
                                                FStar_Syntax_Syntax.p =
                                                  (uu___2743_21936.FStar_Syntax_Syntax.p)
                                              }  in
                                            let uu____21941 =
                                              aux simple_pats1 bvs1 sub_pats2
                                               in
                                            (hd2, b) :: uu____21941
                                        | FStar_Syntax_Syntax.Pat_var x ->
                                            (match (bvs1, sub_pats2) with
                                             | (x'::bvs2,(hd2,uu____21985)::sub_pats3)
                                                 when
                                                 FStar_Syntax_Syntax.bv_eq x
                                                   x'
                                                 ->
                                                 let uu____22022 =
                                                   aux simple_pats1 bvs2
                                                     sub_pats3
                                                    in
                                                 (hd2, b) :: uu____22022
                                             | uu____22042 ->
                                                 failwith
                                                   "Impossible: simple pat variable mismatch")
                                        | uu____22068 ->
                                            failwith
                                              "Impossible: expected a simple pattern")
                                    in
                                 match pat.FStar_Syntax_Syntax.v with
                                 | FStar_Syntax_Syntax.Pat_cons
                                     (fv1,simple_pats) ->
                                     let nested_pats =
                                       aux simple_pats simple_bvs1
                                         checked_sub_pats
                                        in
                                     let uu___2764_22111 = pat  in
                                     {
                                       FStar_Syntax_Syntax.v =
                                         (FStar_Syntax_Syntax.Pat_cons
                                            (fv1, nested_pats));
                                       FStar_Syntax_Syntax.p =
                                         (uu___2764_22111.FStar_Syntax_Syntax.p)
                                     }
                                 | uu____22123 -> failwith "Impossible"  in
                               let uu____22127 =
                                 reconstruct_nested_pat simple_pat_elab  in
                               (bvs, tms, pat_e, uu____22127, g, erasable2))))))
           in
        (let uu____22134 =
           FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
             (FStar_Options.Other "Patterns")
            in
         if uu____22134
         then
           let uu____22139 = FStar_Syntax_Print.pat_to_string p0  in
           FStar_Util.print1 "Checking pattern: %s\n" uu____22139
         else ());
        (let uu____22144 =
           let uu____22162 =
             let uu___2769_22163 =
               let uu____22164 = FStar_TypeChecker_Env.clear_expected_typ env
                  in
               FStar_All.pipe_right uu____22164 FStar_Pervasives_Native.fst
                in
             {
               FStar_TypeChecker_Env.solver =
                 (uu___2769_22163.FStar_TypeChecker_Env.solver);
               FStar_TypeChecker_Env.range =
                 (uu___2769_22163.FStar_TypeChecker_Env.range);
               FStar_TypeChecker_Env.curmodule =
                 (uu___2769_22163.FStar_TypeChecker_Env.curmodule);
               FStar_TypeChecker_Env.gamma =
                 (uu___2769_22163.FStar_TypeChecker_Env.gamma);
               FStar_TypeChecker_Env.gamma_sig =
                 (uu___2769_22163.FStar_TypeChecker_Env.gamma_sig);
               FStar_TypeChecker_Env.gamma_cache =
                 (uu___2769_22163.FStar_TypeChecker_Env.gamma_cache);
               FStar_TypeChecker_Env.modules =
                 (uu___2769_22163.FStar_TypeChecker_Env.modules);
               FStar_TypeChecker_Env.expected_typ =
                 (uu___2769_22163.FStar_TypeChecker_Env.expected_typ);
               FStar_TypeChecker_Env.sigtab =
                 (uu___2769_22163.FStar_TypeChecker_Env.sigtab);
               FStar_TypeChecker_Env.attrtab =
                 (uu___2769_22163.FStar_TypeChecker_Env.attrtab);
               FStar_TypeChecker_Env.instantiate_imp =
                 (uu___2769_22163.FStar_TypeChecker_Env.instantiate_imp);
               FStar_TypeChecker_Env.effects =
                 (uu___2769_22163.FStar_TypeChecker_Env.effects);
               FStar_TypeChecker_Env.generalize =
                 (uu___2769_22163.FStar_TypeChecker_Env.generalize);
               FStar_TypeChecker_Env.letrecs =
                 (uu___2769_22163.FStar_TypeChecker_Env.letrecs);
               FStar_TypeChecker_Env.top_level =
                 (uu___2769_22163.FStar_TypeChecker_Env.top_level);
               FStar_TypeChecker_Env.check_uvars =
                 (uu___2769_22163.FStar_TypeChecker_Env.check_uvars);
               FStar_TypeChecker_Env.use_eq = true;
               FStar_TypeChecker_Env.is_iface =
                 (uu___2769_22163.FStar_TypeChecker_Env.is_iface);
               FStar_TypeChecker_Env.admit =
                 (uu___2769_22163.FStar_TypeChecker_Env.admit);
               FStar_TypeChecker_Env.lax =
                 (uu___2769_22163.FStar_TypeChecker_Env.lax);
               FStar_TypeChecker_Env.lax_universes =
                 (uu___2769_22163.FStar_TypeChecker_Env.lax_universes);
               FStar_TypeChecker_Env.phase1 =
                 (uu___2769_22163.FStar_TypeChecker_Env.phase1);
               FStar_TypeChecker_Env.failhard =
                 (uu___2769_22163.FStar_TypeChecker_Env.failhard);
               FStar_TypeChecker_Env.nosynth =
                 (uu___2769_22163.FStar_TypeChecker_Env.nosynth);
               FStar_TypeChecker_Env.uvar_subtyping =
                 (uu___2769_22163.FStar_TypeChecker_Env.uvar_subtyping);
               FStar_TypeChecker_Env.tc_term =
                 (uu___2769_22163.FStar_TypeChecker_Env.tc_term);
               FStar_TypeChecker_Env.type_of =
                 (uu___2769_22163.FStar_TypeChecker_Env.type_of);
               FStar_TypeChecker_Env.universe_of =
                 (uu___2769_22163.FStar_TypeChecker_Env.universe_of);
               FStar_TypeChecker_Env.check_type_of =
                 (uu___2769_22163.FStar_TypeChecker_Env.check_type_of);
               FStar_TypeChecker_Env.use_bv_sorts =
                 (uu___2769_22163.FStar_TypeChecker_Env.use_bv_sorts);
               FStar_TypeChecker_Env.qtbl_name_and_index =
                 (uu___2769_22163.FStar_TypeChecker_Env.qtbl_name_and_index);
               FStar_TypeChecker_Env.normalized_eff_names =
                 (uu___2769_22163.FStar_TypeChecker_Env.normalized_eff_names);
               FStar_TypeChecker_Env.fv_delta_depths =
                 (uu___2769_22163.FStar_TypeChecker_Env.fv_delta_depths);
               FStar_TypeChecker_Env.proof_ns =
                 (uu___2769_22163.FStar_TypeChecker_Env.proof_ns);
               FStar_TypeChecker_Env.synth_hook =
                 (uu___2769_22163.FStar_TypeChecker_Env.synth_hook);
               FStar_TypeChecker_Env.splice =
                 (uu___2769_22163.FStar_TypeChecker_Env.splice);
               FStar_TypeChecker_Env.mpreprocess =
                 (uu___2769_22163.FStar_TypeChecker_Env.mpreprocess);
               FStar_TypeChecker_Env.postprocess =
                 (uu___2769_22163.FStar_TypeChecker_Env.postprocess);
               FStar_TypeChecker_Env.is_native_tactic =
                 (uu___2769_22163.FStar_TypeChecker_Env.is_native_tactic);
               FStar_TypeChecker_Env.identifier_info =
                 (uu___2769_22163.FStar_TypeChecker_Env.identifier_info);
               FStar_TypeChecker_Env.tc_hooks =
                 (uu___2769_22163.FStar_TypeChecker_Env.tc_hooks);
               FStar_TypeChecker_Env.dsenv =
                 (uu___2769_22163.FStar_TypeChecker_Env.dsenv);
               FStar_TypeChecker_Env.nbe =
                 (uu___2769_22163.FStar_TypeChecker_Env.nbe);
               FStar_TypeChecker_Env.strict_args_tab =
                 (uu___2769_22163.FStar_TypeChecker_Env.strict_args_tab);
               FStar_TypeChecker_Env.erasable_types_tab =
                 (uu___2769_22163.FStar_TypeChecker_Env.erasable_types_tab)
             }  in
           let uu____22180 =
             FStar_TypeChecker_PatternUtils.elaborate_pat env p0  in
           check_nested_pattern uu____22162 uu____22180 pat_t  in
         match uu____22144 with
         | (bvs,tms,pat_e,pat,g,erasable1) ->
             ((let uu____22219 =
                 FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                   (FStar_Options.Other "Patterns")
                  in
               if uu____22219
               then
                 let uu____22224 = FStar_Syntax_Print.pat_to_string pat  in
                 let uu____22226 = FStar_Syntax_Print.term_to_string pat_e
                    in
                 FStar_Util.print2
                   "Done checking pattern %s as expression %s\n" uu____22224
                   uu____22226
               else ());
              (let uu____22231 = FStar_TypeChecker_Env.push_bvs env bvs  in
               let uu____22232 =
                 FStar_TypeChecker_Normalize.normalize
                   [FStar_TypeChecker_Env.Beta] env pat_e
                  in
               (pat, bvs, tms, uu____22231, pat_e, uu____22232, g, erasable1))))

and (tc_eqn :
  FStar_Syntax_Syntax.bv ->
    FStar_TypeChecker_Env.env ->
      FStar_Syntax_Syntax.branch ->
        ((FStar_Syntax_Syntax.pat * FStar_Syntax_Syntax.term
          FStar_Pervasives_Native.option * FStar_Syntax_Syntax.term) *
          FStar_Syntax_Syntax.term * FStar_Ident.lident *
          FStar_Syntax_Syntax.cflag Prims.list *
          (Prims.bool -> FStar_TypeChecker_Common.lcomp) *
          FStar_TypeChecker_Common.guard_t * Prims.bool))
  =
  fun scrutinee  ->
    fun env  ->
      fun branch1  ->
        let uu____22270 = FStar_Syntax_Subst.open_branch branch1  in
        match uu____22270 with
        | (pattern,when_clause,branch_exp) ->
            let uu____22319 = branch1  in
            (match uu____22319 with
             | (cpat,uu____22350,cbr) ->
                 let pat_t = scrutinee.FStar_Syntax_Syntax.sort  in
                 let scrutinee_tm = FStar_Syntax_Syntax.bv_to_name scrutinee
                    in
                 let uu____22372 =
                   let uu____22379 =
                     FStar_TypeChecker_Env.push_bv env scrutinee  in
                   FStar_All.pipe_right uu____22379
                     FStar_TypeChecker_Env.clear_expected_typ
                    in
                 (match uu____22372 with
                  | (scrutinee_env,uu____22416) ->
                      let uu____22421 = tc_pat env pat_t pattern  in
                      (match uu____22421 with
                       | (pattern1,pat_bvs1,pat_bv_tms,pat_env,pat_exp,norm_pat_exp,guard_pat,erasable1)
                           ->
                           ((let uu____22491 =
                               FStar_All.pipe_left
                                 (FStar_TypeChecker_Env.debug env)
                                 FStar_Options.Extreme
                                in
                             if uu____22491
                             then
                               let uu____22495 =
                                 FStar_Syntax_Print.pat_to_string pattern1
                                  in
                               let uu____22497 =
                                 FStar_Syntax_Print.bvs_to_string ";"
                                   pat_bvs1
                                  in
                               let uu____22500 =
                                 FStar_List.fold_left
                                   (fun s  ->
                                      fun t  ->
                                        let uu____22509 =
                                          let uu____22511 =
                                            FStar_Syntax_Print.term_to_string
                                              t
                                             in
                                          Prims.op_Hat ";" uu____22511  in
                                        Prims.op_Hat s uu____22509) ""
                                   pat_bv_tms
                                  in
                               FStar_Util.print3
                                 "tc_eqn: typechecked pattern %s with bvs %s and pat_bv_tms %s"
                                 uu____22495 uu____22497 uu____22500
                             else ());
                            (let uu____22518 =
                               match when_clause with
                               | FStar_Pervasives_Native.None  ->
                                   (FStar_Pervasives_Native.None,
                                     FStar_TypeChecker_Env.trivial_guard)
                               | FStar_Pervasives_Native.Some e ->
                                   let uu____22548 =
                                     FStar_TypeChecker_Env.should_verify env
                                      in
                                   if uu____22548
                                   then
                                     FStar_Errors.raise_error
                                       (FStar_Errors.Fatal_WhenClauseNotSupported,
                                         "When clauses are not yet supported in --verify mode; they will be some day")
                                       e.FStar_Syntax_Syntax.pos
                                   else
                                     (let uu____22571 =
                                        let uu____22578 =
                                          FStar_TypeChecker_Env.set_expected_typ
                                            pat_env FStar_Syntax_Util.t_bool
                                           in
                                        tc_term uu____22578 e  in
                                      match uu____22571 with
                                      | (e1,c,g) ->
                                          ((FStar_Pervasives_Native.Some e1),
                                            g))
                                in
                             match uu____22518 with
                             | (when_clause1,g_when) ->
                                 let uu____22635 = tc_term pat_env branch_exp
                                    in
                                 (match uu____22635 with
                                  | (branch_exp1,c,g_branch) ->
                                      (FStar_TypeChecker_Env.def_check_guard_wf
                                         cbr.FStar_Syntax_Syntax.pos
                                         "tc_eqn.1" pat_env g_branch;
                                       (let when_condition =
                                          match when_clause1 with
                                          | FStar_Pervasives_Native.None  ->
                                              FStar_Pervasives_Native.None
                                          | FStar_Pervasives_Native.Some w ->
                                              let uu____22694 =
                                                FStar_Syntax_Util.mk_eq2
                                                  FStar_Syntax_Syntax.U_zero
                                                  FStar_Syntax_Util.t_bool w
                                                  FStar_Syntax_Util.exp_true_bool
                                                 in
                                              FStar_All.pipe_left
                                                (fun _22705  ->
                                                   FStar_Pervasives_Native.Some
                                                     _22705) uu____22694
                                           in
                                        let branch_guard =
                                          let uu____22709 =
                                            let uu____22711 =
                                              FStar_TypeChecker_Env.should_verify
                                                env
                                               in
                                            Prims.op_Negation uu____22711  in
                                          if uu____22709
                                          then FStar_Syntax_Util.t_true
                                          else
                                            (let rec build_branch_guard
                                               scrutinee_tm1 pattern2
                                               pat_exp1 =
                                               let discriminate scrutinee_tm2
                                                 f =
                                                 let uu____22767 =
                                                   let uu____22775 =
                                                     FStar_TypeChecker_Env.typ_of_datacon
                                                       env
                                                       f.FStar_Syntax_Syntax.v
                                                      in
                                                   FStar_TypeChecker_Env.datacons_of_typ
                                                     env uu____22775
                                                    in
                                                 match uu____22767 with
                                                 | (is_induc,datacons) ->
                                                     if
                                                       (Prims.op_Negation
                                                          is_induc)
                                                         ||
                                                         ((FStar_List.length
                                                             datacons)
                                                            > Prims.int_one)
                                                     then
                                                       let discriminator =
                                                         FStar_Syntax_Util.mk_discriminator
                                                           f.FStar_Syntax_Syntax.v
                                                          in
                                                       let uu____22791 =
                                                         FStar_TypeChecker_Env.try_lookup_lid
                                                           env discriminator
                                                          in
                                                       (match uu____22791
                                                        with
                                                        | FStar_Pervasives_Native.None
                                                             -> []
                                                        | uu____22812 ->
                                                            let disc =
                                                              FStar_Syntax_Syntax.fvar
                                                                discriminator
                                                                (FStar_Syntax_Syntax.Delta_equational_at_level
                                                                   Prims.int_one)
                                                                FStar_Pervasives_Native.None
                                                               in
                                                            let disc1 =
                                                              let uu____22828
                                                                =
                                                                let uu____22833
                                                                  =
                                                                  let uu____22834
                                                                    =
                                                                    FStar_Syntax_Syntax.as_arg
                                                                    scrutinee_tm2
                                                                     in
                                                                  [uu____22834]
                                                                   in
                                                                FStar_Syntax_Syntax.mk_Tm_app
                                                                  disc
                                                                  uu____22833
                                                                 in
                                                              uu____22828
                                                                FStar_Pervasives_Native.None
                                                                scrutinee_tm2.FStar_Syntax_Syntax.pos
                                                               in
                                                            let uu____22859 =
                                                              FStar_Syntax_Util.mk_eq2
                                                                FStar_Syntax_Syntax.U_zero
                                                                FStar_Syntax_Util.t_bool
                                                                disc1
                                                                FStar_Syntax_Util.exp_true_bool
                                                               in
                                                            [uu____22859])
                                                     else []
                                                  in
                                               let fail1 uu____22867 =
                                                 let uu____22868 =
                                                   let uu____22870 =
                                                     FStar_Range.string_of_range
                                                       pat_exp1.FStar_Syntax_Syntax.pos
                                                      in
                                                   let uu____22872 =
                                                     FStar_Syntax_Print.term_to_string
                                                       pat_exp1
                                                      in
                                                   let uu____22874 =
                                                     FStar_Syntax_Print.tag_of_term
                                                       pat_exp1
                                                      in
                                                   FStar_Util.format3
                                                     "tc_eqn: Impossible (%s) %s (%s)"
                                                     uu____22870 uu____22872
                                                     uu____22874
                                                    in
                                                 failwith uu____22868  in
                                               let rec head_constructor t =
                                                 match t.FStar_Syntax_Syntax.n
                                                 with
                                                 | FStar_Syntax_Syntax.Tm_fvar
                                                     fv ->
                                                     fv.FStar_Syntax_Syntax.fv_name
                                                 | FStar_Syntax_Syntax.Tm_uinst
                                                     (t1,uu____22889) ->
                                                     head_constructor t1
                                                 | uu____22894 -> fail1 ()
                                                  in
                                               let force_scrutinee
                                                 uu____22900 =
                                                 match scrutinee_tm1 with
                                                 | FStar_Pervasives_Native.None
                                                      ->
                                                     let uu____22901 =
                                                       let uu____22903 =
                                                         FStar_Range.string_of_range
                                                           pattern2.FStar_Syntax_Syntax.p
                                                          in
                                                       let uu____22905 =
                                                         FStar_Syntax_Print.pat_to_string
                                                           pattern2
                                                          in
                                                       FStar_Util.format2
                                                         "Impossible (%s): scrutinee of match is not defined %s"
                                                         uu____22903
                                                         uu____22905
                                                        in
                                                     failwith uu____22901
                                                 | FStar_Pervasives_Native.Some
                                                     t -> t
                                                  in
                                               let pat_exp2 =
                                                 let uu____22912 =
                                                   FStar_Syntax_Subst.compress
                                                     pat_exp1
                                                    in
                                                 FStar_All.pipe_right
                                                   uu____22912
                                                   FStar_Syntax_Util.unmeta
                                                  in
                                               match ((pattern2.FStar_Syntax_Syntax.v),
                                                       (pat_exp2.FStar_Syntax_Syntax.n))
                                               with
                                               | (uu____22917,FStar_Syntax_Syntax.Tm_name
                                                  uu____22918) -> []
                                               | (uu____22919,FStar_Syntax_Syntax.Tm_constant
                                                  (FStar_Const.Const_unit ))
                                                   -> []
                                               | (FStar_Syntax_Syntax.Pat_constant
                                                  _c,FStar_Syntax_Syntax.Tm_constant
                                                  c1) ->
                                                   let uu____22922 =
                                                     let uu____22923 =
                                                       tc_constant env
                                                         pat_exp2.FStar_Syntax_Syntax.pos
                                                         c1
                                                        in
                                                     let uu____22924 =
                                                       force_scrutinee ()  in
                                                     FStar_Syntax_Util.mk_eq2
                                                       FStar_Syntax_Syntax.U_zero
                                                       uu____22923
                                                       uu____22924 pat_exp2
                                                      in
                                                   [uu____22922]
                                               | (FStar_Syntax_Syntax.Pat_constant
                                                  (FStar_Const.Const_int
                                                  (uu____22925,FStar_Pervasives_Native.Some
                                                   uu____22926)),uu____22927)
                                                   ->
                                                   let uu____22944 =
                                                     let uu____22951 =
                                                       FStar_TypeChecker_Env.clear_expected_typ
                                                         env
                                                        in
                                                     match uu____22951 with
                                                     | (env1,uu____22965) ->
                                                         env1.FStar_TypeChecker_Env.type_of
                                                           env1 pat_exp2
                                                      in
                                                   (match uu____22944 with
                                                    | (uu____22972,t,uu____22974)
                                                        ->
                                                        let uu____22975 =
                                                          let uu____22976 =
                                                            force_scrutinee
                                                              ()
                                                             in
                                                          FStar_Syntax_Util.mk_eq2
                                                            FStar_Syntax_Syntax.U_zero
                                                            t uu____22976
                                                            pat_exp2
                                                           in
                                                        [uu____22975])
                                               | (FStar_Syntax_Syntax.Pat_cons
                                                  (uu____22977,[]),FStar_Syntax_Syntax.Tm_uinst
                                                  uu____22978) ->
                                                   let f =
                                                     head_constructor
                                                       pat_exp2
                                                      in
                                                   let uu____23002 =
                                                     let uu____23004 =
                                                       FStar_TypeChecker_Env.is_datacon
                                                         env
                                                         f.FStar_Syntax_Syntax.v
                                                        in
                                                     Prims.op_Negation
                                                       uu____23004
                                                      in
                                                   if uu____23002
                                                   then
                                                     failwith
                                                       "Impossible: nullary patterns must be data constructors"
                                                   else
                                                     (let uu____23014 =
                                                        force_scrutinee ()
                                                         in
                                                      let uu____23017 =
                                                        head_constructor
                                                          pat_exp2
                                                         in
                                                      discriminate
                                                        uu____23014
                                                        uu____23017)
                                               | (FStar_Syntax_Syntax.Pat_cons
                                                  (uu____23020,[]),FStar_Syntax_Syntax.Tm_fvar
                                                  uu____23021) ->
                                                   let f =
                                                     head_constructor
                                                       pat_exp2
                                                      in
                                                   let uu____23039 =
                                                     let uu____23041 =
                                                       FStar_TypeChecker_Env.is_datacon
                                                         env
                                                         f.FStar_Syntax_Syntax.v
                                                        in
                                                     Prims.op_Negation
                                                       uu____23041
                                                      in
                                                   if uu____23039
                                                   then
                                                     failwith
                                                       "Impossible: nullary patterns must be data constructors"
                                                   else
                                                     (let uu____23051 =
                                                        force_scrutinee ()
                                                         in
                                                      let uu____23054 =
                                                        head_constructor
                                                          pat_exp2
                                                         in
                                                      discriminate
                                                        uu____23051
                                                        uu____23054)
                                               | (FStar_Syntax_Syntax.Pat_cons
                                                  (uu____23057,pat_args),FStar_Syntax_Syntax.Tm_app
                                                  (head1,args)) ->
                                                   let f =
                                                     head_constructor head1
                                                      in
                                                   let uu____23104 =
                                                     (let uu____23108 =
                                                        FStar_TypeChecker_Env.is_datacon
                                                          env
                                                          f.FStar_Syntax_Syntax.v
                                                         in
                                                      Prims.op_Negation
                                                        uu____23108)
                                                       ||
                                                       ((FStar_List.length
                                                           pat_args)
                                                          <>
                                                          (FStar_List.length
                                                             args))
                                                      in
                                                   if uu____23104
                                                   then
                                                     failwith
                                                       "Impossible: application patterns must be fully-applied data constructors"
                                                   else
                                                     (let sub_term_guards =
                                                        let uu____23136 =
                                                          let uu____23141 =
                                                            FStar_List.zip
                                                              pat_args args
                                                             in
                                                          FStar_All.pipe_right
                                                            uu____23141
                                                            (FStar_List.mapi
                                                               (fun i  ->
                                                                  fun
                                                                    uu____23227
                                                                     ->
                                                                    match uu____23227
                                                                    with
                                                                    | 
                                                                    ((pi,uu____23249),
                                                                    (ei,uu____23251))
                                                                    ->
                                                                    let projector
                                                                    =
                                                                    FStar_TypeChecker_Env.lookup_projector
                                                                    env
                                                                    f.FStar_Syntax_Syntax.v
                                                                    i  in
                                                                    let scrutinee_tm2
                                                                    =
                                                                    let uu____23279
                                                                    =
                                                                    FStar_TypeChecker_Env.try_lookup_lid
                                                                    env
                                                                    projector
                                                                     in
                                                                    match uu____23279
                                                                    with
                                                                    | 
                                                                    FStar_Pervasives_Native.None
                                                                     ->
                                                                    FStar_Pervasives_Native.None
                                                                    | 
                                                                    uu____23300
                                                                    ->
                                                                    let proj
                                                                    =
                                                                    let uu____23312
                                                                    =
                                                                    FStar_Ident.set_lid_range
                                                                    projector
                                                                    f.FStar_Syntax_Syntax.p
                                                                     in
                                                                    FStar_Syntax_Syntax.fvar
                                                                    uu____23312
                                                                    (FStar_Syntax_Syntax.Delta_equational_at_level
                                                                    Prims.int_one)
                                                                    FStar_Pervasives_Native.None
                                                                     in
                                                                    let uu____23314
                                                                    =
                                                                    let uu____23315
                                                                    =
                                                                    let uu____23320
                                                                    =
                                                                    let uu____23321
                                                                    =
                                                                    let uu____23330
                                                                    =
                                                                    force_scrutinee
                                                                    ()  in
                                                                    FStar_Syntax_Syntax.as_arg
                                                                    uu____23330
                                                                     in
                                                                    [uu____23321]
                                                                     in
                                                                    FStar_Syntax_Syntax.mk_Tm_app
                                                                    proj
                                                                    uu____23320
                                                                     in
                                                                    uu____23315
                                                                    FStar_Pervasives_Native.None
                                                                    f.FStar_Syntax_Syntax.p
                                                                     in
                                                                    FStar_Pervasives_Native.Some
                                                                    uu____23314
                                                                     in
                                                                    build_branch_guard
                                                                    scrutinee_tm2
                                                                    pi ei))
                                                           in
                                                        FStar_All.pipe_right
                                                          uu____23136
                                                          FStar_List.flatten
                                                         in
                                                      let uu____23353 =
                                                        let uu____23356 =
                                                          force_scrutinee ()
                                                           in
                                                        discriminate
                                                          uu____23356 f
                                                         in
                                                      FStar_List.append
                                                        uu____23353
                                                        sub_term_guards)
                                               | (FStar_Syntax_Syntax.Pat_dot_term
                                                  uu____23359,uu____23360) ->
                                                   []
                                               | uu____23367 ->
                                                   let uu____23372 =
                                                     let uu____23374 =
                                                       FStar_Syntax_Print.pat_to_string
                                                         pattern2
                                                        in
                                                     let uu____23376 =
                                                       FStar_Syntax_Print.term_to_string
                                                         pat_exp2
                                                        in
                                                     FStar_Util.format2
                                                       "Internal error: unexpected elaborated pattern: %s and pattern expression %s"
                                                       uu____23374
                                                       uu____23376
                                                      in
                                                   failwith uu____23372
                                                in
                                             let build_and_check_branch_guard
                                               scrutinee_tm1 pattern2 pat =
                                               let uu____23405 =
                                                 let uu____23407 =
                                                   FStar_TypeChecker_Env.should_verify
                                                     env
                                                    in
                                                 Prims.op_Negation
                                                   uu____23407
                                                  in
                                               if uu____23405
                                               then
                                                 FStar_TypeChecker_Util.fvar_const
                                                   env
                                                   FStar_Parser_Const.true_lid
                                               else
                                                 (let t =
                                                    let uu____23413 =
                                                      build_branch_guard
                                                        scrutinee_tm1
                                                        pattern2 pat
                                                       in
                                                    FStar_All.pipe_left
                                                      FStar_Syntax_Util.mk_conj_l
                                                      uu____23413
                                                     in
                                                  let uu____23422 =
                                                    FStar_Syntax_Util.type_u
                                                      ()
                                                     in
                                                  match uu____23422 with
                                                  | (k,uu____23428) ->
                                                      let uu____23429 =
                                                        tc_check_tot_or_gtot_term
                                                          scrutinee_env t k
                                                         in
                                                      (match uu____23429 with
                                                       | (t1,uu____23437,uu____23438)
                                                           -> t1))
                                                in
                                             let branch_guard =
                                               build_and_check_branch_guard
                                                 (FStar_Pervasives_Native.Some
                                                    scrutinee_tm) pattern1
                                                 norm_pat_exp
                                                in
                                             let branch_guard1 =
                                               match when_condition with
                                               | FStar_Pervasives_Native.None
                                                    -> branch_guard
                                               | FStar_Pervasives_Native.Some
                                                   w ->
                                                   FStar_Syntax_Util.mk_conj
                                                     branch_guard w
                                                in
                                             branch_guard1)
                                           in
                                        let uu____23452 =
                                          let eqs =
                                            let uu____23474 =
                                              let uu____23476 =
                                                FStar_TypeChecker_Env.should_verify
                                                  env
                                                 in
                                              Prims.op_Negation uu____23476
                                               in
                                            if uu____23474
                                            then FStar_Pervasives_Native.None
                                            else
                                              (let e =
                                                 FStar_Syntax_Subst.compress
                                                   pat_exp
                                                  in
                                               match e.FStar_Syntax_Syntax.n
                                               with
                                               | FStar_Syntax_Syntax.Tm_uvar
                                                   uu____23492 ->
                                                   FStar_Pervasives_Native.None
                                               | FStar_Syntax_Syntax.Tm_constant
                                                   uu____23507 ->
                                                   FStar_Pervasives_Native.None
                                               | FStar_Syntax_Syntax.Tm_fvar
                                                   uu____23510 ->
                                                   FStar_Pervasives_Native.None
                                               | uu____23513 ->
                                                   let uu____23514 =
                                                     let uu____23517 =
                                                       env.FStar_TypeChecker_Env.universe_of
                                                         env pat_t
                                                        in
                                                     FStar_Syntax_Util.mk_eq2
                                                       uu____23517 pat_t
                                                       scrutinee_tm e
                                                      in
                                                   FStar_Pervasives_Native.Some
                                                     uu____23514)
                                             in
                                          let uu____23520 =
                                            FStar_TypeChecker_Util.strengthen_precondition
                                              FStar_Pervasives_Native.None
                                              env branch_exp1 c g_branch
                                             in
                                          match uu____23520 with
                                          | (c1,g_branch1) ->
                                              let branch_has_layered_effect =
                                                let uu____23549 =
                                                  FStar_All.pipe_right
                                                    c1.FStar_TypeChecker_Common.eff_name
                                                    (FStar_TypeChecker_Env.norm_eff_name
                                                       env)
                                                   in
                                                FStar_All.pipe_right
                                                  uu____23549
                                                  (FStar_TypeChecker_Env.is_layered_effect
                                                     env)
                                                 in
                                              let uu____23551 =
                                                let env1 =
                                                  let uu____23557 =
                                                    FStar_All.pipe_right
                                                      pat_bvs1
                                                      (FStar_List.map
                                                         FStar_Syntax_Syntax.mk_binder)
                                                     in
                                                  FStar_TypeChecker_Env.push_binders
                                                    scrutinee_env uu____23557
                                                   in
                                                if branch_has_layered_effect
                                                then
                                                  let uu____23565 =
                                                    FStar_TypeChecker_Util.weaken_precondition
                                                      env1 c1
                                                      (FStar_TypeChecker_Common.NonTrivial
                                                         branch_guard)
                                                     in
                                                  (uu____23565,
                                                    FStar_TypeChecker_Env.trivial_guard)
                                                else
                                                  (match (eqs,
                                                           when_condition)
                                                   with
                                                   | uu____23580 when
                                                       let uu____23593 =
                                                         FStar_TypeChecker_Env.should_verify
                                                           env1
                                                          in
                                                       Prims.op_Negation
                                                         uu____23593
                                                       -> (c1, g_when)
                                                   | (FStar_Pervasives_Native.None
                                                      ,FStar_Pervasives_Native.None
                                                      ) -> (c1, g_when)
                                                   | (FStar_Pervasives_Native.Some
                                                      f,FStar_Pervasives_Native.None
                                                      ) ->
                                                       let gf =
                                                         FStar_TypeChecker_Common.NonTrivial
                                                           f
                                                          in
                                                       let g =
                                                         FStar_TypeChecker_Env.guard_of_guard_formula
                                                           gf
                                                          in
                                                       let uu____23624 =
                                                         FStar_TypeChecker_Util.weaken_precondition
                                                           env1 c1 gf
                                                          in
                                                       let uu____23625 =
                                                         FStar_TypeChecker_Env.imp_guard
                                                           g g_when
                                                          in
                                                       (uu____23624,
                                                         uu____23625)
                                                   | (FStar_Pervasives_Native.Some
                                                      f,FStar_Pervasives_Native.Some
                                                      w) ->
                                                       let g_f =
                                                         FStar_TypeChecker_Common.NonTrivial
                                                           f
                                                          in
                                                       let g_fw =
                                                         let uu____23646 =
                                                           FStar_Syntax_Util.mk_conj
                                                             f w
                                                            in
                                                         FStar_TypeChecker_Common.NonTrivial
                                                           uu____23646
                                                          in
                                                       let uu____23647 =
                                                         FStar_TypeChecker_Util.weaken_precondition
                                                           env1 c1 g_fw
                                                          in
                                                       let uu____23648 =
                                                         let uu____23649 =
                                                           FStar_TypeChecker_Env.guard_of_guard_formula
                                                             g_f
                                                            in
                                                         FStar_TypeChecker_Env.imp_guard
                                                           uu____23649 g_when
                                                          in
                                                       (uu____23647,
                                                         uu____23648)
                                                   | (FStar_Pervasives_Native.None
                                                      ,FStar_Pervasives_Native.Some
                                                      w) ->
                                                       let g_w =
                                                         FStar_TypeChecker_Common.NonTrivial
                                                           w
                                                          in
                                                       let g =
                                                         FStar_TypeChecker_Env.guard_of_guard_formula
                                                           g_w
                                                          in
                                                       let uu____23667 =
                                                         FStar_TypeChecker_Util.weaken_precondition
                                                           env1 c1 g_w
                                                          in
                                                       (uu____23667, g_when))
                                                 in
                                              (match uu____23551 with
                                               | (c_weak,g_when_weak) ->
                                                   let binders =
                                                     FStar_List.map
                                                       FStar_Syntax_Syntax.mk_binder
                                                       pat_bvs1
                                                      in
                                                   let maybe_return_c_weak
                                                     should_return1 =
                                                     let c_weak1 =
                                                       let uu____23710 =
                                                         should_return1 &&
                                                           (FStar_TypeChecker_Common.is_pure_or_ghost_lcomp
                                                              c_weak)
                                                          in
                                                       if uu____23710
                                                       then
                                                         FStar_TypeChecker_Util.maybe_assume_result_eq_pure_term
                                                           env branch_exp1
                                                           c_weak
                                                       else c_weak  in
                                                     if
                                                       branch_has_layered_effect
                                                     then
                                                       ((let uu____23717 =
                                                           FStar_All.pipe_left
                                                             (FStar_TypeChecker_Env.debug
                                                                env)
                                                             (FStar_Options.Other
                                                                "LayeredEffects")
                                                            in
                                                         if uu____23717
                                                         then
                                                           FStar_Util.print_string
                                                             "Typechecking pat_bv_tms ...\n"
                                                         else ());
                                                        (let uu____23725 =
                                                           FStar_List.fold_left2
                                                             (fun uu____23747
                                                                 ->
                                                                fun pat_bv_tm
                                                                   ->
                                                                  fun bv  ->
                                                                    match uu____23747
                                                                    with
                                                                    | 
                                                                    (env1,acc)
                                                                    ->
                                                                    let expected_t
                                                                    =
                                                                    let uu____23771
                                                                    =
                                                                    let uu____23780
                                                                    =
                                                                    FStar_Syntax_Syntax.null_binder
                                                                    pat_t  in
                                                                    [uu____23780]
                                                                     in
                                                                    let uu____23799
                                                                    =
                                                                    let uu____23802
                                                                    =
                                                                    let uu____23805
                                                                    =
                                                                    FStar_TypeChecker_Env.new_u_univ
                                                                    ()  in
                                                                    FStar_All.pipe_right
                                                                    uu____23805
                                                                    (fun
                                                                    _23808 
                                                                    ->
                                                                    FStar_Pervasives_Native.Some
                                                                    _23808)
                                                                     in
                                                                    FStar_Syntax_Syntax.mk_Total'
                                                                    bv.FStar_Syntax_Syntax.sort
                                                                    uu____23802
                                                                     in
                                                                    FStar_Syntax_Util.arrow
                                                                    uu____23771
                                                                    uu____23799
                                                                     in
                                                                    let env2
                                                                    =
                                                                    let uu___3012_23810
                                                                    =
                                                                    FStar_TypeChecker_Env.set_expected_typ
                                                                    env1
                                                                    expected_t
                                                                     in
                                                                    {
                                                                    FStar_TypeChecker_Env.solver
                                                                    =
                                                                    (uu___3012_23810.FStar_TypeChecker_Env.solver);
                                                                    FStar_TypeChecker_Env.range
                                                                    =
                                                                    (uu___3012_23810.FStar_TypeChecker_Env.range);
                                                                    FStar_TypeChecker_Env.curmodule
                                                                    =
                                                                    (uu___3012_23810.FStar_TypeChecker_Env.curmodule);
                                                                    FStar_TypeChecker_Env.gamma
                                                                    =
                                                                    (uu___3012_23810.FStar_TypeChecker_Env.gamma);
                                                                    FStar_TypeChecker_Env.gamma_sig
                                                                    =
                                                                    (uu___3012_23810.FStar_TypeChecker_Env.gamma_sig);
                                                                    FStar_TypeChecker_Env.gamma_cache
                                                                    =
                                                                    (uu___3012_23810.FStar_TypeChecker_Env.gamma_cache);
                                                                    FStar_TypeChecker_Env.modules
                                                                    =
                                                                    (uu___3012_23810.FStar_TypeChecker_Env.modules);
                                                                    FStar_TypeChecker_Env.expected_typ
                                                                    =
                                                                    (uu___3012_23810.FStar_TypeChecker_Env.expected_typ);
                                                                    FStar_TypeChecker_Env.sigtab
                                                                    =
                                                                    (uu___3012_23810.FStar_TypeChecker_Env.sigtab);
                                                                    FStar_TypeChecker_Env.attrtab
                                                                    =
                                                                    (uu___3012_23810.FStar_TypeChecker_Env.attrtab);
                                                                    FStar_TypeChecker_Env.instantiate_imp
                                                                    =
                                                                    (uu___3012_23810.FStar_TypeChecker_Env.instantiate_imp);
                                                                    FStar_TypeChecker_Env.effects
                                                                    =
                                                                    (uu___3012_23810.FStar_TypeChecker_Env.effects);
                                                                    FStar_TypeChecker_Env.generalize
                                                                    =
                                                                    (uu___3012_23810.FStar_TypeChecker_Env.generalize);
                                                                    FStar_TypeChecker_Env.letrecs
                                                                    =
                                                                    (uu___3012_23810.FStar_TypeChecker_Env.letrecs);
                                                                    FStar_TypeChecker_Env.top_level
                                                                    =
                                                                    (uu___3012_23810.FStar_TypeChecker_Env.top_level);
                                                                    FStar_TypeChecker_Env.check_uvars
                                                                    =
                                                                    (uu___3012_23810.FStar_TypeChecker_Env.check_uvars);
                                                                    FStar_TypeChecker_Env.use_eq
                                                                    =
                                                                    (uu___3012_23810.FStar_TypeChecker_Env.use_eq);
                                                                    FStar_TypeChecker_Env.is_iface
                                                                    =
                                                                    (uu___3012_23810.FStar_TypeChecker_Env.is_iface);
                                                                    FStar_TypeChecker_Env.admit
                                                                    =
                                                                    (uu___3012_23810.FStar_TypeChecker_Env.admit);
                                                                    FStar_TypeChecker_Env.lax
                                                                    = true;
                                                                    FStar_TypeChecker_Env.lax_universes
                                                                    =
                                                                    (uu___3012_23810.FStar_TypeChecker_Env.lax_universes);
                                                                    FStar_TypeChecker_Env.phase1
                                                                    =
                                                                    (uu___3012_23810.FStar_TypeChecker_Env.phase1);
                                                                    FStar_TypeChecker_Env.failhard
                                                                    =
                                                                    (uu___3012_23810.FStar_TypeChecker_Env.failhard);
                                                                    FStar_TypeChecker_Env.nosynth
                                                                    =
                                                                    (uu___3012_23810.FStar_TypeChecker_Env.nosynth);
                                                                    FStar_TypeChecker_Env.uvar_subtyping
                                                                    =
                                                                    (uu___3012_23810.FStar_TypeChecker_Env.uvar_subtyping);
                                                                    FStar_TypeChecker_Env.tc_term
                                                                    =
                                                                    (uu___3012_23810.FStar_TypeChecker_Env.tc_term);
                                                                    FStar_TypeChecker_Env.type_of
                                                                    =
                                                                    (uu___3012_23810.FStar_TypeChecker_Env.type_of);
                                                                    FStar_TypeChecker_Env.universe_of
                                                                    =
                                                                    (uu___3012_23810.FStar_TypeChecker_Env.universe_of);
                                                                    FStar_TypeChecker_Env.check_type_of
                                                                    =
                                                                    (uu___3012_23810.FStar_TypeChecker_Env.check_type_of);
                                                                    FStar_TypeChecker_Env.use_bv_sorts
                                                                    =
                                                                    (uu___3012_23810.FStar_TypeChecker_Env.use_bv_sorts);
                                                                    FStar_TypeChecker_Env.qtbl_name_and_index
                                                                    =
                                                                    (uu___3012_23810.FStar_TypeChecker_Env.qtbl_name_and_index);
                                                                    FStar_TypeChecker_Env.normalized_eff_names
                                                                    =
                                                                    (uu___3012_23810.FStar_TypeChecker_Env.normalized_eff_names);
                                                                    FStar_TypeChecker_Env.fv_delta_depths
                                                                    =
                                                                    (uu___3012_23810.FStar_TypeChecker_Env.fv_delta_depths);
                                                                    FStar_TypeChecker_Env.proof_ns
                                                                    =
                                                                    (uu___3012_23810.FStar_TypeChecker_Env.proof_ns);
                                                                    FStar_TypeChecker_Env.synth_hook
                                                                    =
                                                                    (uu___3012_23810.FStar_TypeChecker_Env.synth_hook);
                                                                    FStar_TypeChecker_Env.splice
                                                                    =
                                                                    (uu___3012_23810.FStar_TypeChecker_Env.splice);
                                                                    FStar_TypeChecker_Env.mpreprocess
                                                                    =
                                                                    (uu___3012_23810.FStar_TypeChecker_Env.mpreprocess);
                                                                    FStar_TypeChecker_Env.postprocess
                                                                    =
                                                                    (uu___3012_23810.FStar_TypeChecker_Env.postprocess);
                                                                    FStar_TypeChecker_Env.is_native_tactic
                                                                    =
                                                                    (uu___3012_23810.FStar_TypeChecker_Env.is_native_tactic);
                                                                    FStar_TypeChecker_Env.identifier_info
                                                                    =
                                                                    (uu___3012_23810.FStar_TypeChecker_Env.identifier_info);
                                                                    FStar_TypeChecker_Env.tc_hooks
                                                                    =
                                                                    (uu___3012_23810.FStar_TypeChecker_Env.tc_hooks);
                                                                    FStar_TypeChecker_Env.dsenv
                                                                    =
                                                                    (uu___3012_23810.FStar_TypeChecker_Env.dsenv);
                                                                    FStar_TypeChecker_Env.nbe
                                                                    =
                                                                    (uu___3012_23810.FStar_TypeChecker_Env.nbe);
                                                                    FStar_TypeChecker_Env.strict_args_tab
                                                                    =
                                                                    (uu___3012_23810.FStar_TypeChecker_Env.strict_args_tab);
                                                                    FStar_TypeChecker_Env.erasable_types_tab
                                                                    =
                                                                    (uu___3012_23810.FStar_TypeChecker_Env.erasable_types_tab)
                                                                    }  in
                                                                    let pat_bv_tm1
                                                                    =
                                                                    let uu____23813
                                                                    =
                                                                    tc_trivial_guard
                                                                    env2
                                                                    pat_bv_tm
                                                                     in
                                                                    FStar_All.pipe_right
                                                                    uu____23813
                                                                    FStar_Pervasives_Native.fst
                                                                     in
                                                                    let uu____23822
                                                                    =
                                                                    FStar_TypeChecker_Env.push_bv
                                                                    env2 bv
                                                                     in
                                                                    (uu____23822,
                                                                    (FStar_List.append
                                                                    acc
                                                                    [pat_bv_tm1])))
                                                             (env, [])
                                                             pat_bv_tms
                                                             pat_bvs1
                                                            in
                                                         match uu____23725
                                                         with
                                                         | (uu____23827,pat_bv_tms1)
                                                             ->
                                                             let pat_bv_tms2
                                                               =
                                                               let uu____23836
                                                                 =
                                                                 FStar_All.pipe_right
                                                                   pat_bv_tms1
                                                                   (FStar_List.map
                                                                    (fun
                                                                    pat_bv_tm
                                                                     ->
                                                                    let uu____23848
                                                                    =
                                                                    let uu____23853
                                                                    =
                                                                    let uu____23854
                                                                    =
                                                                    FStar_All.pipe_right
                                                                    scrutinee_tm
                                                                    FStar_Syntax_Syntax.as_arg
                                                                     in
                                                                    [uu____23854]
                                                                     in
                                                                    FStar_Syntax_Syntax.mk_Tm_app
                                                                    pat_bv_tm
                                                                    uu____23853
                                                                     in
                                                                    uu____23848
                                                                    FStar_Pervasives_Native.None
                                                                    FStar_Range.dummyRange))
                                                                  in
                                                               FStar_All.pipe_right
                                                                 uu____23836
                                                                 (FStar_List.map
                                                                    (
                                                                    FStar_TypeChecker_Normalize.normalize
                                                                    [FStar_TypeChecker_Env.Beta]
                                                                    env))
                                                                in
                                                             ((let uu____23892
                                                                 =
                                                                 FStar_All.pipe_left
                                                                   (FStar_TypeChecker_Env.debug
                                                                    env)
                                                                   (FStar_Options.Other
                                                                    "LayeredEffects")
                                                                  in
                                                               if uu____23892
                                                               then
                                                                 let uu____23897
                                                                   =
                                                                   FStar_List.fold_left
                                                                    (fun s 
                                                                    ->
                                                                    fun t  ->
                                                                    let uu____23906
                                                                    =
                                                                    let uu____23908
                                                                    =
                                                                    FStar_Syntax_Print.term_to_string
                                                                    t  in
                                                                    Prims.op_Hat
                                                                    ";"
                                                                    uu____23908
                                                                     in
                                                                    Prims.op_Hat
                                                                    s
                                                                    uu____23906)
                                                                    ""
                                                                    pat_bv_tms2
                                                                    in
                                                                 FStar_Util.print1
                                                                   "tc_eqn: typechecked pat_bv_tms %s"
                                                                   uu____23897
                                                               else ());
                                                              FStar_TypeChecker_Util.close_layered_lcomp
                                                                env pat_bvs1
                                                                pat_bv_tms2
                                                                c_weak1)))
                                                     else
                                                       FStar_TypeChecker_Util.close_wp_lcomp
                                                         env pat_bvs1 c_weak1
                                                      in
                                                   ((let uu____23918 =
                                                       (let uu____23922 =
                                                          FStar_TypeChecker_Env.try_lookup_effect_lid
                                                            env
                                                            FStar_Parser_Const.effect_GTot_lid
                                                           in
                                                        FStar_Option.isSome
                                                          uu____23922)
                                                         &&
                                                         (FStar_All.pipe_left
                                                            (FStar_TypeChecker_Env.debug
                                                               env)
                                                            (FStar_Options.Other
                                                               "LayeredEffects"))
                                                        in
                                                     if uu____23918
                                                     then
                                                       let uu____23928 =
                                                         let uu____23930 =
                                                           maybe_return_c_weak
                                                             false
                                                            in
                                                         FStar_TypeChecker_Common.lcomp_to_string
                                                           uu____23930
                                                          in
                                                       FStar_Util.print1
                                                         "tc_eqn: c_weak applied to false: %s\n"
                                                         uu____23928
                                                     else ());
                                                    (let uu____23935 =
                                                       FStar_TypeChecker_Env.close_guard
                                                         env binders
                                                         g_when_weak
                                                        in
                                                     let uu____23936 =
                                                       FStar_TypeChecker_Env.conj_guard
                                                         guard_pat g_branch1
                                                        in
                                                     ((c_weak.FStar_TypeChecker_Common.eff_name),
                                                       (c_weak.FStar_TypeChecker_Common.cflags),
                                                       maybe_return_c_weak,
                                                       uu____23935,
                                                       uu____23936))))
                                           in
                                        match uu____23452 with
                                        | (effect_label,cflags,maybe_return_c,g_when1,g_branch1)
                                            ->
                                            let guard =
                                              FStar_TypeChecker_Env.conj_guard
                                                g_when1 g_branch1
                                               in
                                            ((let uu____23991 =
                                                FStar_TypeChecker_Env.debug
                                                  env FStar_Options.High
                                                 in
                                              if uu____23991
                                              then
                                                let uu____23994 =
                                                  FStar_TypeChecker_Rel.guard_to_string
                                                    env guard
                                                   in
                                                FStar_All.pipe_left
                                                  (FStar_Util.print1
                                                     "Carrying guard from match: %s\n")
                                                  uu____23994
                                              else ());
                                             (let uu____24000 =
                                                FStar_Syntax_Subst.close_branch
                                                  (pattern1, when_clause1,
                                                    branch_exp1)
                                                 in
                                              let uu____24017 =
                                                let uu____24018 =
                                                  FStar_List.map
                                                    FStar_Syntax_Syntax.mk_binder
                                                    pat_bvs1
                                                   in
                                                FStar_TypeChecker_Util.close_guard_implicits
                                                  env false uu____24018 guard
                                                 in
                                              (uu____24000, branch_guard,
                                                effect_label, cflags,
                                                maybe_return_c, uu____24017,
                                                erasable1)))))))))))

and (check_top_level_let :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term ->
      (FStar_Syntax_Syntax.term * FStar_TypeChecker_Common.lcomp *
        FStar_TypeChecker_Common.guard_t))
  =
  fun env  ->
    fun e  ->
      let env1 = instantiate_both env  in
      match e.FStar_Syntax_Syntax.n with
      | FStar_Syntax_Syntax.Tm_let ((false ,lb::[]),e2) ->
          let uu____24067 = check_let_bound_def true env1 lb  in
          (match uu____24067 with
           | (e1,univ_vars1,c1,g1,annotated) ->
               let uu____24093 =
                 if
                   annotated &&
                     (Prims.op_Negation env1.FStar_TypeChecker_Env.generalize)
                 then
                   let uu____24115 =
                     FStar_TypeChecker_Normalize.reduce_uvar_solutions env1
                       e1
                      in
                   (g1, uu____24115, univ_vars1, c1)
                 else
                   (let g11 =
                      let uu____24121 =
                        FStar_TypeChecker_Rel.solve_deferred_constraints env1
                          g1
                         in
                      FStar_All.pipe_right uu____24121
                        (FStar_TypeChecker_Rel.resolve_implicits env1)
                       in
                    let uu____24122 = FStar_TypeChecker_Common.lcomp_comp c1
                       in
                    match uu____24122 with
                    | (comp1,g_comp1) ->
                        let g12 =
                          FStar_TypeChecker_Env.conj_guard g11 g_comp1  in
                        let uu____24140 =
                          let uu____24153 =
                            FStar_TypeChecker_Util.generalize env1 false
                              [((lb.FStar_Syntax_Syntax.lbname), e1, comp1)]
                             in
                          FStar_List.hd uu____24153  in
                        (match uu____24140 with
                         | (uu____24203,univs1,e11,c11,gvs) ->
                             let g13 =
                               FStar_All.pipe_left
                                 (FStar_TypeChecker_Env.map_guard g12)
                                 (FStar_TypeChecker_Normalize.normalize
                                    [FStar_TypeChecker_Env.Beta;
                                    FStar_TypeChecker_Env.DoNotUnfoldPureLets;
                                    FStar_TypeChecker_Env.CompressUvars;
                                    FStar_TypeChecker_Env.NoFullNorm;
                                    FStar_TypeChecker_Env.Exclude
                                      FStar_TypeChecker_Env.Zeta] env1)
                                in
                             let g14 =
                               FStar_TypeChecker_Env.abstract_guard_n gvs g13
                                in
                             let uu____24217 =
                               FStar_TypeChecker_Common.lcomp_of_comp c11  in
                             (g14, e11, univs1, uu____24217)))
                  in
               (match uu____24093 with
                | (g11,e11,univ_vars2,c11) ->
                    let uu____24234 =
                      let uu____24243 =
                        FStar_TypeChecker_Env.should_verify env1  in
                      if uu____24243
                      then
                        let uu____24254 =
                          FStar_TypeChecker_Util.check_top_level env1 g11 c11
                           in
                        match uu____24254 with
                        | (ok,c12) ->
                            (if ok
                             then (e2, c12)
                             else
                               ((let uu____24288 =
                                   FStar_TypeChecker_Env.get_range env1  in
                                 FStar_Errors.log_issue uu____24288
                                   FStar_TypeChecker_Err.top_level_effect);
                                (let uu____24289 =
                                   FStar_Syntax_Syntax.mk
                                     (FStar_Syntax_Syntax.Tm_meta
                                        (e2,
                                          (FStar_Syntax_Syntax.Meta_desugared
                                             FStar_Syntax_Syntax.Masked_effect)))
                                     FStar_Pervasives_Native.None
                                     e2.FStar_Syntax_Syntax.pos
                                    in
                                 (uu____24289, c12))))
                      else
                        (FStar_TypeChecker_Rel.force_trivial_guard env1 g11;
                         (let uu____24301 =
                            FStar_TypeChecker_Common.lcomp_comp c11  in
                          match uu____24301 with
                          | (comp1,g_comp1) ->
                              (FStar_TypeChecker_Rel.force_trivial_guard env1
                                 g_comp1;
                               (let c =
                                  FStar_All.pipe_right comp1
                                    (FStar_TypeChecker_Normalize.normalize_comp
                                       [FStar_TypeChecker_Env.Beta;
                                       FStar_TypeChecker_Env.NoFullNorm;
                                       FStar_TypeChecker_Env.DoNotUnfoldPureLets]
                                       env1)
                                   in
                                let e21 =
                                  let uu____24325 =
                                    FStar_Syntax_Util.is_pure_comp c  in
                                  if uu____24325
                                  then e2
                                  else
                                    ((let uu____24333 =
                                        FStar_TypeChecker_Env.get_range env1
                                         in
                                      FStar_Errors.log_issue uu____24333
                                        FStar_TypeChecker_Err.top_level_effect);
                                     FStar_Syntax_Syntax.mk
                                       (FStar_Syntax_Syntax.Tm_meta
                                          (e2,
                                            (FStar_Syntax_Syntax.Meta_desugared
                                               FStar_Syntax_Syntax.Masked_effect)))
                                       FStar_Pervasives_Native.None
                                       e2.FStar_Syntax_Syntax.pos)
                                   in
                                (e21, c)))))
                       in
                    (match uu____24234 with
                     | (e21,c12) ->
                         ((let uu____24357 =
                             FStar_TypeChecker_Env.debug env1
                               FStar_Options.Medium
                              in
                           if uu____24357
                           then
                             let uu____24360 =
                               FStar_Syntax_Print.term_to_string e11  in
                             FStar_Util.print1
                               "Let binding BEFORE tcnorm: %s\n" uu____24360
                           else ());
                          (let e12 =
                             let uu____24366 = FStar_Options.tcnorm ()  in
                             if uu____24366
                             then
                               FStar_TypeChecker_Normalize.normalize
                                 [FStar_TypeChecker_Env.UnfoldAttr
                                    [FStar_Parser_Const.tcnorm_attr];
                                 FStar_TypeChecker_Env.Exclude
                                   FStar_TypeChecker_Env.Beta;
                                 FStar_TypeChecker_Env.Exclude
                                   FStar_TypeChecker_Env.Zeta;
                                 FStar_TypeChecker_Env.NoFullNorm;
                                 FStar_TypeChecker_Env.DoNotUnfoldPureLets]
                                 env1 e11
                             else e11  in
                           (let uu____24372 =
                              FStar_TypeChecker_Env.debug env1
                                FStar_Options.Medium
                               in
                            if uu____24372
                            then
                              let uu____24375 =
                                FStar_Syntax_Print.term_to_string e12  in
                              FStar_Util.print1
                                "Let binding AFTER tcnorm: %s\n" uu____24375
                            else ());
                           (let cres =
                              let uu____24381 =
                                FStar_Syntax_Util.is_pure_or_ghost_comp c12
                                 in
                              if uu____24381
                              then
                                FStar_Syntax_Syntax.mk_Total'
                                  FStar_Syntax_Syntax.t_unit
                                  (FStar_Pervasives_Native.Some
                                     FStar_Syntax_Syntax.U_zero)
                              else
                                (let c1_comp_typ =
                                   FStar_All.pipe_right c12
                                     (FStar_TypeChecker_Env.unfold_effect_abbrev
                                        env1)
                                    in
                                 let c1_wp =
                                   match c1_comp_typ.FStar_Syntax_Syntax.effect_args
                                   with
                                   | (wp,uu____24389)::[] -> wp
                                   | uu____24414 ->
                                       failwith
                                         "Impossible! check_top_level_let: got unexpected effect args"
                                    in
                                 let c1_eff_decl =
                                   FStar_TypeChecker_Env.get_effect_decl env1
                                     c1_comp_typ.FStar_Syntax_Syntax.effect_name
                                    in
                                 let wp2 =
                                   let ret1 =
                                     FStar_All.pipe_right c1_eff_decl
                                       FStar_Syntax_Util.get_return_vc_combinator
                                      in
                                   let uu____24431 =
                                     let uu____24436 =
                                       FStar_TypeChecker_Env.inst_effect_fun_with
                                         [FStar_Syntax_Syntax.U_zero] env1
                                         c1_eff_decl ret1
                                        in
                                     let uu____24437 =
                                       let uu____24438 =
                                         FStar_Syntax_Syntax.as_arg
                                           FStar_Syntax_Syntax.t_unit
                                          in
                                       let uu____24447 =
                                         let uu____24458 =
                                           FStar_Syntax_Syntax.as_arg
                                             FStar_Syntax_Syntax.unit_const
                                            in
                                         [uu____24458]  in
                                       uu____24438 :: uu____24447  in
                                     FStar_Syntax_Syntax.mk_Tm_app
                                       uu____24436 uu____24437
                                      in
                                   uu____24431 FStar_Pervasives_Native.None
                                     e21.FStar_Syntax_Syntax.pos
                                    in
                                 let wp =
                                   let bind1 =
                                     FStar_All.pipe_right c1_eff_decl
                                       FStar_Syntax_Util.get_bind_vc_combinator
                                      in
                                   let uu____24495 =
                                     let uu____24500 =
                                       FStar_TypeChecker_Env.inst_effect_fun_with
                                         (FStar_List.append
                                            c1_comp_typ.FStar_Syntax_Syntax.comp_univs
                                            [FStar_Syntax_Syntax.U_zero])
                                         env1 c1_eff_decl bind1
                                        in
                                     let uu____24501 =
                                       let uu____24502 =
                                         let uu____24511 =
                                           FStar_Syntax_Syntax.mk
                                             (FStar_Syntax_Syntax.Tm_constant
                                                (FStar_Const.Const_range
                                                   (lb.FStar_Syntax_Syntax.lbpos)))
                                             FStar_Pervasives_Native.None
                                             lb.FStar_Syntax_Syntax.lbpos
                                            in
                                         FStar_All.pipe_left
                                           FStar_Syntax_Syntax.as_arg
                                           uu____24511
                                          in
                                       let uu____24520 =
                                         let uu____24531 =
                                           FStar_All.pipe_left
                                             FStar_Syntax_Syntax.as_arg
                                             c1_comp_typ.FStar_Syntax_Syntax.result_typ
                                            in
                                         let uu____24548 =
                                           let uu____24559 =
                                             FStar_Syntax_Syntax.as_arg
                                               FStar_Syntax_Syntax.t_unit
                                              in
                                           let uu____24568 =
                                             let uu____24579 =
                                               FStar_Syntax_Syntax.as_arg
                                                 c1_wp
                                                in
                                             let uu____24588 =
                                               let uu____24599 =
                                                 let uu____24608 =
                                                   let uu____24609 =
                                                     let uu____24610 =
                                                       FStar_Syntax_Syntax.null_binder
                                                         c1_comp_typ.FStar_Syntax_Syntax.result_typ
                                                        in
                                                     [uu____24610]  in
                                                   FStar_Syntax_Util.abs
                                                     uu____24609 wp2
                                                     (FStar_Pervasives_Native.Some
                                                        (FStar_Syntax_Util.mk_residual_comp
                                                           FStar_Parser_Const.effect_Tot_lid
                                                           FStar_Pervasives_Native.None
                                                           [FStar_Syntax_Syntax.TOTAL]))
                                                    in
                                                 FStar_All.pipe_left
                                                   FStar_Syntax_Syntax.as_arg
                                                   uu____24608
                                                  in
                                               [uu____24599]  in
                                             uu____24579 :: uu____24588  in
                                           uu____24559 :: uu____24568  in
                                         uu____24531 :: uu____24548  in
                                       uu____24502 :: uu____24520  in
                                     FStar_Syntax_Syntax.mk_Tm_app
                                       uu____24500 uu____24501
                                      in
                                   uu____24495 FStar_Pervasives_Native.None
                                     lb.FStar_Syntax_Syntax.lbpos
                                    in
                                 let uu____24687 =
                                   let uu____24688 =
                                     let uu____24699 =
                                       FStar_Syntax_Syntax.as_arg wp  in
                                     [uu____24699]  in
                                   {
                                     FStar_Syntax_Syntax.comp_univs =
                                       [FStar_Syntax_Syntax.U_zero];
                                     FStar_Syntax_Syntax.effect_name =
                                       (c1_comp_typ.FStar_Syntax_Syntax.effect_name);
                                     FStar_Syntax_Syntax.result_typ =
                                       FStar_Syntax_Syntax.t_unit;
                                     FStar_Syntax_Syntax.effect_args =
                                       uu____24688;
                                     FStar_Syntax_Syntax.flags = []
                                   }  in
                                 FStar_Syntax_Syntax.mk_Comp uu____24687)
                               in
                            let lb1 =
                              FStar_Syntax_Util.close_univs_and_mk_letbinding
                                FStar_Pervasives_Native.None
                                lb.FStar_Syntax_Syntax.lbname univ_vars2
                                (FStar_Syntax_Util.comp_result c12)
                                (FStar_Syntax_Util.comp_effect_name c12) e12
                                lb.FStar_Syntax_Syntax.lbattrs
                                lb.FStar_Syntax_Syntax.lbpos
                               in
                            let uu____24727 =
                              FStar_Syntax_Syntax.mk
                                (FStar_Syntax_Syntax.Tm_let
                                   ((false, [lb1]), e21))
                                FStar_Pervasives_Native.None
                                e.FStar_Syntax_Syntax.pos
                               in
                            let uu____24741 =
                              FStar_TypeChecker_Common.lcomp_of_comp cres  in
                            (uu____24727, uu____24741,
                              FStar_TypeChecker_Env.trivial_guard)))))))
      | uu____24742 -> failwith "Impossible"

and (maybe_intro_smt_lemma :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term ->
      FStar_TypeChecker_Common.lcomp -> FStar_TypeChecker_Common.lcomp)
  =
  fun env  ->
    fun lem_typ  ->
      fun c2  ->
        let uu____24753 = FStar_Syntax_Util.is_smt_lemma lem_typ  in
        if uu____24753
        then
          let universe_of_binders bs =
            let uu____24780 =
              FStar_List.fold_left
                (fun uu____24805  ->
                   fun b  ->
                     match uu____24805 with
                     | (env1,us) ->
                         let u =
                           env1.FStar_TypeChecker_Env.universe_of env1
                             (FStar_Pervasives_Native.fst b).FStar_Syntax_Syntax.sort
                            in
                         let env2 =
                           FStar_TypeChecker_Env.push_binders env1 [b]  in
                         (env2, (u :: us))) (env, []) bs
               in
            match uu____24780 with | (uu____24853,us) -> FStar_List.rev us
             in
          let quant =
            FStar_Syntax_Util.smt_lemma_as_forall lem_typ universe_of_binders
             in
          FStar_TypeChecker_Util.weaken_precondition env c2
            (FStar_TypeChecker_Common.NonTrivial quant)
        else c2

and (check_inner_let :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term ->
      (FStar_Syntax_Syntax.term * FStar_TypeChecker_Common.lcomp *
        FStar_TypeChecker_Common.guard_t))
  =
  fun env  ->
    fun e  ->
      let env1 = instantiate_both env  in
      match e.FStar_Syntax_Syntax.n with
      | FStar_Syntax_Syntax.Tm_let ((false ,lb::[]),e2) ->
          let env2 =
            let uu___3137_24889 = env1  in
            {
              FStar_TypeChecker_Env.solver =
                (uu___3137_24889.FStar_TypeChecker_Env.solver);
              FStar_TypeChecker_Env.range =
                (uu___3137_24889.FStar_TypeChecker_Env.range);
              FStar_TypeChecker_Env.curmodule =
                (uu___3137_24889.FStar_TypeChecker_Env.curmodule);
              FStar_TypeChecker_Env.gamma =
                (uu___3137_24889.FStar_TypeChecker_Env.gamma);
              FStar_TypeChecker_Env.gamma_sig =
                (uu___3137_24889.FStar_TypeChecker_Env.gamma_sig);
              FStar_TypeChecker_Env.gamma_cache =
                (uu___3137_24889.FStar_TypeChecker_Env.gamma_cache);
              FStar_TypeChecker_Env.modules =
                (uu___3137_24889.FStar_TypeChecker_Env.modules);
              FStar_TypeChecker_Env.expected_typ =
                (uu___3137_24889.FStar_TypeChecker_Env.expected_typ);
              FStar_TypeChecker_Env.sigtab =
                (uu___3137_24889.FStar_TypeChecker_Env.sigtab);
              FStar_TypeChecker_Env.attrtab =
                (uu___3137_24889.FStar_TypeChecker_Env.attrtab);
              FStar_TypeChecker_Env.instantiate_imp =
                (uu___3137_24889.FStar_TypeChecker_Env.instantiate_imp);
              FStar_TypeChecker_Env.effects =
                (uu___3137_24889.FStar_TypeChecker_Env.effects);
              FStar_TypeChecker_Env.generalize =
                (uu___3137_24889.FStar_TypeChecker_Env.generalize);
              FStar_TypeChecker_Env.letrecs =
                (uu___3137_24889.FStar_TypeChecker_Env.letrecs);
              FStar_TypeChecker_Env.top_level = false;
              FStar_TypeChecker_Env.check_uvars =
                (uu___3137_24889.FStar_TypeChecker_Env.check_uvars);
              FStar_TypeChecker_Env.use_eq =
                (uu___3137_24889.FStar_TypeChecker_Env.use_eq);
              FStar_TypeChecker_Env.is_iface =
                (uu___3137_24889.FStar_TypeChecker_Env.is_iface);
              FStar_TypeChecker_Env.admit =
                (uu___3137_24889.FStar_TypeChecker_Env.admit);
              FStar_TypeChecker_Env.lax =
                (uu___3137_24889.FStar_TypeChecker_Env.lax);
              FStar_TypeChecker_Env.lax_universes =
                (uu___3137_24889.FStar_TypeChecker_Env.lax_universes);
              FStar_TypeChecker_Env.phase1 =
                (uu___3137_24889.FStar_TypeChecker_Env.phase1);
              FStar_TypeChecker_Env.failhard =
                (uu___3137_24889.FStar_TypeChecker_Env.failhard);
              FStar_TypeChecker_Env.nosynth =
                (uu___3137_24889.FStar_TypeChecker_Env.nosynth);
              FStar_TypeChecker_Env.uvar_subtyping =
                (uu___3137_24889.FStar_TypeChecker_Env.uvar_subtyping);
              FStar_TypeChecker_Env.tc_term =
                (uu___3137_24889.FStar_TypeChecker_Env.tc_term);
              FStar_TypeChecker_Env.type_of =
                (uu___3137_24889.FStar_TypeChecker_Env.type_of);
              FStar_TypeChecker_Env.universe_of =
                (uu___3137_24889.FStar_TypeChecker_Env.universe_of);
              FStar_TypeChecker_Env.check_type_of =
                (uu___3137_24889.FStar_TypeChecker_Env.check_type_of);
              FStar_TypeChecker_Env.use_bv_sorts =
                (uu___3137_24889.FStar_TypeChecker_Env.use_bv_sorts);
              FStar_TypeChecker_Env.qtbl_name_and_index =
                (uu___3137_24889.FStar_TypeChecker_Env.qtbl_name_and_index);
              FStar_TypeChecker_Env.normalized_eff_names =
                (uu___3137_24889.FStar_TypeChecker_Env.normalized_eff_names);
              FStar_TypeChecker_Env.fv_delta_depths =
                (uu___3137_24889.FStar_TypeChecker_Env.fv_delta_depths);
              FStar_TypeChecker_Env.proof_ns =
                (uu___3137_24889.FStar_TypeChecker_Env.proof_ns);
              FStar_TypeChecker_Env.synth_hook =
                (uu___3137_24889.FStar_TypeChecker_Env.synth_hook);
              FStar_TypeChecker_Env.splice =
                (uu___3137_24889.FStar_TypeChecker_Env.splice);
              FStar_TypeChecker_Env.mpreprocess =
                (uu___3137_24889.FStar_TypeChecker_Env.mpreprocess);
              FStar_TypeChecker_Env.postprocess =
                (uu___3137_24889.FStar_TypeChecker_Env.postprocess);
              FStar_TypeChecker_Env.is_native_tactic =
                (uu___3137_24889.FStar_TypeChecker_Env.is_native_tactic);
              FStar_TypeChecker_Env.identifier_info =
                (uu___3137_24889.FStar_TypeChecker_Env.identifier_info);
              FStar_TypeChecker_Env.tc_hooks =
                (uu___3137_24889.FStar_TypeChecker_Env.tc_hooks);
              FStar_TypeChecker_Env.dsenv =
                (uu___3137_24889.FStar_TypeChecker_Env.dsenv);
              FStar_TypeChecker_Env.nbe =
                (uu___3137_24889.FStar_TypeChecker_Env.nbe);
              FStar_TypeChecker_Env.strict_args_tab =
                (uu___3137_24889.FStar_TypeChecker_Env.strict_args_tab);
              FStar_TypeChecker_Env.erasable_types_tab =
                (uu___3137_24889.FStar_TypeChecker_Env.erasable_types_tab)
            }  in
          let uu____24891 =
            let uu____24903 =
              let uu____24904 = FStar_TypeChecker_Env.clear_expected_typ env2
                 in
              FStar_All.pipe_right uu____24904 FStar_Pervasives_Native.fst
               in
            check_let_bound_def false uu____24903 lb  in
          (match uu____24891 with
           | (e1,uu____24927,c1,g1,annotated) ->
               let pure_or_ghost =
                 FStar_TypeChecker_Common.is_pure_or_ghost_lcomp c1  in
               let is_inline_let =
                 FStar_Util.for_some
                   (FStar_Syntax_Util.is_fvar
                      FStar_Parser_Const.inline_let_attr)
                   lb.FStar_Syntax_Syntax.lbattrs
                  in
               (if is_inline_let && (Prims.op_Negation pure_or_ghost)
                then
                  (let uu____24941 =
                     let uu____24947 =
                       let uu____24949 = FStar_Syntax_Print.term_to_string e1
                          in
                       let uu____24951 =
                         FStar_Syntax_Print.lid_to_string
                           c1.FStar_TypeChecker_Common.eff_name
                          in
                       FStar_Util.format2
                         "Definitions marked @inline_let are expected to be pure or ghost; got an expression \"%s\" with effect \"%s\""
                         uu____24949 uu____24951
                        in
                     (FStar_Errors.Fatal_ExpectedPureExpression, uu____24947)
                      in
                   FStar_Errors.raise_error uu____24941
                     e1.FStar_Syntax_Syntax.pos)
                else ();
                (let attrs =
                   let uu____24962 =
                     (pure_or_ghost && (Prims.op_Negation is_inline_let)) &&
                       (FStar_Syntax_Util.is_unit
                          c1.FStar_TypeChecker_Common.res_typ)
                      in
                   if uu____24962
                   then FStar_Syntax_Util.inline_let_attr ::
                     (lb.FStar_Syntax_Syntax.lbattrs)
                   else lb.FStar_Syntax_Syntax.lbattrs  in
                 let x =
                   let uu___3152_24974 =
                     FStar_Util.left lb.FStar_Syntax_Syntax.lbname  in
                   {
                     FStar_Syntax_Syntax.ppname =
                       (uu___3152_24974.FStar_Syntax_Syntax.ppname);
                     FStar_Syntax_Syntax.index =
                       (uu___3152_24974.FStar_Syntax_Syntax.index);
                     FStar_Syntax_Syntax.sort =
                       (c1.FStar_TypeChecker_Common.res_typ)
                   }  in
                 let uu____24975 =
                   let uu____24980 =
                     let uu____24981 = FStar_Syntax_Syntax.mk_binder x  in
                     [uu____24981]  in
                   FStar_Syntax_Subst.open_term uu____24980 e2  in
                 match uu____24975 with
                 | (xb,e21) ->
                     let xbinder = FStar_List.hd xb  in
                     let x1 = FStar_Pervasives_Native.fst xbinder  in
                     let env_x = FStar_TypeChecker_Env.push_bv env2 x1  in
                     let uu____25025 = tc_term env_x e21  in
                     (match uu____25025 with
                      | (e22,c2,g2) ->
                          let c21 =
                            maybe_intro_smt_lemma env_x
                              c1.FStar_TypeChecker_Common.res_typ c2
                             in
                          let cres =
                            FStar_TypeChecker_Util.maybe_return_e2_and_bind
                              e1.FStar_Syntax_Syntax.pos env2
                              (FStar_Pervasives_Native.Some e1) c1 e22
                              ((FStar_Pervasives_Native.Some x1), c21)
                             in
                          let e11 =
                            FStar_TypeChecker_Util.maybe_lift env2 e1
                              c1.FStar_TypeChecker_Common.eff_name
                              cres.FStar_TypeChecker_Common.eff_name
                              c1.FStar_TypeChecker_Common.res_typ
                             in
                          let e23 =
                            FStar_TypeChecker_Util.maybe_lift env2 e22
                              c21.FStar_TypeChecker_Common.eff_name
                              cres.FStar_TypeChecker_Common.eff_name
                              c21.FStar_TypeChecker_Common.res_typ
                             in
                          let lb1 =
                            FStar_Syntax_Util.mk_letbinding
                              (FStar_Util.Inl x1) []
                              c1.FStar_TypeChecker_Common.res_typ
                              cres.FStar_TypeChecker_Common.eff_name e11
                              attrs lb.FStar_Syntax_Syntax.lbpos
                             in
                          let e3 =
                            let uu____25051 =
                              let uu____25058 =
                                let uu____25059 =
                                  let uu____25073 =
                                    FStar_Syntax_Subst.close xb e23  in
                                  ((false, [lb1]), uu____25073)  in
                                FStar_Syntax_Syntax.Tm_let uu____25059  in
                              FStar_Syntax_Syntax.mk uu____25058  in
                            uu____25051 FStar_Pervasives_Native.None
                              e.FStar_Syntax_Syntax.pos
                             in
                          let e4 =
                            FStar_TypeChecker_Util.maybe_monadic env2 e3
                              cres.FStar_TypeChecker_Common.eff_name
                              cres.FStar_TypeChecker_Common.res_typ
                             in
                          let x_eq_e1 =
                            let uu____25091 =
                              let uu____25092 =
                                env2.FStar_TypeChecker_Env.universe_of env2
                                  c1.FStar_TypeChecker_Common.res_typ
                                 in
                              let uu____25093 =
                                FStar_Syntax_Syntax.bv_to_name x1  in
                              FStar_Syntax_Util.mk_eq2 uu____25092
                                c1.FStar_TypeChecker_Common.res_typ
                                uu____25093 e11
                               in
                            FStar_All.pipe_left
                              (fun _25094  ->
                                 FStar_TypeChecker_Common.NonTrivial _25094)
                              uu____25091
                             in
                          let g21 =
                            let uu____25096 =
                              let uu____25097 =
                                FStar_TypeChecker_Env.guard_of_guard_formula
                                  x_eq_e1
                                 in
                              FStar_TypeChecker_Env.imp_guard uu____25097 g2
                               in
                            FStar_TypeChecker_Env.close_guard env2 xb
                              uu____25096
                             in
                          let g22 =
                            let uu____25099 =
                              let uu____25101 =
                                FStar_All.pipe_right
                                  cres.FStar_TypeChecker_Common.eff_name
                                  (FStar_TypeChecker_Env.norm_eff_name env2)
                                 in
                              FStar_All.pipe_right uu____25101
                                (FStar_TypeChecker_Env.is_layered_effect env2)
                               in
                            FStar_TypeChecker_Util.close_guard_implicits env2
                              uu____25099 xb g21
                             in
                          let guard = FStar_TypeChecker_Env.conj_guard g1 g22
                             in
                          let uu____25104 =
                            let uu____25106 =
                              FStar_TypeChecker_Env.expected_typ env2  in
                            FStar_Option.isSome uu____25106  in
                          if uu____25104
                          then
                            let tt =
                              let uu____25117 =
                                FStar_TypeChecker_Env.expected_typ env2  in
                              FStar_All.pipe_right uu____25117
                                FStar_Option.get
                               in
                            ((let uu____25123 =
                                FStar_All.pipe_left
                                  (FStar_TypeChecker_Env.debug env2)
                                  (FStar_Options.Other "Exports")
                                 in
                              if uu____25123
                              then
                                let uu____25128 =
                                  FStar_Syntax_Print.term_to_string tt  in
                                let uu____25130 =
                                  FStar_Syntax_Print.term_to_string
                                    cres.FStar_TypeChecker_Common.res_typ
                                   in
                                FStar_Util.print2
                                  "Got expected type from env %s\ncres.res_typ=%s\n"
                                  uu____25128 uu____25130
                              else ());
                             (e4, cres, guard))
                          else
                            (let uu____25137 =
                               check_no_escape FStar_Pervasives_Native.None
                                 env2 [x1]
                                 cres.FStar_TypeChecker_Common.res_typ
                                in
                             match uu____25137 with
                             | (t,g_ex) ->
                                 ((let uu____25151 =
                                     FStar_All.pipe_left
                                       (FStar_TypeChecker_Env.debug env2)
                                       (FStar_Options.Other "Exports")
                                      in
                                   if uu____25151
                                   then
                                     let uu____25156 =
                                       FStar_Syntax_Print.term_to_string
                                         cres.FStar_TypeChecker_Common.res_typ
                                        in
                                     let uu____25158 =
                                       FStar_Syntax_Print.term_to_string t
                                        in
                                     FStar_Util.print2
                                       "Checked %s has no escaping types; normalized to %s\n"
                                       uu____25156 uu____25158
                                   else ());
                                  (let uu____25163 =
                                     FStar_TypeChecker_Env.conj_guard g_ex
                                       guard
                                      in
                                   (e4,
                                     (let uu___3185_25165 = cres  in
                                      {
                                        FStar_TypeChecker_Common.eff_name =
                                          (uu___3185_25165.FStar_TypeChecker_Common.eff_name);
                                        FStar_TypeChecker_Common.res_typ = t;
                                        FStar_TypeChecker_Common.cflags =
                                          (uu___3185_25165.FStar_TypeChecker_Common.cflags);
                                        FStar_TypeChecker_Common.comp_thunk =
                                          (uu___3185_25165.FStar_TypeChecker_Common.comp_thunk)
                                      }), uu____25163))))))))
      | uu____25166 ->
          failwith "Impossible (inner let with more than one lb)"

and (check_top_level_let_rec :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term ->
      (FStar_Syntax_Syntax.term * FStar_TypeChecker_Common.lcomp *
        FStar_TypeChecker_Common.guard_t))
  =
  fun env  ->
    fun top  ->
      let env1 = instantiate_both env  in
      match top.FStar_Syntax_Syntax.n with
      | FStar_Syntax_Syntax.Tm_let ((true ,lbs),e2) ->
          let uu____25202 = FStar_Syntax_Subst.open_let_rec lbs e2  in
          (match uu____25202 with
           | (lbs1,e21) ->
               let uu____25221 =
                 FStar_TypeChecker_Env.clear_expected_typ env1  in
               (match uu____25221 with
                | (env0,topt) ->
                    let uu____25240 = build_let_rec_env true env0 lbs1  in
                    (match uu____25240 with
                     | (lbs2,rec_env,g_t) ->
                         let uu____25263 = check_let_recs rec_env lbs2  in
                         (match uu____25263 with
                          | (lbs3,g_lbs) ->
                              let g_lbs1 =
                                let uu____25283 =
                                  let uu____25284 =
                                    FStar_TypeChecker_Env.conj_guard g_t
                                      g_lbs
                                     in
                                  FStar_All.pipe_right uu____25284
                                    (FStar_TypeChecker_Rel.solve_deferred_constraints
                                       env1)
                                   in
                                FStar_All.pipe_right uu____25283
                                  (FStar_TypeChecker_Rel.resolve_implicits
                                     env1)
                                 in
                              let all_lb_names =
                                let uu____25290 =
                                  FStar_All.pipe_right lbs3
                                    (FStar_List.map
                                       (fun lb  ->
                                          FStar_Util.right
                                            lb.FStar_Syntax_Syntax.lbname))
                                   in
                                FStar_All.pipe_right uu____25290
                                  (fun _25307  ->
                                     FStar_Pervasives_Native.Some _25307)
                                 in
                              let lbs4 =
                                if
                                  Prims.op_Negation
                                    env1.FStar_TypeChecker_Env.generalize
                                then
                                  FStar_All.pipe_right lbs3
                                    (FStar_List.map
                                       (fun lb  ->
                                          let lbdef =
                                            FStar_TypeChecker_Normalize.reduce_uvar_solutions
                                              env1
                                              lb.FStar_Syntax_Syntax.lbdef
                                             in
                                          if
                                            lb.FStar_Syntax_Syntax.lbunivs =
                                              []
                                          then lb
                                          else
                                            FStar_Syntax_Util.close_univs_and_mk_letbinding
                                              all_lb_names
                                              lb.FStar_Syntax_Syntax.lbname
                                              lb.FStar_Syntax_Syntax.lbunivs
                                              lb.FStar_Syntax_Syntax.lbtyp
                                              lb.FStar_Syntax_Syntax.lbeff
                                              lbdef
                                              lb.FStar_Syntax_Syntax.lbattrs
                                              lb.FStar_Syntax_Syntax.lbpos))
                                else
                                  (let ecs =
                                     let uu____25344 =
                                       FStar_All.pipe_right lbs3
                                         (FStar_List.map
                                            (fun lb  ->
                                               let uu____25378 =
                                                 FStar_Syntax_Syntax.mk_Total
                                                   lb.FStar_Syntax_Syntax.lbtyp
                                                  in
                                               ((lb.FStar_Syntax_Syntax.lbname),
                                                 (lb.FStar_Syntax_Syntax.lbdef),
                                                 uu____25378)))
                                        in
                                     FStar_TypeChecker_Util.generalize env1
                                       true uu____25344
                                      in
                                   FStar_List.map2
                                     (fun uu____25413  ->
                                        fun lb  ->
                                          match uu____25413 with
                                          | (x,uvs,e,c,gvs) ->
                                              FStar_Syntax_Util.close_univs_and_mk_letbinding
                                                all_lb_names x uvs
                                                (FStar_Syntax_Util.comp_result
                                                   c)
                                                (FStar_Syntax_Util.comp_effect_name
                                                   c) e
                                                lb.FStar_Syntax_Syntax.lbattrs
                                                lb.FStar_Syntax_Syntax.lbpos)
                                     ecs lbs3)
                                 in
                              let cres =
                                let uu____25461 =
                                  FStar_Syntax_Syntax.mk_Total
                                    FStar_Syntax_Syntax.t_unit
                                   in
                                FStar_All.pipe_left
                                  FStar_TypeChecker_Common.lcomp_of_comp
                                  uu____25461
                                 in
                              let uu____25462 =
                                FStar_Syntax_Subst.close_let_rec lbs4 e21  in
                              (match uu____25462 with
                               | (lbs5,e22) ->
                                   ((let uu____25482 =
                                       FStar_TypeChecker_Rel.discharge_guard
                                         env1 g_lbs1
                                        in
                                     FStar_All.pipe_right uu____25482
                                       (FStar_TypeChecker_Rel.force_trivial_guard
                                          env1));
                                    (let uu____25483 =
                                       FStar_Syntax_Syntax.mk
                                         (FStar_Syntax_Syntax.Tm_let
                                            ((true, lbs5), e22))
                                         FStar_Pervasives_Native.None
                                         top.FStar_Syntax_Syntax.pos
                                        in
                                     (uu____25483, cres,
                                       FStar_TypeChecker_Env.trivial_guard))))))))
      | uu____25497 -> failwith "Impossible"

and (check_inner_let_rec :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term ->
      (FStar_Syntax_Syntax.term * FStar_TypeChecker_Common.lcomp *
        FStar_TypeChecker_Common.guard_t))
  =
  fun env  ->
    fun top  ->
      let env1 = instantiate_both env  in
      match top.FStar_Syntax_Syntax.n with
      | FStar_Syntax_Syntax.Tm_let ((true ,lbs),e2) ->
          let uu____25533 = FStar_Syntax_Subst.open_let_rec lbs e2  in
          (match uu____25533 with
           | (lbs1,e21) ->
               let uu____25552 =
                 FStar_TypeChecker_Env.clear_expected_typ env1  in
               (match uu____25552 with
                | (env0,topt) ->
                    let uu____25571 = build_let_rec_env false env0 lbs1  in
                    (match uu____25571 with
                     | (lbs2,rec_env,g_t) ->
                         let uu____25594 =
                           let uu____25601 = check_let_recs rec_env lbs2  in
                           FStar_All.pipe_right uu____25601
                             (fun uu____25624  ->
                                match uu____25624 with
                                | (lbs3,g) ->
                                    let uu____25643 =
                                      FStar_TypeChecker_Env.conj_guard g_t g
                                       in
                                    (lbs3, uu____25643))
                            in
                         (match uu____25594 with
                          | (lbs3,g_lbs) ->
                              let uu____25658 =
                                FStar_All.pipe_right lbs3
                                  (FStar_Util.fold_map
                                     (fun env2  ->
                                        fun lb  ->
                                          let x =
                                            let uu___3260_25681 =
                                              FStar_Util.left
                                                lb.FStar_Syntax_Syntax.lbname
                                               in
                                            {
                                              FStar_Syntax_Syntax.ppname =
                                                (uu___3260_25681.FStar_Syntax_Syntax.ppname);
                                              FStar_Syntax_Syntax.index =
                                                (uu___3260_25681.FStar_Syntax_Syntax.index);
                                              FStar_Syntax_Syntax.sort =
                                                (lb.FStar_Syntax_Syntax.lbtyp)
                                            }  in
                                          let lb1 =
                                            let uu___3263_25683 = lb  in
                                            {
                                              FStar_Syntax_Syntax.lbname =
                                                (FStar_Util.Inl x);
                                              FStar_Syntax_Syntax.lbunivs =
                                                (uu___3263_25683.FStar_Syntax_Syntax.lbunivs);
                                              FStar_Syntax_Syntax.lbtyp =
                                                (uu___3263_25683.FStar_Syntax_Syntax.lbtyp);
                                              FStar_Syntax_Syntax.lbeff =
                                                (uu___3263_25683.FStar_Syntax_Syntax.lbeff);
                                              FStar_Syntax_Syntax.lbdef =
                                                (uu___3263_25683.FStar_Syntax_Syntax.lbdef);
                                              FStar_Syntax_Syntax.lbattrs =
                                                (uu___3263_25683.FStar_Syntax_Syntax.lbattrs);
                                              FStar_Syntax_Syntax.lbpos =
                                                (uu___3263_25683.FStar_Syntax_Syntax.lbpos)
                                            }  in
                                          let env3 =
                                            FStar_TypeChecker_Env.push_let_binding
                                              env2
                                              lb1.FStar_Syntax_Syntax.lbname
                                              ([],
                                                (lb1.FStar_Syntax_Syntax.lbtyp))
                                             in
                                          (env3, lb1)) env1)
                                 in
                              (match uu____25658 with
                               | (env2,lbs4) ->
                                   let bvs =
                                     FStar_All.pipe_right lbs4
                                       (FStar_List.map
                                          (fun lb  ->
                                             FStar_Util.left
                                               lb.FStar_Syntax_Syntax.lbname))
                                      in
                                   let uu____25710 = tc_term env2 e21  in
                                   (match uu____25710 with
                                    | (e22,cres,g2) ->
                                        let cres1 =
                                          FStar_List.fold_right
                                            (fun lb  ->
                                               fun cres1  ->
                                                 maybe_intro_smt_lemma env2
                                                   lb.FStar_Syntax_Syntax.lbtyp
                                                   cres1) lbs4 cres
                                           in
                                        let cres2 =
                                          FStar_TypeChecker_Util.maybe_assume_result_eq_pure_term
                                            env2 e22 cres1
                                           in
                                        let cres3 =
                                          FStar_TypeChecker_Common.lcomp_set_flags
                                            cres2
                                            [FStar_Syntax_Syntax.SHOULD_NOT_INLINE]
                                           in
                                        let guard =
                                          let uu____25734 =
                                            let uu____25735 =
                                              FStar_List.map
                                                FStar_Syntax_Syntax.mk_binder
                                                bvs
                                               in
                                            FStar_TypeChecker_Env.close_guard
                                              env2 uu____25735 g2
                                             in
                                          FStar_TypeChecker_Env.conj_guard
                                            g_lbs uu____25734
                                           in
                                        let cres4 =
                                          FStar_TypeChecker_Util.close_wp_lcomp
                                            env2 bvs cres3
                                           in
                                        let tres =
                                          norm env2
                                            cres4.FStar_TypeChecker_Common.res_typ
                                           in
                                        let cres5 =
                                          let uu___3284_25745 = cres4  in
                                          {
                                            FStar_TypeChecker_Common.eff_name
                                              =
                                              (uu___3284_25745.FStar_TypeChecker_Common.eff_name);
                                            FStar_TypeChecker_Common.res_typ
                                              = tres;
                                            FStar_TypeChecker_Common.cflags =
                                              (uu___3284_25745.FStar_TypeChecker_Common.cflags);
                                            FStar_TypeChecker_Common.comp_thunk
                                              =
                                              (uu___3284_25745.FStar_TypeChecker_Common.comp_thunk)
                                          }  in
                                        let guard1 =
                                          let bs =
                                            FStar_All.pipe_right lbs4
                                              (FStar_List.map
                                                 (fun lb  ->
                                                    let uu____25753 =
                                                      FStar_Util.left
                                                        lb.FStar_Syntax_Syntax.lbname
                                                       in
                                                    FStar_Syntax_Syntax.mk_binder
                                                      uu____25753))
                                             in
                                          FStar_TypeChecker_Util.close_guard_implicits
                                            env2 false bs guard
                                           in
                                        let uu____25755 =
                                          FStar_Syntax_Subst.close_let_rec
                                            lbs4 e22
                                           in
                                        (match uu____25755 with
                                         | (lbs5,e23) ->
                                             let e =
                                               FStar_Syntax_Syntax.mk
                                                 (FStar_Syntax_Syntax.Tm_let
                                                    ((true, lbs5), e23))
                                                 FStar_Pervasives_Native.None
                                                 top.FStar_Syntax_Syntax.pos
                                                in
                                             (match topt with
                                              | FStar_Pervasives_Native.Some
                                                  uu____25796 ->
                                                  (e, cres5, guard1)
                                              | FStar_Pervasives_Native.None 
                                                  ->
                                                  let uu____25797 =
                                                    check_no_escape
                                                      FStar_Pervasives_Native.None
                                                      env2 bvs tres
                                                     in
                                                  (match uu____25797 with
                                                   | (tres1,g_ex) ->
                                                       let cres6 =
                                                         let uu___3300_25811
                                                           = cres5  in
                                                         {
                                                           FStar_TypeChecker_Common.eff_name
                                                             =
                                                             (uu___3300_25811.FStar_TypeChecker_Common.eff_name);
                                                           FStar_TypeChecker_Common.res_typ
                                                             = tres1;
                                                           FStar_TypeChecker_Common.cflags
                                                             =
                                                             (uu___3300_25811.FStar_TypeChecker_Common.cflags);
                                                           FStar_TypeChecker_Common.comp_thunk
                                                             =
                                                             (uu___3300_25811.FStar_TypeChecker_Common.comp_thunk)
                                                         }  in
                                                       let uu____25812 =
                                                         FStar_TypeChecker_Env.conj_guard
                                                           g_ex guard1
                                                          in
                                                       (e, cres6,
                                                         uu____25812))))))))))
      | uu____25813 -> failwith "Impossible"

and (build_let_rec_env :
  Prims.bool ->
    FStar_TypeChecker_Env.env ->
      FStar_Syntax_Syntax.letbinding Prims.list ->
        (FStar_Syntax_Syntax.letbinding Prims.list *
          FStar_TypeChecker_Env.env_t * FStar_TypeChecker_Common.guard_t))
  =
  fun top_level  ->
    fun env  ->
      fun lbs  ->
        let env0 = env  in
        let termination_check_enabled lbname lbdef lbtyp =
          let uu____25861 = FStar_Options.ml_ish ()  in
          if uu____25861
          then false
          else
            (let t = FStar_TypeChecker_Normalize.unfold_whnf env lbtyp  in
             let uu____25869 = FStar_Syntax_Util.arrow_formals_comp t  in
             match uu____25869 with
             | (formals,c) ->
                 let uu____25901 = FStar_Syntax_Util.abs_formals lbdef  in
                 (match uu____25901 with
                  | (actuals,uu____25912,uu____25913) ->
                      if
                        ((FStar_List.length formals) < Prims.int_one) ||
                          ((FStar_List.length actuals) < Prims.int_one)
                      then
                        let uu____25934 =
                          let uu____25940 =
                            let uu____25942 =
                              FStar_Syntax_Print.term_to_string lbdef  in
                            let uu____25944 =
                              FStar_Syntax_Print.term_to_string lbtyp  in
                            FStar_Util.format2
                              "Only function literals with arrow types can be defined recursively; got %s : %s"
                              uu____25942 uu____25944
                             in
                          (FStar_Errors.Fatal_RecursiveFunctionLiteral,
                            uu____25940)
                           in
                        FStar_Errors.raise_error uu____25934
                          lbtyp.FStar_Syntax_Syntax.pos
                      else
                        (let actuals1 =
                           let uu____25952 =
                             FStar_TypeChecker_Env.set_expected_typ env lbtyp
                              in
                           FStar_TypeChecker_Util.maybe_add_implicit_binders
                             uu____25952 actuals
                            in
                         if
                           (FStar_List.length formals) <>
                             (FStar_List.length actuals1)
                         then
                           (let actuals_msg =
                              let n1 = FStar_List.length actuals1  in
                              if n1 = Prims.int_one
                              then "1 argument was found"
                              else
                                (let uu____25983 =
                                   FStar_Util.string_of_int n1  in
                                 FStar_Util.format1 "%s arguments were found"
                                   uu____25983)
                               in
                            let formals_msg =
                              let n1 = FStar_List.length formals  in
                              if n1 = Prims.int_one
                              then "1 argument"
                              else
                                (let uu____26002 =
                                   FStar_Util.string_of_int n1  in
                                 FStar_Util.format1 "%s arguments"
                                   uu____26002)
                               in
                            let msg =
                              let uu____26007 =
                                FStar_Syntax_Print.term_to_string lbtyp  in
                              let uu____26009 =
                                FStar_Syntax_Print.lbname_to_string lbname
                                 in
                              FStar_Util.format4
                                "From its type %s, the definition of `let rec %s` expects a function with %s, but %s"
                                uu____26007 uu____26009 formals_msg
                                actuals_msg
                               in
                            FStar_Errors.raise_error
                              (FStar_Errors.Fatal_LetRecArgumentMismatch,
                                msg) lbdef.FStar_Syntax_Syntax.pos)
                         else ();
                         (let quals =
                            FStar_TypeChecker_Env.lookup_effect_quals env
                              (FStar_Syntax_Util.comp_effect_name c)
                             in
                          FStar_All.pipe_right quals
                            (FStar_List.contains
                               FStar_Syntax_Syntax.TotalEffect)))))
           in
        let uu____26021 =
          FStar_List.fold_left
            (fun uu____26054  ->
               fun lb  ->
                 match uu____26054 with
                 | (lbs1,env1,g_acc) ->
                     let uu____26079 =
                       FStar_TypeChecker_Util.extract_let_rec_annotation env1
                         lb
                        in
                     (match uu____26079 with
                      | (univ_vars1,t,check_t) ->
                          let env2 =
                            FStar_TypeChecker_Env.push_univ_vars env1
                              univ_vars1
                             in
                          let e =
                            FStar_Syntax_Util.unascribe
                              lb.FStar_Syntax_Syntax.lbdef
                             in
                          let uu____26102 =
                            if Prims.op_Negation check_t
                            then (g_acc, t)
                            else
                              (let env01 =
                                 FStar_TypeChecker_Env.push_univ_vars env0
                                   univ_vars1
                                  in
                               let uu____26121 =
                                 let uu____26128 =
                                   let uu____26129 =
                                     FStar_Syntax_Util.type_u ()  in
                                   FStar_All.pipe_left
                                     FStar_Pervasives_Native.fst uu____26129
                                    in
                                 tc_check_tot_or_gtot_term
                                   (let uu___3346_26140 = env01  in
                                    {
                                      FStar_TypeChecker_Env.solver =
                                        (uu___3346_26140.FStar_TypeChecker_Env.solver);
                                      FStar_TypeChecker_Env.range =
                                        (uu___3346_26140.FStar_TypeChecker_Env.range);
                                      FStar_TypeChecker_Env.curmodule =
                                        (uu___3346_26140.FStar_TypeChecker_Env.curmodule);
                                      FStar_TypeChecker_Env.gamma =
                                        (uu___3346_26140.FStar_TypeChecker_Env.gamma);
                                      FStar_TypeChecker_Env.gamma_sig =
                                        (uu___3346_26140.FStar_TypeChecker_Env.gamma_sig);
                                      FStar_TypeChecker_Env.gamma_cache =
                                        (uu___3346_26140.FStar_TypeChecker_Env.gamma_cache);
                                      FStar_TypeChecker_Env.modules =
                                        (uu___3346_26140.FStar_TypeChecker_Env.modules);
                                      FStar_TypeChecker_Env.expected_typ =
                                        (uu___3346_26140.FStar_TypeChecker_Env.expected_typ);
                                      FStar_TypeChecker_Env.sigtab =
                                        (uu___3346_26140.FStar_TypeChecker_Env.sigtab);
                                      FStar_TypeChecker_Env.attrtab =
                                        (uu___3346_26140.FStar_TypeChecker_Env.attrtab);
                                      FStar_TypeChecker_Env.instantiate_imp =
                                        (uu___3346_26140.FStar_TypeChecker_Env.instantiate_imp);
                                      FStar_TypeChecker_Env.effects =
                                        (uu___3346_26140.FStar_TypeChecker_Env.effects);
                                      FStar_TypeChecker_Env.generalize =
                                        (uu___3346_26140.FStar_TypeChecker_Env.generalize);
                                      FStar_TypeChecker_Env.letrecs =
                                        (uu___3346_26140.FStar_TypeChecker_Env.letrecs);
                                      FStar_TypeChecker_Env.top_level =
                                        (uu___3346_26140.FStar_TypeChecker_Env.top_level);
                                      FStar_TypeChecker_Env.check_uvars =
                                        true;
                                      FStar_TypeChecker_Env.use_eq =
                                        (uu___3346_26140.FStar_TypeChecker_Env.use_eq);
                                      FStar_TypeChecker_Env.is_iface =
                                        (uu___3346_26140.FStar_TypeChecker_Env.is_iface);
                                      FStar_TypeChecker_Env.admit =
                                        (uu___3346_26140.FStar_TypeChecker_Env.admit);
                                      FStar_TypeChecker_Env.lax =
                                        (uu___3346_26140.FStar_TypeChecker_Env.lax);
                                      FStar_TypeChecker_Env.lax_universes =
                                        (uu___3346_26140.FStar_TypeChecker_Env.lax_universes);
                                      FStar_TypeChecker_Env.phase1 =
                                        (uu___3346_26140.FStar_TypeChecker_Env.phase1);
                                      FStar_TypeChecker_Env.failhard =
                                        (uu___3346_26140.FStar_TypeChecker_Env.failhard);
                                      FStar_TypeChecker_Env.nosynth =
                                        (uu___3346_26140.FStar_TypeChecker_Env.nosynth);
                                      FStar_TypeChecker_Env.uvar_subtyping =
                                        (uu___3346_26140.FStar_TypeChecker_Env.uvar_subtyping);
                                      FStar_TypeChecker_Env.tc_term =
                                        (uu___3346_26140.FStar_TypeChecker_Env.tc_term);
                                      FStar_TypeChecker_Env.type_of =
                                        (uu___3346_26140.FStar_TypeChecker_Env.type_of);
                                      FStar_TypeChecker_Env.universe_of =
                                        (uu___3346_26140.FStar_TypeChecker_Env.universe_of);
                                      FStar_TypeChecker_Env.check_type_of =
                                        (uu___3346_26140.FStar_TypeChecker_Env.check_type_of);
                                      FStar_TypeChecker_Env.use_bv_sorts =
                                        (uu___3346_26140.FStar_TypeChecker_Env.use_bv_sorts);
                                      FStar_TypeChecker_Env.qtbl_name_and_index
                                        =
                                        (uu___3346_26140.FStar_TypeChecker_Env.qtbl_name_and_index);
                                      FStar_TypeChecker_Env.normalized_eff_names
                                        =
                                        (uu___3346_26140.FStar_TypeChecker_Env.normalized_eff_names);
                                      FStar_TypeChecker_Env.fv_delta_depths =
                                        (uu___3346_26140.FStar_TypeChecker_Env.fv_delta_depths);
                                      FStar_TypeChecker_Env.proof_ns =
                                        (uu___3346_26140.FStar_TypeChecker_Env.proof_ns);
                                      FStar_TypeChecker_Env.synth_hook =
                                        (uu___3346_26140.FStar_TypeChecker_Env.synth_hook);
                                      FStar_TypeChecker_Env.splice =
                                        (uu___3346_26140.FStar_TypeChecker_Env.splice);
                                      FStar_TypeChecker_Env.mpreprocess =
                                        (uu___3346_26140.FStar_TypeChecker_Env.mpreprocess);
                                      FStar_TypeChecker_Env.postprocess =
                                        (uu___3346_26140.FStar_TypeChecker_Env.postprocess);
                                      FStar_TypeChecker_Env.is_native_tactic
                                        =
                                        (uu___3346_26140.FStar_TypeChecker_Env.is_native_tactic);
                                      FStar_TypeChecker_Env.identifier_info =
                                        (uu___3346_26140.FStar_TypeChecker_Env.identifier_info);
                                      FStar_TypeChecker_Env.tc_hooks =
                                        (uu___3346_26140.FStar_TypeChecker_Env.tc_hooks);
                                      FStar_TypeChecker_Env.dsenv =
                                        (uu___3346_26140.FStar_TypeChecker_Env.dsenv);
                                      FStar_TypeChecker_Env.nbe =
                                        (uu___3346_26140.FStar_TypeChecker_Env.nbe);
                                      FStar_TypeChecker_Env.strict_args_tab =
                                        (uu___3346_26140.FStar_TypeChecker_Env.strict_args_tab);
                                      FStar_TypeChecker_Env.erasable_types_tab
                                        =
                                        (uu___3346_26140.FStar_TypeChecker_Env.erasable_types_tab)
                                    }) t uu____26128
                                  in
                               match uu____26121 with
                               | (t1,uu____26149,g) ->
                                   let uu____26151 =
                                     let uu____26152 =
                                       let uu____26153 =
                                         FStar_All.pipe_right g
                                           (FStar_TypeChecker_Rel.resolve_implicits
                                              env2)
                                          in
                                       FStar_All.pipe_right uu____26153
                                         (FStar_TypeChecker_Rel.discharge_guard
                                            env2)
                                        in
                                     FStar_TypeChecker_Env.conj_guard g_acc
                                       uu____26152
                                      in
                                   let uu____26154 = norm env01 t1  in
                                   (uu____26151, uu____26154))
                             in
                          (match uu____26102 with
                           | (g,t1) ->
                               let env3 =
                                 let uu____26174 =
                                   termination_check_enabled
                                     lb.FStar_Syntax_Syntax.lbname e t1
                                    in
                                 if uu____26174
                                 then
                                   let uu___3356_26177 = env2  in
                                   {
                                     FStar_TypeChecker_Env.solver =
                                       (uu___3356_26177.FStar_TypeChecker_Env.solver);
                                     FStar_TypeChecker_Env.range =
                                       (uu___3356_26177.FStar_TypeChecker_Env.range);
                                     FStar_TypeChecker_Env.curmodule =
                                       (uu___3356_26177.FStar_TypeChecker_Env.curmodule);
                                     FStar_TypeChecker_Env.gamma =
                                       (uu___3356_26177.FStar_TypeChecker_Env.gamma);
                                     FStar_TypeChecker_Env.gamma_sig =
                                       (uu___3356_26177.FStar_TypeChecker_Env.gamma_sig);
                                     FStar_TypeChecker_Env.gamma_cache =
                                       (uu___3356_26177.FStar_TypeChecker_Env.gamma_cache);
                                     FStar_TypeChecker_Env.modules =
                                       (uu___3356_26177.FStar_TypeChecker_Env.modules);
                                     FStar_TypeChecker_Env.expected_typ =
                                       (uu___3356_26177.FStar_TypeChecker_Env.expected_typ);
                                     FStar_TypeChecker_Env.sigtab =
                                       (uu___3356_26177.FStar_TypeChecker_Env.sigtab);
                                     FStar_TypeChecker_Env.attrtab =
                                       (uu___3356_26177.FStar_TypeChecker_Env.attrtab);
                                     FStar_TypeChecker_Env.instantiate_imp =
                                       (uu___3356_26177.FStar_TypeChecker_Env.instantiate_imp);
                                     FStar_TypeChecker_Env.effects =
                                       (uu___3356_26177.FStar_TypeChecker_Env.effects);
                                     FStar_TypeChecker_Env.generalize =
                                       (uu___3356_26177.FStar_TypeChecker_Env.generalize);
                                     FStar_TypeChecker_Env.letrecs =
                                       (((lb.FStar_Syntax_Syntax.lbname), t1,
                                          univ_vars1) ::
                                       (env2.FStar_TypeChecker_Env.letrecs));
                                     FStar_TypeChecker_Env.top_level =
                                       (uu___3356_26177.FStar_TypeChecker_Env.top_level);
                                     FStar_TypeChecker_Env.check_uvars =
                                       (uu___3356_26177.FStar_TypeChecker_Env.check_uvars);
                                     FStar_TypeChecker_Env.use_eq =
                                       (uu___3356_26177.FStar_TypeChecker_Env.use_eq);
                                     FStar_TypeChecker_Env.is_iface =
                                       (uu___3356_26177.FStar_TypeChecker_Env.is_iface);
                                     FStar_TypeChecker_Env.admit =
                                       (uu___3356_26177.FStar_TypeChecker_Env.admit);
                                     FStar_TypeChecker_Env.lax =
                                       (uu___3356_26177.FStar_TypeChecker_Env.lax);
                                     FStar_TypeChecker_Env.lax_universes =
                                       (uu___3356_26177.FStar_TypeChecker_Env.lax_universes);
                                     FStar_TypeChecker_Env.phase1 =
                                       (uu___3356_26177.FStar_TypeChecker_Env.phase1);
                                     FStar_TypeChecker_Env.failhard =
                                       (uu___3356_26177.FStar_TypeChecker_Env.failhard);
                                     FStar_TypeChecker_Env.nosynth =
                                       (uu___3356_26177.FStar_TypeChecker_Env.nosynth);
                                     FStar_TypeChecker_Env.uvar_subtyping =
                                       (uu___3356_26177.FStar_TypeChecker_Env.uvar_subtyping);
                                     FStar_TypeChecker_Env.tc_term =
                                       (uu___3356_26177.FStar_TypeChecker_Env.tc_term);
                                     FStar_TypeChecker_Env.type_of =
                                       (uu___3356_26177.FStar_TypeChecker_Env.type_of);
                                     FStar_TypeChecker_Env.universe_of =
                                       (uu___3356_26177.FStar_TypeChecker_Env.universe_of);
                                     FStar_TypeChecker_Env.check_type_of =
                                       (uu___3356_26177.FStar_TypeChecker_Env.check_type_of);
                                     FStar_TypeChecker_Env.use_bv_sorts =
                                       (uu___3356_26177.FStar_TypeChecker_Env.use_bv_sorts);
                                     FStar_TypeChecker_Env.qtbl_name_and_index
                                       =
                                       (uu___3356_26177.FStar_TypeChecker_Env.qtbl_name_and_index);
                                     FStar_TypeChecker_Env.normalized_eff_names
                                       =
                                       (uu___3356_26177.FStar_TypeChecker_Env.normalized_eff_names);
                                     FStar_TypeChecker_Env.fv_delta_depths =
                                       (uu___3356_26177.FStar_TypeChecker_Env.fv_delta_depths);
                                     FStar_TypeChecker_Env.proof_ns =
                                       (uu___3356_26177.FStar_TypeChecker_Env.proof_ns);
                                     FStar_TypeChecker_Env.synth_hook =
                                       (uu___3356_26177.FStar_TypeChecker_Env.synth_hook);
                                     FStar_TypeChecker_Env.splice =
                                       (uu___3356_26177.FStar_TypeChecker_Env.splice);
                                     FStar_TypeChecker_Env.mpreprocess =
                                       (uu___3356_26177.FStar_TypeChecker_Env.mpreprocess);
                                     FStar_TypeChecker_Env.postprocess =
                                       (uu___3356_26177.FStar_TypeChecker_Env.postprocess);
                                     FStar_TypeChecker_Env.is_native_tactic =
                                       (uu___3356_26177.FStar_TypeChecker_Env.is_native_tactic);
                                     FStar_TypeChecker_Env.identifier_info =
                                       (uu___3356_26177.FStar_TypeChecker_Env.identifier_info);
                                     FStar_TypeChecker_Env.tc_hooks =
                                       (uu___3356_26177.FStar_TypeChecker_Env.tc_hooks);
                                     FStar_TypeChecker_Env.dsenv =
                                       (uu___3356_26177.FStar_TypeChecker_Env.dsenv);
                                     FStar_TypeChecker_Env.nbe =
                                       (uu___3356_26177.FStar_TypeChecker_Env.nbe);
                                     FStar_TypeChecker_Env.strict_args_tab =
                                       (uu___3356_26177.FStar_TypeChecker_Env.strict_args_tab);
                                     FStar_TypeChecker_Env.erasable_types_tab
                                       =
                                       (uu___3356_26177.FStar_TypeChecker_Env.erasable_types_tab)
                                   }
                                 else
                                   FStar_TypeChecker_Env.push_let_binding
                                     env2 lb.FStar_Syntax_Syntax.lbname
                                     (univ_vars1, t1)
                                  in
                               let lb1 =
                                 let uu___3359_26191 = lb  in
                                 {
                                   FStar_Syntax_Syntax.lbname =
                                     (uu___3359_26191.FStar_Syntax_Syntax.lbname);
                                   FStar_Syntax_Syntax.lbunivs = univ_vars1;
                                   FStar_Syntax_Syntax.lbtyp = t1;
                                   FStar_Syntax_Syntax.lbeff =
                                     (uu___3359_26191.FStar_Syntax_Syntax.lbeff);
                                   FStar_Syntax_Syntax.lbdef = e;
                                   FStar_Syntax_Syntax.lbattrs =
                                     (uu___3359_26191.FStar_Syntax_Syntax.lbattrs);
                                   FStar_Syntax_Syntax.lbpos =
                                     (uu___3359_26191.FStar_Syntax_Syntax.lbpos)
                                 }  in
                               ((lb1 :: lbs1), env3, g))))
            ([], env, FStar_TypeChecker_Env.trivial_guard) lbs
           in
        match uu____26021 with
        | (lbs1,env1,g) -> ((FStar_List.rev lbs1), env1, g)

and (check_let_recs :
  FStar_TypeChecker_Env.env_t ->
    FStar_Syntax_Syntax.letbinding Prims.list ->
      (FStar_Syntax_Syntax.letbinding Prims.list *
        FStar_TypeChecker_Env.guard_t))
  =
  fun env  ->
    fun lbs  ->
      let uu____26217 =
        let uu____26226 =
          FStar_All.pipe_right lbs
            (FStar_List.map
               (fun lb  ->
                  let uu____26252 =
                    FStar_Syntax_Util.abs_formals
                      lb.FStar_Syntax_Syntax.lbdef
                     in
                  match uu____26252 with
                  | (bs,t,lcomp) ->
                      (match bs with
                       | [] ->
                           let uu____26282 =
                             FStar_Syntax_Syntax.range_of_lbname
                               lb.FStar_Syntax_Syntax.lbname
                              in
                           FStar_Errors.raise_error
                             (FStar_Errors.Fatal_RecursiveFunctionLiteral,
                               "Only function literals may be defined recursively")
                             uu____26282
                       | uu____26289 ->
                           let lb1 =
                             let uu___3376_26292 = lb  in
                             let uu____26293 =
                               FStar_Syntax_Util.abs bs t lcomp  in
                             {
                               FStar_Syntax_Syntax.lbname =
                                 (uu___3376_26292.FStar_Syntax_Syntax.lbname);
                               FStar_Syntax_Syntax.lbunivs =
                                 (uu___3376_26292.FStar_Syntax_Syntax.lbunivs);
                               FStar_Syntax_Syntax.lbtyp =
                                 (uu___3376_26292.FStar_Syntax_Syntax.lbtyp);
                               FStar_Syntax_Syntax.lbeff =
                                 (uu___3376_26292.FStar_Syntax_Syntax.lbeff);
                               FStar_Syntax_Syntax.lbdef = uu____26293;
                               FStar_Syntax_Syntax.lbattrs =
                                 (uu___3376_26292.FStar_Syntax_Syntax.lbattrs);
                               FStar_Syntax_Syntax.lbpos =
                                 (uu___3376_26292.FStar_Syntax_Syntax.lbpos)
                             }  in
                           let uu____26296 =
                             let uu____26303 =
                               FStar_TypeChecker_Env.set_expected_typ env
                                 lb1.FStar_Syntax_Syntax.lbtyp
                                in
                             tc_tot_or_gtot_term uu____26303
                               lb1.FStar_Syntax_Syntax.lbdef
                              in
                           (match uu____26296 with
                            | (e,c,g) ->
                                ((let uu____26312 =
                                    let uu____26314 =
                                      FStar_TypeChecker_Common.is_total_lcomp
                                        c
                                       in
                                    Prims.op_Negation uu____26314  in
                                  if uu____26312
                                  then
                                    FStar_Errors.raise_error
                                      (FStar_Errors.Fatal_UnexpectedGTotForLetRec,
                                        "Expected let rec to be a Tot term; got effect GTot")
                                      e.FStar_Syntax_Syntax.pos
                                  else ());
                                 (let lb2 =
                                    FStar_Syntax_Util.mk_letbinding
                                      lb1.FStar_Syntax_Syntax.lbname
                                      lb1.FStar_Syntax_Syntax.lbunivs
                                      lb1.FStar_Syntax_Syntax.lbtyp
                                      FStar_Parser_Const.effect_Tot_lid e
                                      lb1.FStar_Syntax_Syntax.lbattrs
                                      lb1.FStar_Syntax_Syntax.lbpos
                                     in
                                  (lb2, g)))))))
           in
        FStar_All.pipe_right uu____26226 FStar_List.unzip  in
      match uu____26217 with
      | (lbs1,gs) ->
          let g_lbs =
            FStar_List.fold_right FStar_TypeChecker_Env.conj_guard gs
              FStar_TypeChecker_Env.trivial_guard
             in
          (lbs1, g_lbs)

and (check_let_bound_def :
  Prims.bool ->
    FStar_TypeChecker_Env.env ->
      FStar_Syntax_Syntax.letbinding ->
        (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.univ_names *
          FStar_TypeChecker_Common.lcomp * FStar_TypeChecker_Common.guard_t *
          Prims.bool))
  =
  fun top_level  ->
    fun env  ->
      fun lb  ->
        let uu____26370 = FStar_TypeChecker_Env.clear_expected_typ env  in
        match uu____26370 with
        | (env1,uu____26389) ->
            let e1 = lb.FStar_Syntax_Syntax.lbdef  in
            let uu____26397 = check_lbtyp top_level env lb  in
            (match uu____26397 with
             | (topt,wf_annot,univ_vars1,univ_opening,env11) ->
                 (if (Prims.op_Negation top_level) && (univ_vars1 <> [])
                  then
                    FStar_Errors.raise_error
                      (FStar_Errors.Fatal_UniversePolymorphicInnerLetBound,
                        "Inner let-bound definitions cannot be universe polymorphic")
                      e1.FStar_Syntax_Syntax.pos
                  else ();
                  (let e11 = FStar_Syntax_Subst.subst univ_opening e1  in
                   let uu____26446 =
                     tc_maybe_toplevel_term
                       (let uu___3407_26455 = env11  in
                        {
                          FStar_TypeChecker_Env.solver =
                            (uu___3407_26455.FStar_TypeChecker_Env.solver);
                          FStar_TypeChecker_Env.range =
                            (uu___3407_26455.FStar_TypeChecker_Env.range);
                          FStar_TypeChecker_Env.curmodule =
                            (uu___3407_26455.FStar_TypeChecker_Env.curmodule);
                          FStar_TypeChecker_Env.gamma =
                            (uu___3407_26455.FStar_TypeChecker_Env.gamma);
                          FStar_TypeChecker_Env.gamma_sig =
                            (uu___3407_26455.FStar_TypeChecker_Env.gamma_sig);
                          FStar_TypeChecker_Env.gamma_cache =
                            (uu___3407_26455.FStar_TypeChecker_Env.gamma_cache);
                          FStar_TypeChecker_Env.modules =
                            (uu___3407_26455.FStar_TypeChecker_Env.modules);
                          FStar_TypeChecker_Env.expected_typ =
                            (uu___3407_26455.FStar_TypeChecker_Env.expected_typ);
                          FStar_TypeChecker_Env.sigtab =
                            (uu___3407_26455.FStar_TypeChecker_Env.sigtab);
                          FStar_TypeChecker_Env.attrtab =
                            (uu___3407_26455.FStar_TypeChecker_Env.attrtab);
                          FStar_TypeChecker_Env.instantiate_imp =
                            (uu___3407_26455.FStar_TypeChecker_Env.instantiate_imp);
                          FStar_TypeChecker_Env.effects =
                            (uu___3407_26455.FStar_TypeChecker_Env.effects);
                          FStar_TypeChecker_Env.generalize =
                            (uu___3407_26455.FStar_TypeChecker_Env.generalize);
                          FStar_TypeChecker_Env.letrecs =
                            (uu___3407_26455.FStar_TypeChecker_Env.letrecs);
                          FStar_TypeChecker_Env.top_level = top_level;
                          FStar_TypeChecker_Env.check_uvars =
                            (uu___3407_26455.FStar_TypeChecker_Env.check_uvars);
                          FStar_TypeChecker_Env.use_eq =
                            (uu___3407_26455.FStar_TypeChecker_Env.use_eq);
                          FStar_TypeChecker_Env.is_iface =
                            (uu___3407_26455.FStar_TypeChecker_Env.is_iface);
                          FStar_TypeChecker_Env.admit =
                            (uu___3407_26455.FStar_TypeChecker_Env.admit);
                          FStar_TypeChecker_Env.lax =
                            (uu___3407_26455.FStar_TypeChecker_Env.lax);
                          FStar_TypeChecker_Env.lax_universes =
                            (uu___3407_26455.FStar_TypeChecker_Env.lax_universes);
                          FStar_TypeChecker_Env.phase1 =
                            (uu___3407_26455.FStar_TypeChecker_Env.phase1);
                          FStar_TypeChecker_Env.failhard =
                            (uu___3407_26455.FStar_TypeChecker_Env.failhard);
                          FStar_TypeChecker_Env.nosynth =
                            (uu___3407_26455.FStar_TypeChecker_Env.nosynth);
                          FStar_TypeChecker_Env.uvar_subtyping =
                            (uu___3407_26455.FStar_TypeChecker_Env.uvar_subtyping);
                          FStar_TypeChecker_Env.tc_term =
                            (uu___3407_26455.FStar_TypeChecker_Env.tc_term);
                          FStar_TypeChecker_Env.type_of =
                            (uu___3407_26455.FStar_TypeChecker_Env.type_of);
                          FStar_TypeChecker_Env.universe_of =
                            (uu___3407_26455.FStar_TypeChecker_Env.universe_of);
                          FStar_TypeChecker_Env.check_type_of =
                            (uu___3407_26455.FStar_TypeChecker_Env.check_type_of);
                          FStar_TypeChecker_Env.use_bv_sorts =
                            (uu___3407_26455.FStar_TypeChecker_Env.use_bv_sorts);
                          FStar_TypeChecker_Env.qtbl_name_and_index =
                            (uu___3407_26455.FStar_TypeChecker_Env.qtbl_name_and_index);
                          FStar_TypeChecker_Env.normalized_eff_names =
                            (uu___3407_26455.FStar_TypeChecker_Env.normalized_eff_names);
                          FStar_TypeChecker_Env.fv_delta_depths =
                            (uu___3407_26455.FStar_TypeChecker_Env.fv_delta_depths);
                          FStar_TypeChecker_Env.proof_ns =
                            (uu___3407_26455.FStar_TypeChecker_Env.proof_ns);
                          FStar_TypeChecker_Env.synth_hook =
                            (uu___3407_26455.FStar_TypeChecker_Env.synth_hook);
                          FStar_TypeChecker_Env.splice =
                            (uu___3407_26455.FStar_TypeChecker_Env.splice);
                          FStar_TypeChecker_Env.mpreprocess =
                            (uu___3407_26455.FStar_TypeChecker_Env.mpreprocess);
                          FStar_TypeChecker_Env.postprocess =
                            (uu___3407_26455.FStar_TypeChecker_Env.postprocess);
                          FStar_TypeChecker_Env.is_native_tactic =
                            (uu___3407_26455.FStar_TypeChecker_Env.is_native_tactic);
                          FStar_TypeChecker_Env.identifier_info =
                            (uu___3407_26455.FStar_TypeChecker_Env.identifier_info);
                          FStar_TypeChecker_Env.tc_hooks =
                            (uu___3407_26455.FStar_TypeChecker_Env.tc_hooks);
                          FStar_TypeChecker_Env.dsenv =
                            (uu___3407_26455.FStar_TypeChecker_Env.dsenv);
                          FStar_TypeChecker_Env.nbe =
                            (uu___3407_26455.FStar_TypeChecker_Env.nbe);
                          FStar_TypeChecker_Env.strict_args_tab =
                            (uu___3407_26455.FStar_TypeChecker_Env.strict_args_tab);
                          FStar_TypeChecker_Env.erasable_types_tab =
                            (uu___3407_26455.FStar_TypeChecker_Env.erasable_types_tab)
                        }) e11
                      in
                   match uu____26446 with
                   | (e12,c1,g1) ->
                       let uu____26470 =
                         let uu____26475 =
                           FStar_TypeChecker_Env.set_range env11
                             e12.FStar_Syntax_Syntax.pos
                            in
                         FStar_TypeChecker_Util.strengthen_precondition
                           (FStar_Pervasives_Native.Some
                              (fun uu____26481  ->
                                 FStar_Util.return_all
                                   FStar_TypeChecker_Err.ill_kinded_type))
                           uu____26475 e12 c1 wf_annot
                          in
                       (match uu____26470 with
                        | (c11,guard_f) ->
                            let g11 =
                              FStar_TypeChecker_Env.conj_guard g1 guard_f  in
                            ((let uu____26498 =
                                FStar_TypeChecker_Env.debug env
                                  FStar_Options.Extreme
                                 in
                              if uu____26498
                              then
                                let uu____26501 =
                                  FStar_Syntax_Print.lbname_to_string
                                    lb.FStar_Syntax_Syntax.lbname
                                   in
                                let uu____26503 =
                                  FStar_TypeChecker_Common.lcomp_to_string
                                    c11
                                   in
                                let uu____26505 =
                                  FStar_TypeChecker_Rel.guard_to_string env
                                    g11
                                   in
                                FStar_Util.print3
                                  "checked let-bound def %s : %s guard is %s\n"
                                  uu____26501 uu____26503 uu____26505
                              else ());
                             (e12, univ_vars1, c11, g11,
                               (FStar_Option.isSome topt)))))))

and (check_lbtyp :
  Prims.bool ->
    FStar_TypeChecker_Env.env ->
      FStar_Syntax_Syntax.letbinding ->
        (FStar_Syntax_Syntax.typ FStar_Pervasives_Native.option *
          FStar_TypeChecker_Common.guard_t * FStar_Syntax_Syntax.univ_names *
          FStar_Syntax_Syntax.subst_elt Prims.list *
          FStar_TypeChecker_Env.env))
  =
  fun top_level  ->
    fun env  ->
      fun lb  ->
        let t = FStar_Syntax_Subst.compress lb.FStar_Syntax_Syntax.lbtyp  in
        match t.FStar_Syntax_Syntax.n with
        | FStar_Syntax_Syntax.Tm_unknown  ->
            let uu____26544 =
              FStar_Syntax_Subst.univ_var_opening
                lb.FStar_Syntax_Syntax.lbunivs
               in
            (match uu____26544 with
             | (univ_opening,univ_vars1) ->
                 let uu____26577 =
                   FStar_TypeChecker_Env.push_univ_vars env univ_vars1  in
                 (FStar_Pervasives_Native.None,
                   FStar_TypeChecker_Env.trivial_guard, univ_vars1,
                   univ_opening, uu____26577))
        | uu____26582 ->
            let uu____26583 =
              FStar_Syntax_Subst.univ_var_opening
                lb.FStar_Syntax_Syntax.lbunivs
               in
            (match uu____26583 with
             | (univ_opening,univ_vars1) ->
                 let t1 = FStar_Syntax_Subst.subst univ_opening t  in
                 let env1 =
                   FStar_TypeChecker_Env.push_univ_vars env univ_vars1  in
                 if
                   top_level &&
                     (Prims.op_Negation env.FStar_TypeChecker_Env.generalize)
                 then
                   let uu____26633 =
                     FStar_TypeChecker_Env.set_expected_typ env1 t1  in
                   ((FStar_Pervasives_Native.Some t1),
                     FStar_TypeChecker_Env.trivial_guard, univ_vars1,
                     univ_opening, uu____26633)
                 else
                   (let uu____26640 = FStar_Syntax_Util.type_u ()  in
                    match uu____26640 with
                    | (k,uu____26660) ->
                        let uu____26661 = tc_check_tot_or_gtot_term env1 t1 k
                           in
                        (match uu____26661 with
                         | (t2,uu____26683,g) ->
                             ((let uu____26686 =
                                 FStar_TypeChecker_Env.debug env
                                   FStar_Options.Medium
                                  in
                               if uu____26686
                               then
                                 let uu____26689 =
                                   let uu____26691 =
                                     FStar_Syntax_Util.range_of_lbname
                                       lb.FStar_Syntax_Syntax.lbname
                                      in
                                   FStar_Range.string_of_range uu____26691
                                    in
                                 let uu____26692 =
                                   FStar_Syntax_Print.term_to_string t2  in
                                 FStar_Util.print2
                                   "(%s) Checked type annotation %s\n"
                                   uu____26689 uu____26692
                               else ());
                              (let t3 = norm env1 t2  in
                               let uu____26698 =
                                 FStar_TypeChecker_Env.set_expected_typ env1
                                   t3
                                  in
                               ((FStar_Pervasives_Native.Some t3), g,
                                 univ_vars1, univ_opening, uu____26698))))))

and (tc_binder :
  FStar_TypeChecker_Env.env ->
    (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.arg_qualifier
      FStar_Pervasives_Native.option) ->
      ((FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.arg_qualifier
        FStar_Pervasives_Native.option) * FStar_TypeChecker_Env.env *
        FStar_TypeChecker_Env.guard_t * FStar_Syntax_Syntax.universe))
  =
  fun env  ->
    fun uu____26704  ->
      match uu____26704 with
      | (x,imp) ->
          let uu____26731 = FStar_Syntax_Util.type_u ()  in
          (match uu____26731 with
           | (tu,u) ->
               ((let uu____26753 =
                   FStar_TypeChecker_Env.debug env FStar_Options.Extreme  in
                 if uu____26753
                 then
                   let uu____26756 = FStar_Syntax_Print.bv_to_string x  in
                   let uu____26758 =
                     FStar_Syntax_Print.term_to_string
                       x.FStar_Syntax_Syntax.sort
                      in
                   let uu____26760 = FStar_Syntax_Print.term_to_string tu  in
                   FStar_Util.print3 "Checking binder %s:%s at type %s\n"
                     uu____26756 uu____26758 uu____26760
                 else ());
                (let uu____26765 =
                   tc_check_tot_or_gtot_term env x.FStar_Syntax_Syntax.sort
                     tu
                    in
                 match uu____26765 with
                 | (t,uu____26787,g) ->
                     let uu____26789 =
                       match imp with
                       | FStar_Pervasives_Native.Some
                           (FStar_Syntax_Syntax.Meta tau) ->
                           let uu____26805 =
                             tc_tactic FStar_Syntax_Syntax.t_unit
                               FStar_Syntax_Syntax.t_unit env tau
                              in
                           (match uu____26805 with
                            | (tau1,uu____26819,g1) ->
                                ((FStar_Pervasives_Native.Some
                                    (FStar_Syntax_Syntax.Meta tau1)), g1))
                       | uu____26823 ->
                           (imp, FStar_TypeChecker_Env.trivial_guard)
                        in
                     (match uu____26789 with
                      | (imp1,g') ->
                          let x1 =
                            ((let uu___3469_26858 = x  in
                              {
                                FStar_Syntax_Syntax.ppname =
                                  (uu___3469_26858.FStar_Syntax_Syntax.ppname);
                                FStar_Syntax_Syntax.index =
                                  (uu___3469_26858.FStar_Syntax_Syntax.index);
                                FStar_Syntax_Syntax.sort = t
                              }), imp1)
                             in
                          ((let uu____26860 =
                              FStar_TypeChecker_Env.debug env
                                FStar_Options.High
                               in
                            if uu____26860
                            then
                              let uu____26863 =
                                FStar_Syntax_Print.bv_to_string
                                  (FStar_Pervasives_Native.fst x1)
                                 in
                              let uu____26867 =
                                FStar_Syntax_Print.term_to_string t  in
                              FStar_Util.print2
                                "Pushing binder %s at type %s\n" uu____26863
                                uu____26867
                            else ());
                           (let uu____26872 = push_binding env x1  in
                            (x1, uu____26872, g, u)))))))

and (tc_binders :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.binders ->
      (FStar_Syntax_Syntax.binders * FStar_TypeChecker_Env.env *
        FStar_TypeChecker_Common.guard_t * FStar_Syntax_Syntax.universes))
  =
  fun env  ->
    fun bs  ->
      (let uu____26884 =
         FStar_TypeChecker_Env.debug env FStar_Options.Extreme  in
       if uu____26884
       then
         let uu____26887 = FStar_Syntax_Print.binders_to_string ", " bs  in
         FStar_Util.print1 "Checking binders %s\n" uu____26887
       else ());
      (let rec aux env1 bs1 =
         match bs1 with
         | [] -> ([], env1, FStar_TypeChecker_Env.trivial_guard, [])
         | b::bs2 ->
             let uu____27000 = tc_binder env1 b  in
             (match uu____27000 with
              | (b1,env',g,u) ->
                  let uu____27049 = aux env' bs2  in
                  (match uu____27049 with
                   | (bs3,env'1,g',us) ->
                       let uu____27110 =
                         let uu____27111 =
                           FStar_TypeChecker_Env.close_guard_univs [u] 
                             [b1] g'
                            in
                         FStar_TypeChecker_Env.conj_guard g uu____27111  in
                       ((b1 :: bs3), env'1, uu____27110, (u :: us))))
          in
       aux env bs)

and (tc_smt_pats :
  FStar_TypeChecker_Env.env ->
    (FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax *
      FStar_Syntax_Syntax.arg_qualifier FStar_Pervasives_Native.option)
      Prims.list Prims.list ->
      ((FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax *
        FStar_Syntax_Syntax.arg_qualifier FStar_Pervasives_Native.option)
        Prims.list Prims.list * FStar_TypeChecker_Common.guard_t))
  =
  fun en  ->
    fun pats  ->
      let tc_args en1 args =
        FStar_List.fold_right
          (fun uu____27219  ->
             fun uu____27220  ->
               match (uu____27219, uu____27220) with
               | ((t,imp),(args1,g)) ->
                   (FStar_All.pipe_right t (check_no_smt_theory_symbols en1);
                    (let uu____27312 = tc_term en1 t  in
                     match uu____27312 with
                     | (t1,uu____27332,g') ->
                         let uu____27334 =
                           FStar_TypeChecker_Env.conj_guard g g'  in
                         (((t1, imp) :: args1), uu____27334)))) args
          ([], FStar_TypeChecker_Env.trivial_guard)
         in
      FStar_List.fold_right
        (fun p  ->
           fun uu____27388  ->
             match uu____27388 with
             | (pats1,g) ->
                 let uu____27415 = tc_args en p  in
                 (match uu____27415 with
                  | (args,g') ->
                      let uu____27428 = FStar_TypeChecker_Env.conj_guard g g'
                         in
                      ((args :: pats1), uu____27428))) pats
        ([], FStar_TypeChecker_Env.trivial_guard)

and (tc_tot_or_gtot_term :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term ->
      (FStar_Syntax_Syntax.term * FStar_TypeChecker_Common.lcomp *
        FStar_TypeChecker_Common.guard_t))
  =
  fun env  ->
    fun e  ->
      let uu____27441 = tc_maybe_toplevel_term env e  in
      match uu____27441 with
      | (e1,c,g) ->
          let uu____27457 = FStar_TypeChecker_Common.is_tot_or_gtot_lcomp c
             in
          if uu____27457
          then (e1, c, g)
          else
            (let g1 = FStar_TypeChecker_Rel.solve_deferred_constraints env g
                in
             let uu____27469 = FStar_TypeChecker_Common.lcomp_comp c  in
             match uu____27469 with
             | (c1,g_c) ->
                 let c2 = norm_c env c1  in
                 let uu____27483 =
                   let uu____27489 =
                     FStar_TypeChecker_Util.is_pure_effect env
                       (FStar_Syntax_Util.comp_effect_name c2)
                      in
                   if uu____27489
                   then
                     let uu____27497 =
                       FStar_Syntax_Syntax.mk_Total
                         (FStar_Syntax_Util.comp_result c2)
                        in
                     (uu____27497, false)
                   else
                     (let uu____27502 =
                        FStar_Syntax_Syntax.mk_GTotal
                          (FStar_Syntax_Util.comp_result c2)
                         in
                      (uu____27502, true))
                    in
                 (match uu____27483 with
                  | (target_comp,allow_ghost) ->
                      let uu____27515 =
                        FStar_TypeChecker_Rel.sub_comp env c2 target_comp  in
                      (match uu____27515 with
                       | FStar_Pervasives_Native.Some g' ->
                           let uu____27525 =
                             FStar_TypeChecker_Common.lcomp_of_comp
                               target_comp
                              in
                           let uu____27526 =
                             let uu____27527 =
                               FStar_TypeChecker_Env.conj_guard g_c g'  in
                             FStar_TypeChecker_Env.conj_guard g1 uu____27527
                              in
                           (e1, uu____27525, uu____27526)
                       | uu____27528 ->
                           if allow_ghost
                           then
                             let uu____27538 =
                               FStar_TypeChecker_Err.expected_ghost_expression
                                 e1 c2
                                in
                             FStar_Errors.raise_error uu____27538
                               e1.FStar_Syntax_Syntax.pos
                           else
                             (let uu____27552 =
                                FStar_TypeChecker_Err.expected_pure_expression
                                  e1 c2
                                 in
                              FStar_Errors.raise_error uu____27552
                                e1.FStar_Syntax_Syntax.pos))))

and (tc_check_tot_or_gtot_term :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term ->
      FStar_Syntax_Syntax.typ ->
        (FStar_Syntax_Syntax.term * FStar_TypeChecker_Common.lcomp *
          FStar_TypeChecker_Common.guard_t))
  =
  fun env  ->
    fun e  ->
      fun t  ->
        let env1 = FStar_TypeChecker_Env.set_expected_typ env t  in
        tc_tot_or_gtot_term env1 e

and (tc_trivial_guard :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term ->
      (FStar_Syntax_Syntax.term * FStar_TypeChecker_Common.lcomp))
  =
  fun env  ->
    fun t  ->
      let uu____27576 = tc_tot_or_gtot_term env t  in
      match uu____27576 with
      | (t1,c,g) ->
          (FStar_TypeChecker_Rel.force_trivial_guard env g; (t1, c))

let (tc_check_trivial_guard :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term ->
      FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term)
  =
  fun env  ->
    fun t  ->
      fun k  ->
        let uu____27607 = tc_check_tot_or_gtot_term env t k  in
        match uu____27607 with
        | (t1,uu____27615,g) ->
            (FStar_TypeChecker_Rel.force_trivial_guard env g; t1)
  
let (type_of_tot_term :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term ->
      (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.typ *
        FStar_TypeChecker_Common.guard_t))
  =
  fun env  ->
    fun e  ->
      (let uu____27636 =
         FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
           (FStar_Options.Other "RelCheck")
          in
       if uu____27636
       then
         let uu____27641 = FStar_Syntax_Print.term_to_string e  in
         FStar_Util.print1 "Checking term %s\n" uu____27641
       else ());
      (let env1 =
         let uu___3561_27647 = env  in
         {
           FStar_TypeChecker_Env.solver =
             (uu___3561_27647.FStar_TypeChecker_Env.solver);
           FStar_TypeChecker_Env.range =
             (uu___3561_27647.FStar_TypeChecker_Env.range);
           FStar_TypeChecker_Env.curmodule =
             (uu___3561_27647.FStar_TypeChecker_Env.curmodule);
           FStar_TypeChecker_Env.gamma =
             (uu___3561_27647.FStar_TypeChecker_Env.gamma);
           FStar_TypeChecker_Env.gamma_sig =
             (uu___3561_27647.FStar_TypeChecker_Env.gamma_sig);
           FStar_TypeChecker_Env.gamma_cache =
             (uu___3561_27647.FStar_TypeChecker_Env.gamma_cache);
           FStar_TypeChecker_Env.modules =
             (uu___3561_27647.FStar_TypeChecker_Env.modules);
           FStar_TypeChecker_Env.expected_typ =
             (uu___3561_27647.FStar_TypeChecker_Env.expected_typ);
           FStar_TypeChecker_Env.sigtab =
             (uu___3561_27647.FStar_TypeChecker_Env.sigtab);
           FStar_TypeChecker_Env.attrtab =
             (uu___3561_27647.FStar_TypeChecker_Env.attrtab);
           FStar_TypeChecker_Env.instantiate_imp =
             (uu___3561_27647.FStar_TypeChecker_Env.instantiate_imp);
           FStar_TypeChecker_Env.effects =
             (uu___3561_27647.FStar_TypeChecker_Env.effects);
           FStar_TypeChecker_Env.generalize =
             (uu___3561_27647.FStar_TypeChecker_Env.generalize);
           FStar_TypeChecker_Env.letrecs = [];
           FStar_TypeChecker_Env.top_level = false;
           FStar_TypeChecker_Env.check_uvars =
             (uu___3561_27647.FStar_TypeChecker_Env.check_uvars);
           FStar_TypeChecker_Env.use_eq =
             (uu___3561_27647.FStar_TypeChecker_Env.use_eq);
           FStar_TypeChecker_Env.is_iface =
             (uu___3561_27647.FStar_TypeChecker_Env.is_iface);
           FStar_TypeChecker_Env.admit =
             (uu___3561_27647.FStar_TypeChecker_Env.admit);
           FStar_TypeChecker_Env.lax =
             (uu___3561_27647.FStar_TypeChecker_Env.lax);
           FStar_TypeChecker_Env.lax_universes =
             (uu___3561_27647.FStar_TypeChecker_Env.lax_universes);
           FStar_TypeChecker_Env.phase1 =
             (uu___3561_27647.FStar_TypeChecker_Env.phase1);
           FStar_TypeChecker_Env.failhard =
             (uu___3561_27647.FStar_TypeChecker_Env.failhard);
           FStar_TypeChecker_Env.nosynth =
             (uu___3561_27647.FStar_TypeChecker_Env.nosynth);
           FStar_TypeChecker_Env.uvar_subtyping =
             (uu___3561_27647.FStar_TypeChecker_Env.uvar_subtyping);
           FStar_TypeChecker_Env.tc_term =
             (uu___3561_27647.FStar_TypeChecker_Env.tc_term);
           FStar_TypeChecker_Env.type_of =
             (uu___3561_27647.FStar_TypeChecker_Env.type_of);
           FStar_TypeChecker_Env.universe_of =
             (uu___3561_27647.FStar_TypeChecker_Env.universe_of);
           FStar_TypeChecker_Env.check_type_of =
             (uu___3561_27647.FStar_TypeChecker_Env.check_type_of);
           FStar_TypeChecker_Env.use_bv_sorts =
             (uu___3561_27647.FStar_TypeChecker_Env.use_bv_sorts);
           FStar_TypeChecker_Env.qtbl_name_and_index =
             (uu___3561_27647.FStar_TypeChecker_Env.qtbl_name_and_index);
           FStar_TypeChecker_Env.normalized_eff_names =
             (uu___3561_27647.FStar_TypeChecker_Env.normalized_eff_names);
           FStar_TypeChecker_Env.fv_delta_depths =
             (uu___3561_27647.FStar_TypeChecker_Env.fv_delta_depths);
           FStar_TypeChecker_Env.proof_ns =
             (uu___3561_27647.FStar_TypeChecker_Env.proof_ns);
           FStar_TypeChecker_Env.synth_hook =
             (uu___3561_27647.FStar_TypeChecker_Env.synth_hook);
           FStar_TypeChecker_Env.splice =
             (uu___3561_27647.FStar_TypeChecker_Env.splice);
           FStar_TypeChecker_Env.mpreprocess =
             (uu___3561_27647.FStar_TypeChecker_Env.mpreprocess);
           FStar_TypeChecker_Env.postprocess =
             (uu___3561_27647.FStar_TypeChecker_Env.postprocess);
           FStar_TypeChecker_Env.is_native_tactic =
             (uu___3561_27647.FStar_TypeChecker_Env.is_native_tactic);
           FStar_TypeChecker_Env.identifier_info =
             (uu___3561_27647.FStar_TypeChecker_Env.identifier_info);
           FStar_TypeChecker_Env.tc_hooks =
             (uu___3561_27647.FStar_TypeChecker_Env.tc_hooks);
           FStar_TypeChecker_Env.dsenv =
             (uu___3561_27647.FStar_TypeChecker_Env.dsenv);
           FStar_TypeChecker_Env.nbe =
             (uu___3561_27647.FStar_TypeChecker_Env.nbe);
           FStar_TypeChecker_Env.strict_args_tab =
             (uu___3561_27647.FStar_TypeChecker_Env.strict_args_tab);
           FStar_TypeChecker_Env.erasable_types_tab =
             (uu___3561_27647.FStar_TypeChecker_Env.erasable_types_tab)
         }  in
       let uu____27655 =
         try
           (fun uu___3565_27669  ->
              match () with | () -> tc_tot_or_gtot_term env1 e) ()
         with
         | FStar_Errors.Error (e1,msg,uu____27690) ->
             let uu____27693 = FStar_TypeChecker_Env.get_range env1  in
             FStar_Errors.raise_error (e1, msg) uu____27693
          in
       match uu____27655 with
       | (t,c,g) ->
           let c1 = FStar_TypeChecker_Normalize.ghost_to_pure_lcomp env1 c
              in
           let uu____27711 = FStar_TypeChecker_Common.is_total_lcomp c1  in
           if uu____27711
           then (t, (c1.FStar_TypeChecker_Common.res_typ), g)
           else
             (let uu____27722 =
                let uu____27728 =
                  let uu____27730 = FStar_Syntax_Print.term_to_string e  in
                  FStar_Util.format1
                    "Implicit argument: Expected a total term; got a ghost term: %s"
                    uu____27730
                   in
                (FStar_Errors.Fatal_UnexpectedImplictArgument, uu____27728)
                 in
              let uu____27734 = FStar_TypeChecker_Env.get_range env1  in
              FStar_Errors.raise_error uu____27722 uu____27734))
  
let level_of_type_fail :
  'Auu____27750 .
    FStar_TypeChecker_Env.env ->
      FStar_Syntax_Syntax.term -> Prims.string -> 'Auu____27750
  =
  fun env  ->
    fun e  ->
      fun t  ->
        let uu____27768 =
          let uu____27774 =
            let uu____27776 = FStar_Syntax_Print.term_to_string e  in
            FStar_Util.format2 "Expected a term of type 'Type'; got %s : %s"
              uu____27776 t
             in
          (FStar_Errors.Fatal_UnexpectedTermType, uu____27774)  in
        let uu____27780 = FStar_TypeChecker_Env.get_range env  in
        FStar_Errors.raise_error uu____27768 uu____27780
  
let (level_of_type :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term ->
      FStar_Syntax_Syntax.typ -> FStar_Syntax_Syntax.universe)
  =
  fun env  ->
    fun e  ->
      fun t  ->
        let rec aux retry t1 =
          let uu____27814 =
            let uu____27815 = FStar_Syntax_Util.unrefine t1  in
            uu____27815.FStar_Syntax_Syntax.n  in
          match uu____27814 with
          | FStar_Syntax_Syntax.Tm_type u -> u
          | uu____27819 ->
              if retry
              then
                let t2 =
                  FStar_TypeChecker_Normalize.normalize
                    [FStar_TypeChecker_Env.UnfoldUntil
                       FStar_Syntax_Syntax.delta_constant] env t1
                   in
                aux false t2
              else
                (let uu____27825 = FStar_Syntax_Util.type_u ()  in
                 match uu____27825 with
                 | (t_u,u) ->
                     let env1 =
                       let uu___3597_27833 = env  in
                       {
                         FStar_TypeChecker_Env.solver =
                           (uu___3597_27833.FStar_TypeChecker_Env.solver);
                         FStar_TypeChecker_Env.range =
                           (uu___3597_27833.FStar_TypeChecker_Env.range);
                         FStar_TypeChecker_Env.curmodule =
                           (uu___3597_27833.FStar_TypeChecker_Env.curmodule);
                         FStar_TypeChecker_Env.gamma =
                           (uu___3597_27833.FStar_TypeChecker_Env.gamma);
                         FStar_TypeChecker_Env.gamma_sig =
                           (uu___3597_27833.FStar_TypeChecker_Env.gamma_sig);
                         FStar_TypeChecker_Env.gamma_cache =
                           (uu___3597_27833.FStar_TypeChecker_Env.gamma_cache);
                         FStar_TypeChecker_Env.modules =
                           (uu___3597_27833.FStar_TypeChecker_Env.modules);
                         FStar_TypeChecker_Env.expected_typ =
                           (uu___3597_27833.FStar_TypeChecker_Env.expected_typ);
                         FStar_TypeChecker_Env.sigtab =
                           (uu___3597_27833.FStar_TypeChecker_Env.sigtab);
                         FStar_TypeChecker_Env.attrtab =
                           (uu___3597_27833.FStar_TypeChecker_Env.attrtab);
                         FStar_TypeChecker_Env.instantiate_imp =
                           (uu___3597_27833.FStar_TypeChecker_Env.instantiate_imp);
                         FStar_TypeChecker_Env.effects =
                           (uu___3597_27833.FStar_TypeChecker_Env.effects);
                         FStar_TypeChecker_Env.generalize =
                           (uu___3597_27833.FStar_TypeChecker_Env.generalize);
                         FStar_TypeChecker_Env.letrecs =
                           (uu___3597_27833.FStar_TypeChecker_Env.letrecs);
                         FStar_TypeChecker_Env.top_level =
                           (uu___3597_27833.FStar_TypeChecker_Env.top_level);
                         FStar_TypeChecker_Env.check_uvars =
                           (uu___3597_27833.FStar_TypeChecker_Env.check_uvars);
                         FStar_TypeChecker_Env.use_eq =
                           (uu___3597_27833.FStar_TypeChecker_Env.use_eq);
                         FStar_TypeChecker_Env.is_iface =
                           (uu___3597_27833.FStar_TypeChecker_Env.is_iface);
                         FStar_TypeChecker_Env.admit =
                           (uu___3597_27833.FStar_TypeChecker_Env.admit);
                         FStar_TypeChecker_Env.lax = true;
                         FStar_TypeChecker_Env.lax_universes =
                           (uu___3597_27833.FStar_TypeChecker_Env.lax_universes);
                         FStar_TypeChecker_Env.phase1 =
                           (uu___3597_27833.FStar_TypeChecker_Env.phase1);
                         FStar_TypeChecker_Env.failhard =
                           (uu___3597_27833.FStar_TypeChecker_Env.failhard);
                         FStar_TypeChecker_Env.nosynth =
                           (uu___3597_27833.FStar_TypeChecker_Env.nosynth);
                         FStar_TypeChecker_Env.uvar_subtyping =
                           (uu___3597_27833.FStar_TypeChecker_Env.uvar_subtyping);
                         FStar_TypeChecker_Env.tc_term =
                           (uu___3597_27833.FStar_TypeChecker_Env.tc_term);
                         FStar_TypeChecker_Env.type_of =
                           (uu___3597_27833.FStar_TypeChecker_Env.type_of);
                         FStar_TypeChecker_Env.universe_of =
                           (uu___3597_27833.FStar_TypeChecker_Env.universe_of);
                         FStar_TypeChecker_Env.check_type_of =
                           (uu___3597_27833.FStar_TypeChecker_Env.check_type_of);
                         FStar_TypeChecker_Env.use_bv_sorts =
                           (uu___3597_27833.FStar_TypeChecker_Env.use_bv_sorts);
                         FStar_TypeChecker_Env.qtbl_name_and_index =
                           (uu___3597_27833.FStar_TypeChecker_Env.qtbl_name_and_index);
                         FStar_TypeChecker_Env.normalized_eff_names =
                           (uu___3597_27833.FStar_TypeChecker_Env.normalized_eff_names);
                         FStar_TypeChecker_Env.fv_delta_depths =
                           (uu___3597_27833.FStar_TypeChecker_Env.fv_delta_depths);
                         FStar_TypeChecker_Env.proof_ns =
                           (uu___3597_27833.FStar_TypeChecker_Env.proof_ns);
                         FStar_TypeChecker_Env.synth_hook =
                           (uu___3597_27833.FStar_TypeChecker_Env.synth_hook);
                         FStar_TypeChecker_Env.splice =
                           (uu___3597_27833.FStar_TypeChecker_Env.splice);
                         FStar_TypeChecker_Env.mpreprocess =
                           (uu___3597_27833.FStar_TypeChecker_Env.mpreprocess);
                         FStar_TypeChecker_Env.postprocess =
                           (uu___3597_27833.FStar_TypeChecker_Env.postprocess);
                         FStar_TypeChecker_Env.is_native_tactic =
                           (uu___3597_27833.FStar_TypeChecker_Env.is_native_tactic);
                         FStar_TypeChecker_Env.identifier_info =
                           (uu___3597_27833.FStar_TypeChecker_Env.identifier_info);
                         FStar_TypeChecker_Env.tc_hooks =
                           (uu___3597_27833.FStar_TypeChecker_Env.tc_hooks);
                         FStar_TypeChecker_Env.dsenv =
                           (uu___3597_27833.FStar_TypeChecker_Env.dsenv);
                         FStar_TypeChecker_Env.nbe =
                           (uu___3597_27833.FStar_TypeChecker_Env.nbe);
                         FStar_TypeChecker_Env.strict_args_tab =
                           (uu___3597_27833.FStar_TypeChecker_Env.strict_args_tab);
                         FStar_TypeChecker_Env.erasable_types_tab =
                           (uu___3597_27833.FStar_TypeChecker_Env.erasable_types_tab)
                       }  in
                     let g = FStar_TypeChecker_Rel.teq env1 t1 t_u  in
                     ((match g.FStar_TypeChecker_Common.guard_f with
                       | FStar_TypeChecker_Common.NonTrivial f ->
                           let uu____27838 =
                             FStar_Syntax_Print.term_to_string t1  in
                           level_of_type_fail env1 e uu____27838
                       | uu____27840 ->
                           FStar_TypeChecker_Rel.force_trivial_guard env1 g);
                      u))
           in
        aux true t
  
let rec (universe_of_aux :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
      FStar_Syntax_Syntax.typ)
  =
  fun env  ->
    fun e  ->
      let uu____27857 =
        let uu____27858 = FStar_Syntax_Subst.compress e  in
        uu____27858.FStar_Syntax_Syntax.n  in
      match uu____27857 with
      | FStar_Syntax_Syntax.Tm_bvar uu____27861 -> failwith "Impossible"
      | FStar_Syntax_Syntax.Tm_unknown  -> failwith "Impossible"
      | FStar_Syntax_Syntax.Tm_delayed uu____27864 -> failwith "Impossible"
      | FStar_Syntax_Syntax.Tm_let uu____27888 ->
          let e1 = FStar_TypeChecker_Normalize.normalize [] env e  in
          universe_of_aux env e1
      | FStar_Syntax_Syntax.Tm_abs (bs,t,uu____27905) ->
          level_of_type_fail env e "arrow type"
      | FStar_Syntax_Syntax.Tm_uvar (u,s) ->
          FStar_Syntax_Subst.subst' s u.FStar_Syntax_Syntax.ctx_uvar_typ
      | FStar_Syntax_Syntax.Tm_meta (t,uu____27950) -> universe_of_aux env t
      | FStar_Syntax_Syntax.Tm_name n1 -> n1.FStar_Syntax_Syntax.sort
      | FStar_Syntax_Syntax.Tm_fvar fv ->
          let uu____27957 =
            FStar_TypeChecker_Env.lookup_lid env
              (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
             in
          (match uu____27957 with | ((uu____27966,t),uu____27968) -> t)
      | FStar_Syntax_Syntax.Tm_lazy i ->
          let uu____27974 = FStar_Syntax_Util.unfold_lazy i  in
          universe_of_aux env uu____27974
      | FStar_Syntax_Syntax.Tm_ascribed
          (uu____27977,(FStar_Util.Inl t,uu____27979),uu____27980) -> t
      | FStar_Syntax_Syntax.Tm_ascribed
          (uu____28027,(FStar_Util.Inr c,uu____28029),uu____28030) ->
          FStar_Syntax_Util.comp_result c
      | FStar_Syntax_Syntax.Tm_type u ->
          FStar_Syntax_Syntax.mk
            (FStar_Syntax_Syntax.Tm_type (FStar_Syntax_Syntax.U_succ u))
            FStar_Pervasives_Native.None e.FStar_Syntax_Syntax.pos
      | FStar_Syntax_Syntax.Tm_quoted uu____28078 -> FStar_Syntax_Util.ktype0
      | FStar_Syntax_Syntax.Tm_constant sc ->
          tc_constant env e.FStar_Syntax_Syntax.pos sc
      | FStar_Syntax_Syntax.Tm_uinst
          ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar fv;
             FStar_Syntax_Syntax.pos = uu____28087;
             FStar_Syntax_Syntax.vars = uu____28088;_},us)
          ->
          let uu____28094 =
            FStar_TypeChecker_Env.lookup_lid env
              (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
             in
          (match uu____28094 with
           | ((us',t),uu____28105) ->
               (if (FStar_List.length us) <> (FStar_List.length us')
                then
                  (let uu____28112 = FStar_TypeChecker_Env.get_range env  in
                   FStar_Errors.raise_error
                     (FStar_Errors.Fatal_UnexpectedNumberOfUniverse,
                       "Unexpected number of universe instantiations")
                     uu____28112)
                else
                  FStar_List.iter2
                    (fun u'  ->
                       fun u  ->
                         match u' with
                         | FStar_Syntax_Syntax.U_unif u'' ->
                             FStar_Syntax_Unionfind.univ_change u'' u
                         | uu____28131 -> failwith "Impossible") us' us;
                t))
      | FStar_Syntax_Syntax.Tm_uinst uu____28133 ->
          failwith "Impossible: Tm_uinst's head must be an fvar"
      | FStar_Syntax_Syntax.Tm_refine (x,uu____28142) ->
          universe_of_aux env x.FStar_Syntax_Syntax.sort
      | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
          let uu____28169 = FStar_Syntax_Subst.open_comp bs c  in
          (match uu____28169 with
           | (bs1,c1) ->
               let us =
                 FStar_List.map
                   (fun uu____28189  ->
                      match uu____28189 with
                      | (b,uu____28197) ->
                          let uu____28202 =
                            universe_of_aux env b.FStar_Syntax_Syntax.sort
                             in
                          level_of_type env b.FStar_Syntax_Syntax.sort
                            uu____28202) bs1
                  in
               let u_res =
                 let res = FStar_Syntax_Util.comp_result c1  in
                 let uu____28207 = universe_of_aux env res  in
                 level_of_type env res uu____28207  in
               let u_c =
                 FStar_All.pipe_right c1
                   (FStar_TypeChecker_Util.universe_of_comp env u_res)
                  in
               let u =
                 FStar_TypeChecker_Normalize.normalize_universe env
                   (FStar_Syntax_Syntax.U_max (u_c :: us))
                  in
               FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_type u)
                 FStar_Pervasives_Native.None e.FStar_Syntax_Syntax.pos)
      | FStar_Syntax_Syntax.Tm_app (hd1,args) ->
          let rec type_of_head retry hd2 args1 =
            let hd3 = FStar_Syntax_Subst.compress hd2  in
            match hd3.FStar_Syntax_Syntax.n with
            | FStar_Syntax_Syntax.Tm_unknown  -> failwith "Impossible"
            | FStar_Syntax_Syntax.Tm_bvar uu____28318 ->
                failwith "Impossible"
            | FStar_Syntax_Syntax.Tm_delayed uu____28334 ->
                failwith "Impossible"
            | FStar_Syntax_Syntax.Tm_fvar uu____28372 ->
                let uu____28373 = universe_of_aux env hd3  in
                (uu____28373, args1)
            | FStar_Syntax_Syntax.Tm_name uu____28384 ->
                let uu____28385 = universe_of_aux env hd3  in
                (uu____28385, args1)
            | FStar_Syntax_Syntax.Tm_uvar uu____28396 ->
                let uu____28409 = universe_of_aux env hd3  in
                (uu____28409, args1)
            | FStar_Syntax_Syntax.Tm_uinst uu____28420 ->
                let uu____28427 = universe_of_aux env hd3  in
                (uu____28427, args1)
            | FStar_Syntax_Syntax.Tm_ascribed uu____28438 ->
                let uu____28465 = universe_of_aux env hd3  in
                (uu____28465, args1)
            | FStar_Syntax_Syntax.Tm_refine uu____28476 ->
                let uu____28483 = universe_of_aux env hd3  in
                (uu____28483, args1)
            | FStar_Syntax_Syntax.Tm_constant uu____28494 ->
                let uu____28495 = universe_of_aux env hd3  in
                (uu____28495, args1)
            | FStar_Syntax_Syntax.Tm_arrow uu____28506 ->
                let uu____28521 = universe_of_aux env hd3  in
                (uu____28521, args1)
            | FStar_Syntax_Syntax.Tm_meta uu____28532 ->
                let uu____28539 = universe_of_aux env hd3  in
                (uu____28539, args1)
            | FStar_Syntax_Syntax.Tm_type uu____28550 ->
                let uu____28551 = universe_of_aux env hd3  in
                (uu____28551, args1)
            | FStar_Syntax_Syntax.Tm_match (uu____28562,hd4::uu____28564) ->
                let uu____28629 = FStar_Syntax_Subst.open_branch hd4  in
                (match uu____28629 with
                 | (uu____28644,uu____28645,hd5) ->
                     let uu____28663 = FStar_Syntax_Util.head_and_args hd5
                        in
                     (match uu____28663 with
                      | (hd6,args2) -> type_of_head retry hd6 args2))
            | uu____28720 when retry ->
                let e1 =
                  FStar_TypeChecker_Normalize.normalize
                    [FStar_TypeChecker_Env.Beta;
                    FStar_TypeChecker_Env.DoNotUnfoldPureLets] env e
                   in
                let uu____28722 = FStar_Syntax_Util.head_and_args e1  in
                (match uu____28722 with
                 | (hd4,args2) -> type_of_head false hd4 args2)
            | uu____28780 ->
                let uu____28781 =
                  FStar_TypeChecker_Env.clear_expected_typ env  in
                (match uu____28781 with
                 | (env1,uu____28803) ->
                     let env2 =
                       let uu___3758_28809 = env1  in
                       {
                         FStar_TypeChecker_Env.solver =
                           (uu___3758_28809.FStar_TypeChecker_Env.solver);
                         FStar_TypeChecker_Env.range =
                           (uu___3758_28809.FStar_TypeChecker_Env.range);
                         FStar_TypeChecker_Env.curmodule =
                           (uu___3758_28809.FStar_TypeChecker_Env.curmodule);
                         FStar_TypeChecker_Env.gamma =
                           (uu___3758_28809.FStar_TypeChecker_Env.gamma);
                         FStar_TypeChecker_Env.gamma_sig =
                           (uu___3758_28809.FStar_TypeChecker_Env.gamma_sig);
                         FStar_TypeChecker_Env.gamma_cache =
                           (uu___3758_28809.FStar_TypeChecker_Env.gamma_cache);
                         FStar_TypeChecker_Env.modules =
                           (uu___3758_28809.FStar_TypeChecker_Env.modules);
                         FStar_TypeChecker_Env.expected_typ =
                           (uu___3758_28809.FStar_TypeChecker_Env.expected_typ);
                         FStar_TypeChecker_Env.sigtab =
                           (uu___3758_28809.FStar_TypeChecker_Env.sigtab);
                         FStar_TypeChecker_Env.attrtab =
                           (uu___3758_28809.FStar_TypeChecker_Env.attrtab);
                         FStar_TypeChecker_Env.instantiate_imp =
                           (uu___3758_28809.FStar_TypeChecker_Env.instantiate_imp);
                         FStar_TypeChecker_Env.effects =
                           (uu___3758_28809.FStar_TypeChecker_Env.effects);
                         FStar_TypeChecker_Env.generalize =
                           (uu___3758_28809.FStar_TypeChecker_Env.generalize);
                         FStar_TypeChecker_Env.letrecs =
                           (uu___3758_28809.FStar_TypeChecker_Env.letrecs);
                         FStar_TypeChecker_Env.top_level = false;
                         FStar_TypeChecker_Env.check_uvars =
                           (uu___3758_28809.FStar_TypeChecker_Env.check_uvars);
                         FStar_TypeChecker_Env.use_eq =
                           (uu___3758_28809.FStar_TypeChecker_Env.use_eq);
                         FStar_TypeChecker_Env.is_iface =
                           (uu___3758_28809.FStar_TypeChecker_Env.is_iface);
                         FStar_TypeChecker_Env.admit =
                           (uu___3758_28809.FStar_TypeChecker_Env.admit);
                         FStar_TypeChecker_Env.lax = true;
                         FStar_TypeChecker_Env.lax_universes =
                           (uu___3758_28809.FStar_TypeChecker_Env.lax_universes);
                         FStar_TypeChecker_Env.phase1 =
                           (uu___3758_28809.FStar_TypeChecker_Env.phase1);
                         FStar_TypeChecker_Env.failhard =
                           (uu___3758_28809.FStar_TypeChecker_Env.failhard);
                         FStar_TypeChecker_Env.nosynth =
                           (uu___3758_28809.FStar_TypeChecker_Env.nosynth);
                         FStar_TypeChecker_Env.uvar_subtyping =
                           (uu___3758_28809.FStar_TypeChecker_Env.uvar_subtyping);
                         FStar_TypeChecker_Env.tc_term =
                           (uu___3758_28809.FStar_TypeChecker_Env.tc_term);
                         FStar_TypeChecker_Env.type_of =
                           (uu___3758_28809.FStar_TypeChecker_Env.type_of);
                         FStar_TypeChecker_Env.universe_of =
                           (uu___3758_28809.FStar_TypeChecker_Env.universe_of);
                         FStar_TypeChecker_Env.check_type_of =
                           (uu___3758_28809.FStar_TypeChecker_Env.check_type_of);
                         FStar_TypeChecker_Env.use_bv_sorts = true;
                         FStar_TypeChecker_Env.qtbl_name_and_index =
                           (uu___3758_28809.FStar_TypeChecker_Env.qtbl_name_and_index);
                         FStar_TypeChecker_Env.normalized_eff_names =
                           (uu___3758_28809.FStar_TypeChecker_Env.normalized_eff_names);
                         FStar_TypeChecker_Env.fv_delta_depths =
                           (uu___3758_28809.FStar_TypeChecker_Env.fv_delta_depths);
                         FStar_TypeChecker_Env.proof_ns =
                           (uu___3758_28809.FStar_TypeChecker_Env.proof_ns);
                         FStar_TypeChecker_Env.synth_hook =
                           (uu___3758_28809.FStar_TypeChecker_Env.synth_hook);
                         FStar_TypeChecker_Env.splice =
                           (uu___3758_28809.FStar_TypeChecker_Env.splice);
                         FStar_TypeChecker_Env.mpreprocess =
                           (uu___3758_28809.FStar_TypeChecker_Env.mpreprocess);
                         FStar_TypeChecker_Env.postprocess =
                           (uu___3758_28809.FStar_TypeChecker_Env.postprocess);
                         FStar_TypeChecker_Env.is_native_tactic =
                           (uu___3758_28809.FStar_TypeChecker_Env.is_native_tactic);
                         FStar_TypeChecker_Env.identifier_info =
                           (uu___3758_28809.FStar_TypeChecker_Env.identifier_info);
                         FStar_TypeChecker_Env.tc_hooks =
                           (uu___3758_28809.FStar_TypeChecker_Env.tc_hooks);
                         FStar_TypeChecker_Env.dsenv =
                           (uu___3758_28809.FStar_TypeChecker_Env.dsenv);
                         FStar_TypeChecker_Env.nbe =
                           (uu___3758_28809.FStar_TypeChecker_Env.nbe);
                         FStar_TypeChecker_Env.strict_args_tab =
                           (uu___3758_28809.FStar_TypeChecker_Env.strict_args_tab);
                         FStar_TypeChecker_Env.erasable_types_tab =
                           (uu___3758_28809.FStar_TypeChecker_Env.erasable_types_tab)
                       }  in
                     ((let uu____28814 =
                         FStar_All.pipe_left
                           (FStar_TypeChecker_Env.debug env2)
                           (FStar_Options.Other "UniverseOf")
                          in
                       if uu____28814
                       then
                         let uu____28819 =
                           let uu____28821 =
                             FStar_TypeChecker_Env.get_range env2  in
                           FStar_Range.string_of_range uu____28821  in
                         let uu____28822 =
                           FStar_Syntax_Print.term_to_string hd3  in
                         FStar_Util.print2 "%s: About to type-check %s\n"
                           uu____28819 uu____28822
                       else ());
                      (let uu____28827 = tc_term env2 hd3  in
                       match uu____28827 with
                       | (uu____28848,{
                                        FStar_TypeChecker_Common.eff_name =
                                          uu____28849;
                                        FStar_TypeChecker_Common.res_typ = t;
                                        FStar_TypeChecker_Common.cflags =
                                          uu____28851;
                                        FStar_TypeChecker_Common.comp_thunk =
                                          uu____28852;_},g)
                           ->
                           ((let uu____28870 =
                               FStar_TypeChecker_Rel.solve_deferred_constraints
                                 env2 g
                                in
                             FStar_All.pipe_right uu____28870 (fun a1  -> ()));
                            (t, args1)))))
             in
          let uu____28881 = type_of_head true hd1 args  in
          (match uu____28881 with
           | (t,args1) ->
               let t1 =
                 FStar_TypeChecker_Normalize.normalize
                   [FStar_TypeChecker_Env.UnfoldUntil
                      FStar_Syntax_Syntax.delta_constant] env t
                  in
               let uu____28920 = FStar_Syntax_Util.arrow_formals_comp t1  in
               (match uu____28920 with
                | (bs,res) ->
                    let res1 = FStar_Syntax_Util.comp_result res  in
                    if (FStar_List.length bs) = (FStar_List.length args1)
                    then
                      let subst1 = FStar_Syntax_Util.subst_of_list bs args1
                         in
                      FStar_Syntax_Subst.subst subst1 res1
                    else
                      (let uu____28972 =
                         FStar_Syntax_Print.term_to_string res1  in
                       level_of_type_fail env e uu____28972)))
      | FStar_Syntax_Syntax.Tm_match (uu____28974,hd1::uu____28976) ->
          let uu____29041 = FStar_Syntax_Subst.open_branch hd1  in
          (match uu____29041 with
           | (uu____29042,uu____29043,hd2) -> universe_of_aux env hd2)
      | FStar_Syntax_Syntax.Tm_match (uu____29061,[]) ->
          level_of_type_fail env e "empty match cases"
  
let (universe_of :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.universe)
  =
  fun env  ->
    fun e  ->
      let uu____29108 = universe_of_aux env e  in
      level_of_type env e uu____29108
  
let (tc_tparams :
  FStar_TypeChecker_Env.env_t ->
    FStar_Syntax_Syntax.binders ->
      (FStar_Syntax_Syntax.binders * FStar_TypeChecker_Env.env *
        FStar_Syntax_Syntax.universes))
  =
  fun env0  ->
    fun tps  ->
      let uu____29132 = tc_binders env0 tps  in
      match uu____29132 with
      | (tps1,env,g,us) ->
          (FStar_TypeChecker_Rel.force_trivial_guard env0 g; (tps1, env, us))
  
let rec (type_of_well_typed_term :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term ->
      FStar_Syntax_Syntax.typ FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun t  ->
      let mk_tm_type u =
        FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_type u)
          FStar_Pervasives_Native.None t.FStar_Syntax_Syntax.pos
         in
      let t1 = FStar_Syntax_Subst.compress t  in
      match t1.FStar_Syntax_Syntax.n with
      | FStar_Syntax_Syntax.Tm_delayed uu____29190 -> failwith "Impossible"
      | FStar_Syntax_Syntax.Tm_bvar uu____29216 -> failwith "Impossible"
      | FStar_Syntax_Syntax.Tm_name x ->
          FStar_Pervasives_Native.Some (x.FStar_Syntax_Syntax.sort)
      | FStar_Syntax_Syntax.Tm_lazy i ->
          let uu____29222 = FStar_Syntax_Util.unfold_lazy i  in
          type_of_well_typed_term env uu____29222
      | FStar_Syntax_Syntax.Tm_fvar fv ->
          let uu____29224 =
            FStar_TypeChecker_Env.try_lookup_and_inst_lid env []
              (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
             in
          FStar_Util.bind_opt uu____29224
            (fun uu____29238  ->
               match uu____29238 with
               | (t2,uu____29246) -> FStar_Pervasives_Native.Some t2)
      | FStar_Syntax_Syntax.Tm_uinst
          ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar fv;
             FStar_Syntax_Syntax.pos = uu____29248;
             FStar_Syntax_Syntax.vars = uu____29249;_},us)
          ->
          let uu____29255 =
            FStar_TypeChecker_Env.try_lookup_and_inst_lid env us
              (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
             in
          FStar_Util.bind_opt uu____29255
            (fun uu____29269  ->
               match uu____29269 with
               | (t2,uu____29277) -> FStar_Pervasives_Native.Some t2)
      | FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_reify ) ->
          FStar_Pervasives_Native.None
      | FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_reflect
          uu____29278) -> FStar_Pervasives_Native.None
      | FStar_Syntax_Syntax.Tm_constant sc ->
          let uu____29280 = tc_constant env t1.FStar_Syntax_Syntax.pos sc  in
          FStar_Pervasives_Native.Some uu____29280
      | FStar_Syntax_Syntax.Tm_type u ->
          let uu____29282 = mk_tm_type (FStar_Syntax_Syntax.U_succ u)  in
          FStar_Pervasives_Native.Some uu____29282
      | FStar_Syntax_Syntax.Tm_abs
          (bs,body,FStar_Pervasives_Native.Some
           { FStar_Syntax_Syntax.residual_effect = eff;
             FStar_Syntax_Syntax.residual_typ = FStar_Pervasives_Native.Some
               tbody;
             FStar_Syntax_Syntax.residual_flags = uu____29287;_})
          ->
          let mk_comp =
            let uu____29331 =
              FStar_Ident.lid_equals eff FStar_Parser_Const.effect_Tot_lid
               in
            if uu____29331
            then FStar_Pervasives_Native.Some FStar_Syntax_Syntax.mk_Total'
            else
              (let uu____29362 =
                 FStar_Ident.lid_equals eff
                   FStar_Parser_Const.effect_GTot_lid
                  in
               if uu____29362
               then
                 FStar_Pervasives_Native.Some FStar_Syntax_Syntax.mk_GTotal'
               else FStar_Pervasives_Native.None)
             in
          FStar_Util.bind_opt mk_comp
            (fun f  ->
               let uu____29432 = universe_of_well_typed_term env tbody  in
               FStar_Util.bind_opt uu____29432
                 (fun u  ->
                    let uu____29440 =
                      let uu____29443 =
                        let uu____29450 =
                          let uu____29451 =
                            let uu____29466 =
                              f tbody (FStar_Pervasives_Native.Some u)  in
                            (bs, uu____29466)  in
                          FStar_Syntax_Syntax.Tm_arrow uu____29451  in
                        FStar_Syntax_Syntax.mk uu____29450  in
                      uu____29443 FStar_Pervasives_Native.None
                        t1.FStar_Syntax_Syntax.pos
                       in
                    FStar_Pervasives_Native.Some uu____29440))
      | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
          let uu____29503 = FStar_Syntax_Subst.open_comp bs c  in
          (match uu____29503 with
           | (bs1,c1) ->
               let rec aux env1 us bs2 =
                 match bs2 with
                 | [] ->
                     let uu____29562 =
                       universe_of_well_typed_term env1
                         (FStar_Syntax_Util.comp_result c1)
                        in
                     FStar_Util.bind_opt uu____29562
                       (fun uc  ->
                          let uu____29570 =
                            mk_tm_type (FStar_Syntax_Syntax.U_max (uc :: us))
                             in
                          FStar_Pervasives_Native.Some uu____29570)
                 | (x,imp)::bs3 ->
                     let uu____29596 =
                       universe_of_well_typed_term env1
                         x.FStar_Syntax_Syntax.sort
                        in
                     FStar_Util.bind_opt uu____29596
                       (fun u_x  ->
                          let env2 = FStar_TypeChecker_Env.push_bv env1 x  in
                          aux env2 (u_x :: us) bs3)
                  in
               aux env [] bs1)
      | FStar_Syntax_Syntax.Tm_abs uu____29605 ->
          FStar_Pervasives_Native.None
      | FStar_Syntax_Syntax.Tm_refine (x,uu____29625) ->
          let uu____29630 =
            universe_of_well_typed_term env x.FStar_Syntax_Syntax.sort  in
          FStar_Util.bind_opt uu____29630
            (fun u_x  ->
               let uu____29638 = mk_tm_type u_x  in
               FStar_Pervasives_Native.Some uu____29638)
      | FStar_Syntax_Syntax.Tm_app
          ({
             FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant
               (FStar_Const.Const_range_of );
             FStar_Syntax_Syntax.pos = uu____29643;
             FStar_Syntax_Syntax.vars = uu____29644;_},a::hd1::rest)
          ->
          let rest1 = hd1 :: rest  in
          let uu____29723 = FStar_Syntax_Util.head_and_args t1  in
          (match uu____29723 with
           | (unary_op1,uu____29743) ->
               let head1 =
                 let uu____29771 =
                   FStar_Range.union_ranges unary_op1.FStar_Syntax_Syntax.pos
                     (FStar_Pervasives_Native.fst a).FStar_Syntax_Syntax.pos
                    in
                 FStar_Syntax_Syntax.mk
                   (FStar_Syntax_Syntax.Tm_app (unary_op1, [a]))
                   FStar_Pervasives_Native.None uu____29771
                  in
               let t2 =
                 FStar_Syntax_Syntax.mk
                   (FStar_Syntax_Syntax.Tm_app (head1, rest1))
                   FStar_Pervasives_Native.None t1.FStar_Syntax_Syntax.pos
                  in
               type_of_well_typed_term env t2)
      | FStar_Syntax_Syntax.Tm_app
          ({
             FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant
               (FStar_Const.Const_set_range_of );
             FStar_Syntax_Syntax.pos = uu____29819;
             FStar_Syntax_Syntax.vars = uu____29820;_},a1::a2::hd1::rest)
          ->
          let rest1 = hd1 :: rest  in
          let uu____29916 = FStar_Syntax_Util.head_and_args t1  in
          (match uu____29916 with
           | (unary_op1,uu____29936) ->
               let head1 =
                 let uu____29964 =
                   FStar_Range.union_ranges unary_op1.FStar_Syntax_Syntax.pos
                     (FStar_Pervasives_Native.fst a1).FStar_Syntax_Syntax.pos
                    in
                 FStar_Syntax_Syntax.mk
                   (FStar_Syntax_Syntax.Tm_app (unary_op1, [a1; a2]))
                   FStar_Pervasives_Native.None uu____29964
                  in
               let t2 =
                 FStar_Syntax_Syntax.mk
                   (FStar_Syntax_Syntax.Tm_app (head1, rest1))
                   FStar_Pervasives_Native.None t1.FStar_Syntax_Syntax.pos
                  in
               type_of_well_typed_term env t2)
      | FStar_Syntax_Syntax.Tm_app
          ({
             FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant
               (FStar_Const.Const_range_of );
             FStar_Syntax_Syntax.pos = uu____30020;
             FStar_Syntax_Syntax.vars = uu____30021;_},uu____30022::[])
          -> FStar_Pervasives_Native.Some FStar_Syntax_Syntax.t_range
      | FStar_Syntax_Syntax.Tm_app
          ({
             FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant
               (FStar_Const.Const_set_range_of );
             FStar_Syntax_Syntax.pos = uu____30061;
             FStar_Syntax_Syntax.vars = uu____30062;_},(t2,uu____30064)::uu____30065::[])
          -> type_of_well_typed_term env t2
      | FStar_Syntax_Syntax.Tm_app (hd1,args) ->
          let t_hd = type_of_well_typed_term env hd1  in
          let rec aux t_hd1 =
            let uu____30161 =
              let uu____30162 =
                FStar_TypeChecker_Normalize.unfold_whnf env t_hd1  in
              uu____30162.FStar_Syntax_Syntax.n  in
            match uu____30161 with
            | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
                let n_args = FStar_List.length args  in
                let n_bs = FStar_List.length bs  in
                let bs_t_opt =
                  if n_args < n_bs
                  then
                    let uu____30235 = FStar_Util.first_N n_args bs  in
                    match uu____30235 with
                    | (bs1,rest) ->
                        let t2 =
                          FStar_Syntax_Syntax.mk
                            (FStar_Syntax_Syntax.Tm_arrow (rest, c))
                            FStar_Pervasives_Native.None
                            t_hd1.FStar_Syntax_Syntax.pos
                           in
                        let uu____30323 =
                          let uu____30328 = FStar_Syntax_Syntax.mk_Total t2
                             in
                          FStar_Syntax_Subst.open_comp bs1 uu____30328  in
                        (match uu____30323 with
                         | (bs2,c1) ->
                             FStar_Pervasives_Native.Some
                               (bs2, (FStar_Syntax_Util.comp_result c1)))
                  else
                    if n_args = n_bs
                    then
                      (let uu____30382 = FStar_Syntax_Subst.open_comp bs c
                          in
                       match uu____30382 with
                       | (bs1,c1) ->
                           let uu____30403 =
                             FStar_Syntax_Util.is_tot_or_gtot_comp c1  in
                           if uu____30403
                           then
                             FStar_Pervasives_Native.Some
                               (bs1, (FStar_Syntax_Util.comp_result c1))
                           else FStar_Pervasives_Native.None)
                    else FStar_Pervasives_Native.None
                   in
                FStar_Util.bind_opt bs_t_opt
                  (fun uu____30485  ->
                     match uu____30485 with
                     | (bs1,t2) ->
                         let subst1 =
                           FStar_List.map2
                             (fun b  ->
                                fun a  ->
                                  FStar_Syntax_Syntax.NT
                                    ((FStar_Pervasives_Native.fst b),
                                      (FStar_Pervasives_Native.fst a))) bs1
                             args
                            in
                         let uu____30561 = FStar_Syntax_Subst.subst subst1 t2
                            in
                         FStar_Pervasives_Native.Some uu____30561)
            | FStar_Syntax_Syntax.Tm_refine (x,uu____30563) ->
                aux x.FStar_Syntax_Syntax.sort
            | FStar_Syntax_Syntax.Tm_ascribed (t2,uu____30569,uu____30570) ->
                aux t2
            | uu____30611 -> FStar_Pervasives_Native.None  in
          FStar_Util.bind_opt t_hd aux
      | FStar_Syntax_Syntax.Tm_ascribed
          (uu____30612,(FStar_Util.Inl t2,uu____30614),uu____30615) ->
          FStar_Pervasives_Native.Some t2
      | FStar_Syntax_Syntax.Tm_ascribed
          (uu____30662,(FStar_Util.Inr c,uu____30664),uu____30665) ->
          FStar_Pervasives_Native.Some (FStar_Syntax_Util.comp_result c)
      | FStar_Syntax_Syntax.Tm_uvar (u,s) ->
          let uu____30730 =
            FStar_Syntax_Subst.subst' s u.FStar_Syntax_Syntax.ctx_uvar_typ
             in
          FStar_Pervasives_Native.Some uu____30730
      | FStar_Syntax_Syntax.Tm_quoted (tm,qi) ->
          FStar_Pervasives_Native.Some FStar_Syntax_Syntax.t_term
      | FStar_Syntax_Syntax.Tm_meta (t2,uu____30738) ->
          type_of_well_typed_term env t2
      | FStar_Syntax_Syntax.Tm_match uu____30743 ->
          FStar_Pervasives_Native.None
      | FStar_Syntax_Syntax.Tm_let uu____30766 ->
          FStar_Pervasives_Native.None
      | FStar_Syntax_Syntax.Tm_unknown  -> FStar_Pervasives_Native.None
      | FStar_Syntax_Syntax.Tm_uinst uu____30780 ->
          FStar_Pervasives_Native.None

and (universe_of_well_typed_term :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
      FStar_Syntax_Syntax.universe FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun t  ->
      let uu____30791 = type_of_well_typed_term env t  in
      match uu____30791 with
      | FStar_Pervasives_Native.Some
          { FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_type u;
            FStar_Syntax_Syntax.pos = uu____30797;
            FStar_Syntax_Syntax.vars = uu____30798;_}
          -> FStar_Pervasives_Native.Some u
      | uu____30801 -> FStar_Pervasives_Native.None

let (check_type_of_well_typed_term' :
  Prims.bool ->
    FStar_TypeChecker_Env.env ->
      FStar_Syntax_Syntax.term ->
        FStar_Syntax_Syntax.typ -> FStar_TypeChecker_Common.guard_t)
  =
  fun must_total  ->
    fun env  ->
      fun t  ->
        fun k  ->
          let env1 = FStar_TypeChecker_Env.set_expected_typ env k  in
          let env2 =
            let uu___4037_30829 = env1  in
            {
              FStar_TypeChecker_Env.solver =
                (uu___4037_30829.FStar_TypeChecker_Env.solver);
              FStar_TypeChecker_Env.range =
                (uu___4037_30829.FStar_TypeChecker_Env.range);
              FStar_TypeChecker_Env.curmodule =
                (uu___4037_30829.FStar_TypeChecker_Env.curmodule);
              FStar_TypeChecker_Env.gamma =
                (uu___4037_30829.FStar_TypeChecker_Env.gamma);
              FStar_TypeChecker_Env.gamma_sig =
                (uu___4037_30829.FStar_TypeChecker_Env.gamma_sig);
              FStar_TypeChecker_Env.gamma_cache =
                (uu___4037_30829.FStar_TypeChecker_Env.gamma_cache);
              FStar_TypeChecker_Env.modules =
                (uu___4037_30829.FStar_TypeChecker_Env.modules);
              FStar_TypeChecker_Env.expected_typ =
                (uu___4037_30829.FStar_TypeChecker_Env.expected_typ);
              FStar_TypeChecker_Env.sigtab =
                (uu___4037_30829.FStar_TypeChecker_Env.sigtab);
              FStar_TypeChecker_Env.attrtab =
                (uu___4037_30829.FStar_TypeChecker_Env.attrtab);
              FStar_TypeChecker_Env.instantiate_imp =
                (uu___4037_30829.FStar_TypeChecker_Env.instantiate_imp);
              FStar_TypeChecker_Env.effects =
                (uu___4037_30829.FStar_TypeChecker_Env.effects);
              FStar_TypeChecker_Env.generalize =
                (uu___4037_30829.FStar_TypeChecker_Env.generalize);
              FStar_TypeChecker_Env.letrecs =
                (uu___4037_30829.FStar_TypeChecker_Env.letrecs);
              FStar_TypeChecker_Env.top_level =
                (uu___4037_30829.FStar_TypeChecker_Env.top_level);
              FStar_TypeChecker_Env.check_uvars =
                (uu___4037_30829.FStar_TypeChecker_Env.check_uvars);
              FStar_TypeChecker_Env.use_eq =
                (uu___4037_30829.FStar_TypeChecker_Env.use_eq);
              FStar_TypeChecker_Env.is_iface =
                (uu___4037_30829.FStar_TypeChecker_Env.is_iface);
              FStar_TypeChecker_Env.admit =
                (uu___4037_30829.FStar_TypeChecker_Env.admit);
              FStar_TypeChecker_Env.lax =
                (uu___4037_30829.FStar_TypeChecker_Env.lax);
              FStar_TypeChecker_Env.lax_universes =
                (uu___4037_30829.FStar_TypeChecker_Env.lax_universes);
              FStar_TypeChecker_Env.phase1 =
                (uu___4037_30829.FStar_TypeChecker_Env.phase1);
              FStar_TypeChecker_Env.failhard =
                (uu___4037_30829.FStar_TypeChecker_Env.failhard);
              FStar_TypeChecker_Env.nosynth =
                (uu___4037_30829.FStar_TypeChecker_Env.nosynth);
              FStar_TypeChecker_Env.uvar_subtyping =
                (uu___4037_30829.FStar_TypeChecker_Env.uvar_subtyping);
              FStar_TypeChecker_Env.tc_term =
                (uu___4037_30829.FStar_TypeChecker_Env.tc_term);
              FStar_TypeChecker_Env.type_of =
                (uu___4037_30829.FStar_TypeChecker_Env.type_of);
              FStar_TypeChecker_Env.universe_of =
                (uu___4037_30829.FStar_TypeChecker_Env.universe_of);
              FStar_TypeChecker_Env.check_type_of =
                (uu___4037_30829.FStar_TypeChecker_Env.check_type_of);
              FStar_TypeChecker_Env.use_bv_sorts = true;
              FStar_TypeChecker_Env.qtbl_name_and_index =
                (uu___4037_30829.FStar_TypeChecker_Env.qtbl_name_and_index);
              FStar_TypeChecker_Env.normalized_eff_names =
                (uu___4037_30829.FStar_TypeChecker_Env.normalized_eff_names);
              FStar_TypeChecker_Env.fv_delta_depths =
                (uu___4037_30829.FStar_TypeChecker_Env.fv_delta_depths);
              FStar_TypeChecker_Env.proof_ns =
                (uu___4037_30829.FStar_TypeChecker_Env.proof_ns);
              FStar_TypeChecker_Env.synth_hook =
                (uu___4037_30829.FStar_TypeChecker_Env.synth_hook);
              FStar_TypeChecker_Env.splice =
                (uu___4037_30829.FStar_TypeChecker_Env.splice);
              FStar_TypeChecker_Env.mpreprocess =
                (uu___4037_30829.FStar_TypeChecker_Env.mpreprocess);
              FStar_TypeChecker_Env.postprocess =
                (uu___4037_30829.FStar_TypeChecker_Env.postprocess);
              FStar_TypeChecker_Env.is_native_tactic =
                (uu___4037_30829.FStar_TypeChecker_Env.is_native_tactic);
              FStar_TypeChecker_Env.identifier_info =
                (uu___4037_30829.FStar_TypeChecker_Env.identifier_info);
              FStar_TypeChecker_Env.tc_hooks =
                (uu___4037_30829.FStar_TypeChecker_Env.tc_hooks);
              FStar_TypeChecker_Env.dsenv =
                (uu___4037_30829.FStar_TypeChecker_Env.dsenv);
              FStar_TypeChecker_Env.nbe =
                (uu___4037_30829.FStar_TypeChecker_Env.nbe);
              FStar_TypeChecker_Env.strict_args_tab =
                (uu___4037_30829.FStar_TypeChecker_Env.strict_args_tab);
              FStar_TypeChecker_Env.erasable_types_tab =
                (uu___4037_30829.FStar_TypeChecker_Env.erasable_types_tab)
            }  in
          let slow_check uu____30836 =
            if must_total
            then
              let uu____30838 = env2.FStar_TypeChecker_Env.type_of env2 t  in
              match uu____30838 with | (uu____30845,uu____30846,g) -> g
            else
              (let uu____30850 = env2.FStar_TypeChecker_Env.tc_term env2 t
                  in
               match uu____30850 with | (uu____30857,uu____30858,g) -> g)
             in
          let uu____30860 = type_of_well_typed_term env2 t  in
          match uu____30860 with
          | FStar_Pervasives_Native.None  -> slow_check ()
          | FStar_Pervasives_Native.Some k' ->
              ((let uu____30865 =
                  FStar_All.pipe_left (FStar_TypeChecker_Env.debug env2)
                    (FStar_Options.Other "FastImplicits")
                   in
                if uu____30865
                then
                  let uu____30870 =
                    FStar_Range.string_of_range t.FStar_Syntax_Syntax.pos  in
                  let uu____30872 = FStar_Syntax_Print.term_to_string t  in
                  let uu____30874 = FStar_Syntax_Print.term_to_string k'  in
                  let uu____30876 = FStar_Syntax_Print.term_to_string k  in
                  FStar_Util.print4 "(%s) Fast check  %s : %s <:? %s\n"
                    uu____30870 uu____30872 uu____30874 uu____30876
                else ());
               (let g = FStar_TypeChecker_Rel.subtype_nosmt env2 k' k  in
                (let uu____30885 =
                   FStar_All.pipe_left (FStar_TypeChecker_Env.debug env2)
                     (FStar_Options.Other "FastImplicits")
                    in
                 if uu____30885
                 then
                   let uu____30890 =
                     FStar_Range.string_of_range t.FStar_Syntax_Syntax.pos
                      in
                   let uu____30892 = FStar_Syntax_Print.term_to_string t  in
                   let uu____30894 = FStar_Syntax_Print.term_to_string k'  in
                   let uu____30896 = FStar_Syntax_Print.term_to_string k  in
                   FStar_Util.print5 "(%s) Fast check %s: %s : %s <: %s\n"
                     uu____30890
                     (if FStar_Option.isSome g
                      then "succeeded with guard"
                      else "failed") uu____30892 uu____30894 uu____30896
                 else ());
                (match g with
                 | FStar_Pervasives_Native.None  -> slow_check ()
                 | FStar_Pervasives_Native.Some g1 -> g1)))
  
let (check_type_of_well_typed_term :
  Prims.bool ->
    FStar_TypeChecker_Env.env ->
      FStar_Syntax_Syntax.term ->
        FStar_Syntax_Syntax.typ -> FStar_TypeChecker_Common.guard_t)
  =
  fun must_total  ->
    fun env  ->
      fun t  ->
        fun k  ->
          let env1 = FStar_TypeChecker_Env.set_expected_typ env k  in
          let env2 =
            let uu___4068_30933 = env1  in
            {
              FStar_TypeChecker_Env.solver =
                (uu___4068_30933.FStar_TypeChecker_Env.solver);
              FStar_TypeChecker_Env.range =
                (uu___4068_30933.FStar_TypeChecker_Env.range);
              FStar_TypeChecker_Env.curmodule =
                (uu___4068_30933.FStar_TypeChecker_Env.curmodule);
              FStar_TypeChecker_Env.gamma =
                (uu___4068_30933.FStar_TypeChecker_Env.gamma);
              FStar_TypeChecker_Env.gamma_sig =
                (uu___4068_30933.FStar_TypeChecker_Env.gamma_sig);
              FStar_TypeChecker_Env.gamma_cache =
                (uu___4068_30933.FStar_TypeChecker_Env.gamma_cache);
              FStar_TypeChecker_Env.modules =
                (uu___4068_30933.FStar_TypeChecker_Env.modules);
              FStar_TypeChecker_Env.expected_typ =
                (uu___4068_30933.FStar_TypeChecker_Env.expected_typ);
              FStar_TypeChecker_Env.sigtab =
                (uu___4068_30933.FStar_TypeChecker_Env.sigtab);
              FStar_TypeChecker_Env.attrtab =
                (uu___4068_30933.FStar_TypeChecker_Env.attrtab);
              FStar_TypeChecker_Env.instantiate_imp =
                (uu___4068_30933.FStar_TypeChecker_Env.instantiate_imp);
              FStar_TypeChecker_Env.effects =
                (uu___4068_30933.FStar_TypeChecker_Env.effects);
              FStar_TypeChecker_Env.generalize =
                (uu___4068_30933.FStar_TypeChecker_Env.generalize);
              FStar_TypeChecker_Env.letrecs =
                (uu___4068_30933.FStar_TypeChecker_Env.letrecs);
              FStar_TypeChecker_Env.top_level =
                (uu___4068_30933.FStar_TypeChecker_Env.top_level);
              FStar_TypeChecker_Env.check_uvars =
                (uu___4068_30933.FStar_TypeChecker_Env.check_uvars);
              FStar_TypeChecker_Env.use_eq =
                (uu___4068_30933.FStar_TypeChecker_Env.use_eq);
              FStar_TypeChecker_Env.is_iface =
                (uu___4068_30933.FStar_TypeChecker_Env.is_iface);
              FStar_TypeChecker_Env.admit =
                (uu___4068_30933.FStar_TypeChecker_Env.admit);
              FStar_TypeChecker_Env.lax =
                (uu___4068_30933.FStar_TypeChecker_Env.lax);
              FStar_TypeChecker_Env.lax_universes =
                (uu___4068_30933.FStar_TypeChecker_Env.lax_universes);
              FStar_TypeChecker_Env.phase1 =
                (uu___4068_30933.FStar_TypeChecker_Env.phase1);
              FStar_TypeChecker_Env.failhard =
                (uu___4068_30933.FStar_TypeChecker_Env.failhard);
              FStar_TypeChecker_Env.nosynth =
                (uu___4068_30933.FStar_TypeChecker_Env.nosynth);
              FStar_TypeChecker_Env.uvar_subtyping =
                (uu___4068_30933.FStar_TypeChecker_Env.uvar_subtyping);
              FStar_TypeChecker_Env.tc_term =
                (uu___4068_30933.FStar_TypeChecker_Env.tc_term);
              FStar_TypeChecker_Env.type_of =
                (uu___4068_30933.FStar_TypeChecker_Env.type_of);
              FStar_TypeChecker_Env.universe_of =
                (uu___4068_30933.FStar_TypeChecker_Env.universe_of);
              FStar_TypeChecker_Env.check_type_of =
                (uu___4068_30933.FStar_TypeChecker_Env.check_type_of);
              FStar_TypeChecker_Env.use_bv_sorts = true;
              FStar_TypeChecker_Env.qtbl_name_and_index =
                (uu___4068_30933.FStar_TypeChecker_Env.qtbl_name_and_index);
              FStar_TypeChecker_Env.normalized_eff_names =
                (uu___4068_30933.FStar_TypeChecker_Env.normalized_eff_names);
              FStar_TypeChecker_Env.fv_delta_depths =
                (uu___4068_30933.FStar_TypeChecker_Env.fv_delta_depths);
              FStar_TypeChecker_Env.proof_ns =
                (uu___4068_30933.FStar_TypeChecker_Env.proof_ns);
              FStar_TypeChecker_Env.synth_hook =
                (uu___4068_30933.FStar_TypeChecker_Env.synth_hook);
              FStar_TypeChecker_Env.splice =
                (uu___4068_30933.FStar_TypeChecker_Env.splice);
              FStar_TypeChecker_Env.mpreprocess =
                (uu___4068_30933.FStar_TypeChecker_Env.mpreprocess);
              FStar_TypeChecker_Env.postprocess =
                (uu___4068_30933.FStar_TypeChecker_Env.postprocess);
              FStar_TypeChecker_Env.is_native_tactic =
                (uu___4068_30933.FStar_TypeChecker_Env.is_native_tactic);
              FStar_TypeChecker_Env.identifier_info =
                (uu___4068_30933.FStar_TypeChecker_Env.identifier_info);
              FStar_TypeChecker_Env.tc_hooks =
                (uu___4068_30933.FStar_TypeChecker_Env.tc_hooks);
              FStar_TypeChecker_Env.dsenv =
                (uu___4068_30933.FStar_TypeChecker_Env.dsenv);
              FStar_TypeChecker_Env.nbe =
                (uu___4068_30933.FStar_TypeChecker_Env.nbe);
              FStar_TypeChecker_Env.strict_args_tab =
                (uu___4068_30933.FStar_TypeChecker_Env.strict_args_tab);
              FStar_TypeChecker_Env.erasable_types_tab =
                (uu___4068_30933.FStar_TypeChecker_Env.erasable_types_tab)
            }  in
          let slow_check uu____30940 =
            if must_total
            then
              let uu____30942 = env2.FStar_TypeChecker_Env.type_of env2 t  in
              match uu____30942 with | (uu____30949,uu____30950,g) -> g
            else
              (let uu____30954 = env2.FStar_TypeChecker_Env.tc_term env2 t
                  in
               match uu____30954 with | (uu____30961,uu____30962,g) -> g)
             in
          let uu____30964 =
            let uu____30966 = FStar_Options.__temp_fast_implicits ()  in
            FStar_All.pipe_left Prims.op_Negation uu____30966  in
          if uu____30964
          then slow_check ()
          else check_type_of_well_typed_term' must_total env2 t k
  