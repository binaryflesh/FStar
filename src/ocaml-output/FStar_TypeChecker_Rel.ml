open Prims
let (print_ctx_uvar : FStar_Syntax_Syntax.ctx_uvar -> Prims.string) =
  fun ctx_uvar  -> FStar_Syntax_Print.ctx_uvar_to_string ctx_uvar 
type lstring = Prims.string FStar_Thunk.t
type uvi =
  | TERM of (FStar_Syntax_Syntax.ctx_uvar * FStar_Syntax_Syntax.term) 
  | UNIV of (FStar_Syntax_Syntax.universe_uvar *
  FStar_Syntax_Syntax.universe) 
let (uu___is_TERM : uvi -> Prims.bool) =
  fun projectee  ->
    match projectee with | TERM _0 -> true | uu____49 -> false
  
let (__proj__TERM__item___0 :
  uvi -> (FStar_Syntax_Syntax.ctx_uvar * FStar_Syntax_Syntax.term)) =
  fun projectee  -> match projectee with | TERM _0 -> _0 
let (uu___is_UNIV : uvi -> Prims.bool) =
  fun projectee  ->
    match projectee with | UNIV _0 -> true | uu____84 -> false
  
let (__proj__UNIV__item___0 :
  uvi -> (FStar_Syntax_Syntax.universe_uvar * FStar_Syntax_Syntax.universe))
  = fun projectee  -> match projectee with | UNIV _0 -> _0 
type worklist =
  {
  attempting: FStar_TypeChecker_Common.probs ;
  wl_deferred:
    (Prims.int * lstring * FStar_TypeChecker_Common.prob) Prims.list ;
  ctr: Prims.int ;
  defer_ok: Prims.bool ;
  smt_ok: Prims.bool ;
  umax_heuristic_ok: Prims.bool ;
  tcenv: FStar_TypeChecker_Env.env ;
  wl_implicits: FStar_TypeChecker_Common.implicits }
let (__proj__Mkworklist__item__attempting :
  worklist -> FStar_TypeChecker_Common.probs) =
  fun projectee  ->
    match projectee with
    | { attempting; wl_deferred; ctr; defer_ok; smt_ok; umax_heuristic_ok;
        tcenv; wl_implicits;_} -> attempting
  
let (__proj__Mkworklist__item__wl_deferred :
  worklist ->
    (Prims.int * lstring * FStar_TypeChecker_Common.prob) Prims.list)
  =
  fun projectee  ->
    match projectee with
    | { attempting; wl_deferred; ctr; defer_ok; smt_ok; umax_heuristic_ok;
        tcenv; wl_implicits;_} -> wl_deferred
  
let (__proj__Mkworklist__item__ctr : worklist -> Prims.int) =
  fun projectee  ->
    match projectee with
    | { attempting; wl_deferred; ctr; defer_ok; smt_ok; umax_heuristic_ok;
        tcenv; wl_implicits;_} -> ctr
  
let (__proj__Mkworklist__item__defer_ok : worklist -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | { attempting; wl_deferred; ctr; defer_ok; smt_ok; umax_heuristic_ok;
        tcenv; wl_implicits;_} -> defer_ok
  
let (__proj__Mkworklist__item__smt_ok : worklist -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | { attempting; wl_deferred; ctr; defer_ok; smt_ok; umax_heuristic_ok;
        tcenv; wl_implicits;_} -> smt_ok
  
let (__proj__Mkworklist__item__umax_heuristic_ok : worklist -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | { attempting; wl_deferred; ctr; defer_ok; smt_ok; umax_heuristic_ok;
        tcenv; wl_implicits;_} -> umax_heuristic_ok
  
let (__proj__Mkworklist__item__tcenv : worklist -> FStar_TypeChecker_Env.env)
  =
  fun projectee  ->
    match projectee with
    | { attempting; wl_deferred; ctr; defer_ok; smt_ok; umax_heuristic_ok;
        tcenv; wl_implicits;_} -> tcenv
  
let (__proj__Mkworklist__item__wl_implicits :
  worklist -> FStar_TypeChecker_Common.implicits) =
  fun projectee  ->
    match projectee with
    | { attempting; wl_deferred; ctr; defer_ok; smt_ok; umax_heuristic_ok;
        tcenv; wl_implicits;_} -> wl_implicits
  
let (new_uvar :
  Prims.string ->
    worklist ->
      FStar_Range.range ->
        FStar_Syntax_Syntax.binding Prims.list ->
          (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.arg_qualifier
            FStar_Pervasives_Native.option) Prims.list ->
            FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
              FStar_Syntax_Syntax.should_check_uvar ->
                (FStar_Dyn.dyn * FStar_Syntax_Syntax.term'
                  FStar_Syntax_Syntax.syntax) FStar_Pervasives_Native.option
                  ->
                  (FStar_Syntax_Syntax.ctx_uvar * FStar_Syntax_Syntax.term *
                    worklist))
  =
  fun reason  ->
    fun wl  ->
      fun r  ->
        fun gamma  ->
          fun binders  ->
            fun k  ->
              fun should_check  ->
                fun meta  ->
                  let ctx_uvar =
                    let uu____515 = FStar_Syntax_Unionfind.fresh ()  in
                    {
                      FStar_Syntax_Syntax.ctx_uvar_head = uu____515;
                      FStar_Syntax_Syntax.ctx_uvar_gamma = gamma;
                      FStar_Syntax_Syntax.ctx_uvar_binders = binders;
                      FStar_Syntax_Syntax.ctx_uvar_typ = k;
                      FStar_Syntax_Syntax.ctx_uvar_reason = reason;
                      FStar_Syntax_Syntax.ctx_uvar_should_check =
                        should_check;
                      FStar_Syntax_Syntax.ctx_uvar_range = r;
                      FStar_Syntax_Syntax.ctx_uvar_meta = meta
                    }  in
                  FStar_TypeChecker_Common.check_uvar_ctx_invariant reason r
                    true gamma binders;
                  (let t =
                     FStar_Syntax_Syntax.mk
                       (FStar_Syntax_Syntax.Tm_uvar
                          (ctx_uvar, ([], FStar_Syntax_Syntax.NoUseRange)))
                       FStar_Pervasives_Native.None r
                      in
                   let imp =
                     {
                       FStar_TypeChecker_Common.imp_reason = reason;
                       FStar_TypeChecker_Common.imp_uvar = ctx_uvar;
                       FStar_TypeChecker_Common.imp_tm = t;
                       FStar_TypeChecker_Common.imp_range = r
                     }  in
                   (ctx_uvar, t,
                     (let uu___71_547 = wl  in
                      {
                        attempting = (uu___71_547.attempting);
                        wl_deferred = (uu___71_547.wl_deferred);
                        ctr = (uu___71_547.ctr);
                        defer_ok = (uu___71_547.defer_ok);
                        smt_ok = (uu___71_547.smt_ok);
                        umax_heuristic_ok = (uu___71_547.umax_heuristic_ok);
                        tcenv = (uu___71_547.tcenv);
                        wl_implicits = (imp :: (wl.wl_implicits))
                      })))
  
let (copy_uvar :
  FStar_Syntax_Syntax.ctx_uvar ->
    FStar_Syntax_Syntax.binders ->
      FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
        worklist ->
          (FStar_Syntax_Syntax.ctx_uvar * FStar_Syntax_Syntax.term *
            worklist))
  =
  fun u  ->
    fun bs  ->
      fun t  ->
        fun wl  ->
          let env =
            let uu___77_586 = wl.tcenv  in
            {
              FStar_TypeChecker_Env.solver =
                (uu___77_586.FStar_TypeChecker_Env.solver);
              FStar_TypeChecker_Env.range =
                (uu___77_586.FStar_TypeChecker_Env.range);
              FStar_TypeChecker_Env.curmodule =
                (uu___77_586.FStar_TypeChecker_Env.curmodule);
              FStar_TypeChecker_Env.gamma =
                (u.FStar_Syntax_Syntax.ctx_uvar_gamma);
              FStar_TypeChecker_Env.gamma_sig =
                (uu___77_586.FStar_TypeChecker_Env.gamma_sig);
              FStar_TypeChecker_Env.gamma_cache =
                (uu___77_586.FStar_TypeChecker_Env.gamma_cache);
              FStar_TypeChecker_Env.modules =
                (uu___77_586.FStar_TypeChecker_Env.modules);
              FStar_TypeChecker_Env.expected_typ =
                (uu___77_586.FStar_TypeChecker_Env.expected_typ);
              FStar_TypeChecker_Env.sigtab =
                (uu___77_586.FStar_TypeChecker_Env.sigtab);
              FStar_TypeChecker_Env.attrtab =
                (uu___77_586.FStar_TypeChecker_Env.attrtab);
              FStar_TypeChecker_Env.instantiate_imp =
                (uu___77_586.FStar_TypeChecker_Env.instantiate_imp);
              FStar_TypeChecker_Env.effects =
                (uu___77_586.FStar_TypeChecker_Env.effects);
              FStar_TypeChecker_Env.generalize =
                (uu___77_586.FStar_TypeChecker_Env.generalize);
              FStar_TypeChecker_Env.letrecs =
                (uu___77_586.FStar_TypeChecker_Env.letrecs);
              FStar_TypeChecker_Env.top_level =
                (uu___77_586.FStar_TypeChecker_Env.top_level);
              FStar_TypeChecker_Env.check_uvars =
                (uu___77_586.FStar_TypeChecker_Env.check_uvars);
              FStar_TypeChecker_Env.use_eq =
                (uu___77_586.FStar_TypeChecker_Env.use_eq);
              FStar_TypeChecker_Env.is_iface =
                (uu___77_586.FStar_TypeChecker_Env.is_iface);
              FStar_TypeChecker_Env.admit =
                (uu___77_586.FStar_TypeChecker_Env.admit);
              FStar_TypeChecker_Env.lax =
                (uu___77_586.FStar_TypeChecker_Env.lax);
              FStar_TypeChecker_Env.lax_universes =
                (uu___77_586.FStar_TypeChecker_Env.lax_universes);
              FStar_TypeChecker_Env.phase1 =
                (uu___77_586.FStar_TypeChecker_Env.phase1);
              FStar_TypeChecker_Env.failhard =
                (uu___77_586.FStar_TypeChecker_Env.failhard);
              FStar_TypeChecker_Env.nosynth =
                (uu___77_586.FStar_TypeChecker_Env.nosynth);
              FStar_TypeChecker_Env.uvar_subtyping =
                (uu___77_586.FStar_TypeChecker_Env.uvar_subtyping);
              FStar_TypeChecker_Env.tc_term =
                (uu___77_586.FStar_TypeChecker_Env.tc_term);
              FStar_TypeChecker_Env.type_of =
                (uu___77_586.FStar_TypeChecker_Env.type_of);
              FStar_TypeChecker_Env.universe_of =
                (uu___77_586.FStar_TypeChecker_Env.universe_of);
              FStar_TypeChecker_Env.check_type_of =
                (uu___77_586.FStar_TypeChecker_Env.check_type_of);
              FStar_TypeChecker_Env.use_bv_sorts =
                (uu___77_586.FStar_TypeChecker_Env.use_bv_sorts);
              FStar_TypeChecker_Env.qtbl_name_and_index =
                (uu___77_586.FStar_TypeChecker_Env.qtbl_name_and_index);
              FStar_TypeChecker_Env.normalized_eff_names =
                (uu___77_586.FStar_TypeChecker_Env.normalized_eff_names);
              FStar_TypeChecker_Env.fv_delta_depths =
                (uu___77_586.FStar_TypeChecker_Env.fv_delta_depths);
              FStar_TypeChecker_Env.proof_ns =
                (uu___77_586.FStar_TypeChecker_Env.proof_ns);
              FStar_TypeChecker_Env.synth_hook =
                (uu___77_586.FStar_TypeChecker_Env.synth_hook);
              FStar_TypeChecker_Env.splice =
                (uu___77_586.FStar_TypeChecker_Env.splice);
              FStar_TypeChecker_Env.mpreprocess =
                (uu___77_586.FStar_TypeChecker_Env.mpreprocess);
              FStar_TypeChecker_Env.postprocess =
                (uu___77_586.FStar_TypeChecker_Env.postprocess);
              FStar_TypeChecker_Env.is_native_tactic =
                (uu___77_586.FStar_TypeChecker_Env.is_native_tactic);
              FStar_TypeChecker_Env.identifier_info =
                (uu___77_586.FStar_TypeChecker_Env.identifier_info);
              FStar_TypeChecker_Env.tc_hooks =
                (uu___77_586.FStar_TypeChecker_Env.tc_hooks);
              FStar_TypeChecker_Env.dsenv =
                (uu___77_586.FStar_TypeChecker_Env.dsenv);
              FStar_TypeChecker_Env.nbe =
                (uu___77_586.FStar_TypeChecker_Env.nbe);
              FStar_TypeChecker_Env.strict_args_tab =
                (uu___77_586.FStar_TypeChecker_Env.strict_args_tab);
              FStar_TypeChecker_Env.erasable_types_tab =
                (uu___77_586.FStar_TypeChecker_Env.erasable_types_tab)
            }  in
          let env1 = FStar_TypeChecker_Env.push_binders env bs  in
          let uu____588 = FStar_TypeChecker_Env.all_binders env1  in
          new_uvar
            (Prims.op_Hat "copy:" u.FStar_Syntax_Syntax.ctx_uvar_reason) wl
            u.FStar_Syntax_Syntax.ctx_uvar_range
            env1.FStar_TypeChecker_Env.gamma uu____588 t
            u.FStar_Syntax_Syntax.ctx_uvar_should_check
            u.FStar_Syntax_Syntax.ctx_uvar_meta
  
type solution =
  | Success of (FStar_TypeChecker_Common.deferred *
  FStar_TypeChecker_Common.implicits) 
  | Failed of (FStar_TypeChecker_Common.prob * lstring) 
let (uu___is_Success : solution -> Prims.bool) =
  fun projectee  ->
    match projectee with | Success _0 -> true | uu____649 -> false
  
let (__proj__Success__item___0 :
  solution ->
    (FStar_TypeChecker_Common.deferred * FStar_TypeChecker_Common.implicits))
  = fun projectee  -> match projectee with | Success _0 -> _0 
let (uu___is_Failed : solution -> Prims.bool) =
  fun projectee  ->
    match projectee with | Failed _0 -> true | uu____684 -> false
  
let (__proj__Failed__item___0 :
  solution -> (FStar_TypeChecker_Common.prob * lstring)) =
  fun projectee  -> match projectee with | Failed _0 -> _0 
type variance =
  | COVARIANT 
  | CONTRAVARIANT 
  | INVARIANT 
let (uu___is_COVARIANT : variance -> Prims.bool) =
  fun projectee  ->
    match projectee with | COVARIANT  -> true | uu____714 -> false
  
let (uu___is_CONTRAVARIANT : variance -> Prims.bool) =
  fun projectee  ->
    match projectee with | CONTRAVARIANT  -> true | uu____725 -> false
  
let (uu___is_INVARIANT : variance -> Prims.bool) =
  fun projectee  ->
    match projectee with | INVARIANT  -> true | uu____736 -> false
  
type tprob = FStar_Syntax_Syntax.typ FStar_TypeChecker_Common.problem
type cprob = FStar_Syntax_Syntax.comp FStar_TypeChecker_Common.problem
type 'a problem_t = 'a FStar_TypeChecker_Common.problem
let (rel_to_string : FStar_TypeChecker_Common.rel -> Prims.string) =
  fun uu___0_754  ->
    match uu___0_754 with
    | FStar_TypeChecker_Common.EQ  -> "="
    | FStar_TypeChecker_Common.SUB  -> "<:"
    | FStar_TypeChecker_Common.SUBINV  -> ":>"
  
let (term_to_string : FStar_Syntax_Syntax.term -> Prims.string) =
  fun t  ->
    let uu____766 = FStar_Syntax_Util.head_and_args t  in
    match uu____766 with
    | (head1,args) ->
        (match head1.FStar_Syntax_Syntax.n with
         | FStar_Syntax_Syntax.Tm_uvar (u,s) ->
             let uu____829 = FStar_Syntax_Print.ctx_uvar_to_string u  in
             let uu____831 =
               match FStar_Pervasives_Native.fst s with
               | [] -> ""
               | s1 ->
                   let uu____846 =
                     let uu____848 = FStar_List.hd s1  in
                     FStar_Syntax_Print.subst_to_string uu____848  in
                   FStar_Util.format1 "@<%s>" uu____846
                in
             let uu____852 = FStar_Syntax_Print.args_to_string args  in
             FStar_Util.format3 "%s%s %s" uu____829 uu____831 uu____852
         | uu____855 -> FStar_Syntax_Print.term_to_string t)
  
let (prob_to_string :
  FStar_TypeChecker_Env.env -> FStar_TypeChecker_Common.prob -> Prims.string)
  =
  fun env  ->
    fun uu___1_867  ->
      match uu___1_867 with
      | FStar_TypeChecker_Common.TProb p ->
          let uu____872 =
            let uu____876 =
              FStar_Util.string_of_int p.FStar_TypeChecker_Common.pid  in
            let uu____878 =
              let uu____882 = term_to_string p.FStar_TypeChecker_Common.lhs
                 in
              let uu____884 =
                let uu____888 =
                  let uu____892 =
                    term_to_string p.FStar_TypeChecker_Common.rhs  in
                  [uu____892]  in
                (rel_to_string p.FStar_TypeChecker_Common.relation) ::
                  uu____888
                 in
              uu____882 :: uu____884  in
            uu____876 :: uu____878  in
          FStar_Util.format "\n%s:\t%s \n\t\t%s\n\t%s\n" uu____872
      | FStar_TypeChecker_Common.CProb p ->
          let uu____903 =
            FStar_Util.string_of_int p.FStar_TypeChecker_Common.pid  in
          let uu____905 =
            FStar_TypeChecker_Normalize.comp_to_string env
              p.FStar_TypeChecker_Common.lhs
             in
          let uu____907 =
            FStar_TypeChecker_Normalize.comp_to_string env
              p.FStar_TypeChecker_Common.rhs
             in
          FStar_Util.format4 "\n%s:\t%s \n\t\t%s\n\t%s" uu____903 uu____905
            (rel_to_string p.FStar_TypeChecker_Common.relation) uu____907
  
let (uvi_to_string : FStar_TypeChecker_Env.env -> uvi -> Prims.string) =
  fun env  ->
    fun uu___2_921  ->
      match uu___2_921 with
      | UNIV (u,t) ->
          let x =
            let uu____927 = FStar_Options.hide_uvar_nums ()  in
            if uu____927
            then "?"
            else
              (let uu____934 = FStar_Syntax_Unionfind.univ_uvar_id u  in
               FStar_All.pipe_right uu____934 FStar_Util.string_of_int)
             in
          let uu____938 = FStar_Syntax_Print.univ_to_string t  in
          FStar_Util.format2 "UNIV %s %s" x uu____938
      | TERM (u,t) ->
          let x =
            let uu____945 = FStar_Options.hide_uvar_nums ()  in
            if uu____945
            then "?"
            else
              (let uu____952 =
                 FStar_Syntax_Unionfind.uvar_id
                   u.FStar_Syntax_Syntax.ctx_uvar_head
                  in
               FStar_All.pipe_right uu____952 FStar_Util.string_of_int)
             in
          let uu____956 = FStar_TypeChecker_Normalize.term_to_string env t
             in
          FStar_Util.format2 "TERM %s %s" x uu____956
  
let (uvis_to_string :
  FStar_TypeChecker_Env.env -> uvi Prims.list -> Prims.string) =
  fun env  ->
    fun uvis  ->
      let uu____975 = FStar_List.map (uvi_to_string env) uvis  in
      FStar_All.pipe_right uu____975 (FStar_String.concat ", ")
  
let (names_to_string : FStar_Syntax_Syntax.bv FStar_Util.set -> Prims.string)
  =
  fun nms  ->
    let uu____996 =
      let uu____1000 = FStar_Util.set_elements nms  in
      FStar_All.pipe_right uu____1000
        (FStar_List.map FStar_Syntax_Print.bv_to_string)
       in
    FStar_All.pipe_right uu____996 (FStar_String.concat ", ")
  
let args_to_string :
  'Auu____1019 .
    (FStar_Syntax_Syntax.term * 'Auu____1019) Prims.list -> Prims.string
  =
  fun args  ->
    let uu____1038 =
      FStar_All.pipe_right args
        (FStar_List.map
           (fun uu____1059  ->
              match uu____1059 with
              | (x,uu____1066) -> FStar_Syntax_Print.term_to_string x))
       in
    FStar_All.pipe_right uu____1038 (FStar_String.concat " ")
  
let (empty_worklist : FStar_TypeChecker_Env.env -> worklist) =
  fun env  ->
    {
      attempting = [];
      wl_deferred = [];
      ctr = Prims.int_zero;
      defer_ok = true;
      smt_ok = true;
      umax_heuristic_ok = true;
      tcenv = env;
      wl_implicits = []
    }
  
let (giveup :
  FStar_TypeChecker_Env.env ->
    lstring -> FStar_TypeChecker_Common.prob -> solution)
  =
  fun env  ->
    fun reason  ->
      fun prob  ->
        (let uu____1106 =
           FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
             (FStar_Options.Other "Rel")
            in
         if uu____1106
         then
           let uu____1111 = FStar_Thunk.force reason  in
           let uu____1114 = prob_to_string env prob  in
           FStar_Util.print2 "Failed %s:\n%s\n" uu____1111 uu____1114
         else ());
        Failed (prob, reason)
  
let (giveup_lit :
  FStar_TypeChecker_Env.env ->
    Prims.string -> FStar_TypeChecker_Common.prob -> solution)
  =
  fun env  ->
    fun reason  ->
      fun prob  ->
        let uu____1137 = FStar_Thunk.mk (fun uu____1140  -> reason)  in
        giveup env uu____1137 prob
  
let (invert_rel :
  FStar_TypeChecker_Common.rel -> FStar_TypeChecker_Common.rel) =
  fun uu___3_1146  ->
    match uu___3_1146 with
    | FStar_TypeChecker_Common.EQ  -> FStar_TypeChecker_Common.EQ
    | FStar_TypeChecker_Common.SUB  -> FStar_TypeChecker_Common.SUBINV
    | FStar_TypeChecker_Common.SUBINV  -> FStar_TypeChecker_Common.SUB
  
let invert :
  'Auu____1152 .
    'Auu____1152 FStar_TypeChecker_Common.problem ->
      'Auu____1152 FStar_TypeChecker_Common.problem
  =
  fun p  ->
    let uu___141_1164 = p  in
    {
      FStar_TypeChecker_Common.pid =
        (uu___141_1164.FStar_TypeChecker_Common.pid);
      FStar_TypeChecker_Common.lhs = (p.FStar_TypeChecker_Common.rhs);
      FStar_TypeChecker_Common.relation =
        (invert_rel p.FStar_TypeChecker_Common.relation);
      FStar_TypeChecker_Common.rhs = (p.FStar_TypeChecker_Common.lhs);
      FStar_TypeChecker_Common.element =
        (uu___141_1164.FStar_TypeChecker_Common.element);
      FStar_TypeChecker_Common.logical_guard =
        (uu___141_1164.FStar_TypeChecker_Common.logical_guard);
      FStar_TypeChecker_Common.logical_guard_uvar =
        (uu___141_1164.FStar_TypeChecker_Common.logical_guard_uvar);
      FStar_TypeChecker_Common.reason =
        (uu___141_1164.FStar_TypeChecker_Common.reason);
      FStar_TypeChecker_Common.loc =
        (uu___141_1164.FStar_TypeChecker_Common.loc);
      FStar_TypeChecker_Common.rank =
        (uu___141_1164.FStar_TypeChecker_Common.rank)
    }
  
let maybe_invert :
  'Auu____1172 .
    'Auu____1172 FStar_TypeChecker_Common.problem ->
      'Auu____1172 FStar_TypeChecker_Common.problem
  =
  fun p  ->
    if p.FStar_TypeChecker_Common.relation = FStar_TypeChecker_Common.SUBINV
    then invert p
    else p
  
let (maybe_invert_p :
  FStar_TypeChecker_Common.prob -> FStar_TypeChecker_Common.prob) =
  fun uu___4_1192  ->
    match uu___4_1192 with
    | FStar_TypeChecker_Common.TProb p ->
        FStar_All.pipe_right (maybe_invert p)
          (fun _1198  -> FStar_TypeChecker_Common.TProb _1198)
    | FStar_TypeChecker_Common.CProb p ->
        FStar_All.pipe_right (maybe_invert p)
          (fun _1204  -> FStar_TypeChecker_Common.CProb _1204)
  
let (make_prob_eq :
  FStar_TypeChecker_Common.prob -> FStar_TypeChecker_Common.prob) =
  fun uu___5_1210  ->
    match uu___5_1210 with
    | FStar_TypeChecker_Common.TProb p ->
        FStar_TypeChecker_Common.TProb
          (let uu___153_1216 = p  in
           {
             FStar_TypeChecker_Common.pid =
               (uu___153_1216.FStar_TypeChecker_Common.pid);
             FStar_TypeChecker_Common.lhs =
               (uu___153_1216.FStar_TypeChecker_Common.lhs);
             FStar_TypeChecker_Common.relation = FStar_TypeChecker_Common.EQ;
             FStar_TypeChecker_Common.rhs =
               (uu___153_1216.FStar_TypeChecker_Common.rhs);
             FStar_TypeChecker_Common.element =
               (uu___153_1216.FStar_TypeChecker_Common.element);
             FStar_TypeChecker_Common.logical_guard =
               (uu___153_1216.FStar_TypeChecker_Common.logical_guard);
             FStar_TypeChecker_Common.logical_guard_uvar =
               (uu___153_1216.FStar_TypeChecker_Common.logical_guard_uvar);
             FStar_TypeChecker_Common.reason =
               (uu___153_1216.FStar_TypeChecker_Common.reason);
             FStar_TypeChecker_Common.loc =
               (uu___153_1216.FStar_TypeChecker_Common.loc);
             FStar_TypeChecker_Common.rank =
               (uu___153_1216.FStar_TypeChecker_Common.rank)
           })
    | FStar_TypeChecker_Common.CProb p ->
        FStar_TypeChecker_Common.CProb
          (let uu___157_1224 = p  in
           {
             FStar_TypeChecker_Common.pid =
               (uu___157_1224.FStar_TypeChecker_Common.pid);
             FStar_TypeChecker_Common.lhs =
               (uu___157_1224.FStar_TypeChecker_Common.lhs);
             FStar_TypeChecker_Common.relation = FStar_TypeChecker_Common.EQ;
             FStar_TypeChecker_Common.rhs =
               (uu___157_1224.FStar_TypeChecker_Common.rhs);
             FStar_TypeChecker_Common.element =
               (uu___157_1224.FStar_TypeChecker_Common.element);
             FStar_TypeChecker_Common.logical_guard =
               (uu___157_1224.FStar_TypeChecker_Common.logical_guard);
             FStar_TypeChecker_Common.logical_guard_uvar =
               (uu___157_1224.FStar_TypeChecker_Common.logical_guard_uvar);
             FStar_TypeChecker_Common.reason =
               (uu___157_1224.FStar_TypeChecker_Common.reason);
             FStar_TypeChecker_Common.loc =
               (uu___157_1224.FStar_TypeChecker_Common.loc);
             FStar_TypeChecker_Common.rank =
               (uu___157_1224.FStar_TypeChecker_Common.rank)
           })
  
let (vary_rel :
  FStar_TypeChecker_Common.rel -> variance -> FStar_TypeChecker_Common.rel) =
  fun rel  ->
    fun uu___6_1237  ->
      match uu___6_1237 with
      | INVARIANT  -> FStar_TypeChecker_Common.EQ
      | CONTRAVARIANT  -> invert_rel rel
      | COVARIANT  -> rel
  
let (p_pid : FStar_TypeChecker_Common.prob -> Prims.int) =
  fun uu___7_1244  ->
    match uu___7_1244 with
    | FStar_TypeChecker_Common.TProb p -> p.FStar_TypeChecker_Common.pid
    | FStar_TypeChecker_Common.CProb p -> p.FStar_TypeChecker_Common.pid
  
let (p_rel : FStar_TypeChecker_Common.prob -> FStar_TypeChecker_Common.rel) =
  fun uu___8_1257  ->
    match uu___8_1257 with
    | FStar_TypeChecker_Common.TProb p -> p.FStar_TypeChecker_Common.relation
    | FStar_TypeChecker_Common.CProb p -> p.FStar_TypeChecker_Common.relation
  
let (p_reason : FStar_TypeChecker_Common.prob -> Prims.string Prims.list) =
  fun uu___9_1272  ->
    match uu___9_1272 with
    | FStar_TypeChecker_Common.TProb p -> p.FStar_TypeChecker_Common.reason
    | FStar_TypeChecker_Common.CProb p -> p.FStar_TypeChecker_Common.reason
  
let (p_loc : FStar_TypeChecker_Common.prob -> FStar_Range.range) =
  fun uu___10_1287  ->
    match uu___10_1287 with
    | FStar_TypeChecker_Common.TProb p -> p.FStar_TypeChecker_Common.loc
    | FStar_TypeChecker_Common.CProb p -> p.FStar_TypeChecker_Common.loc
  
let (p_element :
  FStar_TypeChecker_Common.prob ->
    FStar_Syntax_Syntax.bv FStar_Pervasives_Native.option)
  =
  fun uu___11_1301  ->
    match uu___11_1301 with
    | FStar_TypeChecker_Common.TProb p -> p.FStar_TypeChecker_Common.element
    | FStar_TypeChecker_Common.CProb p -> p.FStar_TypeChecker_Common.element
  
let (p_guard : FStar_TypeChecker_Common.prob -> FStar_Syntax_Syntax.term) =
  fun uu___12_1315  ->
    match uu___12_1315 with
    | FStar_TypeChecker_Common.TProb p ->
        p.FStar_TypeChecker_Common.logical_guard
    | FStar_TypeChecker_Common.CProb p ->
        p.FStar_TypeChecker_Common.logical_guard
  
let (p_guard_uvar :
  FStar_TypeChecker_Common.prob -> FStar_Syntax_Syntax.ctx_uvar) =
  fun uu___13_1327  ->
    match uu___13_1327 with
    | FStar_TypeChecker_Common.TProb p ->
        p.FStar_TypeChecker_Common.logical_guard_uvar
    | FStar_TypeChecker_Common.CProb p ->
        p.FStar_TypeChecker_Common.logical_guard_uvar
  
let def_scope_wf :
  'Auu____1343 .
    Prims.string ->
      FStar_Range.range ->
        (FStar_Syntax_Syntax.bv * 'Auu____1343) Prims.list -> unit
  =
  fun msg  ->
    fun rng  ->
      fun r  ->
        let uu____1373 =
          let uu____1375 = FStar_Options.defensive ()  in
          Prims.op_Negation uu____1375  in
        if uu____1373
        then ()
        else
          (let rec aux prev next =
             match next with
             | [] -> ()
             | (bv,uu____1412)::bs ->
                 (FStar_TypeChecker_Env.def_check_closed_in rng msg prev
                    bv.FStar_Syntax_Syntax.sort;
                  aux (FStar_List.append prev [bv]) bs)
              in
           aux [] r)
  
let (p_scope :
  FStar_TypeChecker_Common.prob ->
    (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.arg_qualifier
      FStar_Pervasives_Native.option) Prims.list)
  =
  fun prob  ->
    let r =
      match prob with
      | FStar_TypeChecker_Common.TProb p ->
          let uu____1459 =
            match p_element prob with
            | FStar_Pervasives_Native.None  -> []
            | FStar_Pervasives_Native.Some x ->
                let uu____1483 = FStar_Syntax_Syntax.mk_binder x  in
                [uu____1483]
             in
          FStar_List.append
            (p.FStar_TypeChecker_Common.logical_guard_uvar).FStar_Syntax_Syntax.ctx_uvar_binders
            uu____1459
      | FStar_TypeChecker_Common.CProb p ->
          let uu____1511 =
            match p_element prob with
            | FStar_Pervasives_Native.None  -> []
            | FStar_Pervasives_Native.Some x ->
                let uu____1535 = FStar_Syntax_Syntax.mk_binder x  in
                [uu____1535]
             in
          FStar_List.append
            (p.FStar_TypeChecker_Common.logical_guard_uvar).FStar_Syntax_Syntax.ctx_uvar_binders
            uu____1511
       in
    def_scope_wf "p_scope" (p_loc prob) r; r
  
let (def_check_scoped :
  Prims.string ->
    FStar_TypeChecker_Common.prob -> FStar_Syntax_Syntax.term -> unit)
  =
  fun msg  ->
    fun prob  ->
      fun phi  ->
        let uu____1582 =
          let uu____1584 = FStar_Options.defensive ()  in
          Prims.op_Negation uu____1584  in
        if uu____1582
        then ()
        else
          (let uu____1589 =
             let uu____1592 = p_scope prob  in
             FStar_All.pipe_left (FStar_List.map FStar_Pervasives_Native.fst)
               uu____1592
              in
           FStar_TypeChecker_Env.def_check_closed_in (p_loc prob) msg
             uu____1589 phi)
  
let (def_check_scoped_comp :
  Prims.string ->
    FStar_TypeChecker_Common.prob ->
      FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax -> unit)
  =
  fun msg  ->
    fun prob  ->
      fun comp  ->
        let uu____1641 =
          let uu____1643 = FStar_Options.defensive ()  in
          Prims.op_Negation uu____1643  in
        if uu____1641
        then ()
        else
          (let uu____1648 = FStar_Syntax_Util.arrow [] comp  in
           def_check_scoped msg prob uu____1648)
  
let (def_check_prob : Prims.string -> FStar_TypeChecker_Common.prob -> unit)
  =
  fun msg  ->
    fun prob  ->
      let uu____1668 =
        let uu____1670 = FStar_Options.defensive ()  in
        Prims.op_Negation uu____1670  in
      if uu____1668
      then ()
      else
        (let msgf m =
           let uu____1684 =
             let uu____1686 =
               let uu____1688 = FStar_Util.string_of_int (p_pid prob)  in
               Prims.op_Hat uu____1688 (Prims.op_Hat "." m)  in
             Prims.op_Hat "." uu____1686  in
           Prims.op_Hat msg uu____1684  in
         (let uu____1693 = msgf "scope"  in
          let uu____1696 = p_scope prob  in
          def_scope_wf uu____1693 (p_loc prob) uu____1696);
         (let uu____1708 = msgf "guard"  in
          def_check_scoped uu____1708 prob (p_guard prob));
         (match prob with
          | FStar_TypeChecker_Common.TProb p ->
              ((let uu____1715 = msgf "lhs"  in
                def_check_scoped uu____1715 prob
                  p.FStar_TypeChecker_Common.lhs);
               (let uu____1718 = msgf "rhs"  in
                def_check_scoped uu____1718 prob
                  p.FStar_TypeChecker_Common.rhs))
          | FStar_TypeChecker_Common.CProb p ->
              ((let uu____1725 = msgf "lhs"  in
                def_check_scoped_comp uu____1725 prob
                  p.FStar_TypeChecker_Common.lhs);
               (let uu____1728 = msgf "rhs"  in
                def_check_scoped_comp uu____1728 prob
                  p.FStar_TypeChecker_Common.rhs))))
  
let (singleton :
  worklist -> FStar_TypeChecker_Common.prob -> Prims.bool -> worklist) =
  fun wl  ->
    fun prob  ->
      fun smt_ok  ->
        let uu___250_1749 = wl  in
        {
          attempting = [prob];
          wl_deferred = (uu___250_1749.wl_deferred);
          ctr = (uu___250_1749.ctr);
          defer_ok = (uu___250_1749.defer_ok);
          smt_ok;
          umax_heuristic_ok = (uu___250_1749.umax_heuristic_ok);
          tcenv = (uu___250_1749.tcenv);
          wl_implicits = (uu___250_1749.wl_implicits)
        }
  
let wl_of_guard :
  'Auu____1757 .
    FStar_TypeChecker_Env.env ->
      ('Auu____1757 * FStar_TypeChecker_Common.prob) Prims.list -> worklist
  =
  fun env  ->
    fun g  ->
      let uu___254_1780 = empty_worklist env  in
      let uu____1781 = FStar_List.map FStar_Pervasives_Native.snd g  in
      {
        attempting = uu____1781;
        wl_deferred = (uu___254_1780.wl_deferred);
        ctr = (uu___254_1780.ctr);
        defer_ok = (uu___254_1780.defer_ok);
        smt_ok = (uu___254_1780.smt_ok);
        umax_heuristic_ok = (uu___254_1780.umax_heuristic_ok);
        tcenv = (uu___254_1780.tcenv);
        wl_implicits = (uu___254_1780.wl_implicits)
      }
  
let (defer :
  lstring -> FStar_TypeChecker_Common.prob -> worklist -> worklist) =
  fun reason  ->
    fun prob  ->
      fun wl  ->
        let uu___259_1802 = wl  in
        {
          attempting = (uu___259_1802.attempting);
          wl_deferred = (((wl.ctr), reason, prob) :: (wl.wl_deferred));
          ctr = (uu___259_1802.ctr);
          defer_ok = (uu___259_1802.defer_ok);
          smt_ok = (uu___259_1802.smt_ok);
          umax_heuristic_ok = (uu___259_1802.umax_heuristic_ok);
          tcenv = (uu___259_1802.tcenv);
          wl_implicits = (uu___259_1802.wl_implicits)
        }
  
let (defer_lit :
  Prims.string -> FStar_TypeChecker_Common.prob -> worklist -> worklist) =
  fun reason  ->
    fun prob  ->
      fun wl  ->
        let uu____1829 = FStar_Thunk.mkv reason  in defer uu____1829 prob wl
  
let (attempt :
  FStar_TypeChecker_Common.prob Prims.list -> worklist -> worklist) =
  fun probs  ->
    fun wl  ->
      FStar_List.iter (def_check_prob "attempt") probs;
      (let uu___267_1848 = wl  in
       {
         attempting = (FStar_List.append probs wl.attempting);
         wl_deferred = (uu___267_1848.wl_deferred);
         ctr = (uu___267_1848.ctr);
         defer_ok = (uu___267_1848.defer_ok);
         smt_ok = (uu___267_1848.smt_ok);
         umax_heuristic_ok = (uu___267_1848.umax_heuristic_ok);
         tcenv = (uu___267_1848.tcenv);
         wl_implicits = (uu___267_1848.wl_implicits)
       })
  
let mk_eq2 :
  'Auu____1862 .
    worklist ->
      FStar_TypeChecker_Env.env ->
        'Auu____1862 ->
          FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
            FStar_Syntax_Syntax.term -> (FStar_Syntax_Syntax.term * worklist)
  =
  fun wl  ->
    fun env  ->
      fun prob  ->
        fun t1  ->
          fun t2  ->
            let uu____1896 = FStar_Syntax_Util.type_u ()  in
            match uu____1896 with
            | (t_type,u) ->
                let binders = FStar_TypeChecker_Env.all_binders env  in
                let uu____1908 =
                  new_uvar "eq2" wl t1.FStar_Syntax_Syntax.pos
                    env.FStar_TypeChecker_Env.gamma binders t_type
                    FStar_Syntax_Syntax.Allow_unresolved
                    FStar_Pervasives_Native.None
                   in
                (match uu____1908 with
                 | (uu____1926,tt,wl1) ->
                     let uu____1929 = FStar_Syntax_Util.mk_eq2 u tt t1 t2  in
                     (uu____1929, wl1))
  
let (p_invert :
  FStar_TypeChecker_Common.prob -> FStar_TypeChecker_Common.prob) =
  fun uu___14_1935  ->
    match uu___14_1935 with
    | FStar_TypeChecker_Common.TProb p ->
        FStar_All.pipe_left
          (fun _1941  -> FStar_TypeChecker_Common.TProb _1941) (invert p)
    | FStar_TypeChecker_Common.CProb p ->
        FStar_All.pipe_left
          (fun _1947  -> FStar_TypeChecker_Common.CProb _1947) (invert p)
  
let (is_top_level_prob : FStar_TypeChecker_Common.prob -> Prims.bool) =
  fun p  ->
    let uu____1955 = FStar_All.pipe_right (p_reason p) FStar_List.length  in
    uu____1955 = Prims.int_one
  
let (next_pid : unit -> Prims.int) =
  let ctr = FStar_Util.mk_ref Prims.int_zero  in
  fun uu____1975  -> FStar_Util.incr ctr; FStar_ST.op_Bang ctr 
let mk_problem :
  'Auu____2017 .
    worklist ->
      (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.arg_qualifier
        FStar_Pervasives_Native.option) Prims.list ->
        FStar_TypeChecker_Common.prob ->
          'Auu____2017 ->
            FStar_TypeChecker_Common.rel ->
              'Auu____2017 ->
                FStar_Syntax_Syntax.bv FStar_Pervasives_Native.option ->
                  Prims.string ->
                    ('Auu____2017 FStar_TypeChecker_Common.problem *
                      worklist)
  =
  fun wl  ->
    fun scope  ->
      fun orig  ->
        fun lhs  ->
          fun rel  ->
            fun rhs  ->
              fun elt  ->
                fun reason  ->
                  let scope1 =
                    match elt with
                    | FStar_Pervasives_Native.None  -> scope
                    | FStar_Pervasives_Native.Some x ->
                        let uu____2104 =
                          let uu____2113 = FStar_Syntax_Syntax.mk_binder x
                             in
                          [uu____2113]  in
                        FStar_List.append scope uu____2104
                     in
                  let bs =
                    FStar_List.append
                      (p_guard_uvar orig).FStar_Syntax_Syntax.ctx_uvar_binders
                      scope1
                     in
                  let gamma =
                    let uu____2156 =
                      let uu____2159 =
                        FStar_List.map
                          (fun b  ->
                             FStar_Syntax_Syntax.Binding_var
                               (FStar_Pervasives_Native.fst b)) scope1
                         in
                      FStar_List.rev uu____2159  in
                    FStar_List.append uu____2156
                      (p_guard_uvar orig).FStar_Syntax_Syntax.ctx_uvar_gamma
                     in
                  let uu____2178 =
                    new_uvar
                      (Prims.op_Hat "mk_problem: logical guard for " reason)
                      wl FStar_Range.dummyRange gamma bs
                      FStar_Syntax_Util.ktype0
                      FStar_Syntax_Syntax.Allow_untyped
                      FStar_Pervasives_Native.None
                     in
                  match uu____2178 with
                  | (ctx_uvar,lg,wl1) ->
                      let prob =
                        let uu____2204 = next_pid ()  in
                        {
                          FStar_TypeChecker_Common.pid = uu____2204;
                          FStar_TypeChecker_Common.lhs = lhs;
                          FStar_TypeChecker_Common.relation = rel;
                          FStar_TypeChecker_Common.rhs = rhs;
                          FStar_TypeChecker_Common.element = elt;
                          FStar_TypeChecker_Common.logical_guard = lg;
                          FStar_TypeChecker_Common.logical_guard_uvar =
                            ctx_uvar;
                          FStar_TypeChecker_Common.reason = (reason ::
                            (p_reason orig));
                          FStar_TypeChecker_Common.loc = (p_loc orig);
                          FStar_TypeChecker_Common.rank =
                            FStar_Pervasives_Native.None
                        }  in
                      (prob, wl1)
  
let (mk_t_problem :
  worklist ->
    (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.arg_qualifier
      FStar_Pervasives_Native.option) Prims.list ->
      FStar_TypeChecker_Common.prob ->
        FStar_Syntax_Syntax.typ ->
          FStar_TypeChecker_Common.rel ->
            FStar_Syntax_Syntax.typ ->
              FStar_Syntax_Syntax.bv FStar_Pervasives_Native.option ->
                Prims.string -> (FStar_TypeChecker_Common.prob * worklist))
  =
  fun wl  ->
    fun scope  ->
      fun orig  ->
        fun lhs  ->
          fun rel  ->
            fun rhs  ->
              fun elt  ->
                fun reason  ->
                  def_check_prob (Prims.op_Hat reason ".mk_t.arg") orig;
                  (let uu____2278 =
                     mk_problem wl scope orig lhs rel rhs elt reason  in
                   match uu____2278 with
                   | (p,wl1) ->
                       (def_check_prob (Prims.op_Hat reason ".mk_t")
                          (FStar_TypeChecker_Common.TProb p);
                        ((FStar_TypeChecker_Common.TProb p), wl1)))
  
let (mk_c_problem :
  worklist ->
    (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.arg_qualifier
      FStar_Pervasives_Native.option) Prims.list ->
      FStar_TypeChecker_Common.prob ->
        FStar_Syntax_Syntax.comp ->
          FStar_TypeChecker_Common.rel ->
            FStar_Syntax_Syntax.comp ->
              FStar_Syntax_Syntax.bv FStar_Pervasives_Native.option ->
                Prims.string -> (FStar_TypeChecker_Common.prob * worklist))
  =
  fun wl  ->
    fun scope  ->
      fun orig  ->
        fun lhs  ->
          fun rel  ->
            fun rhs  ->
              fun elt  ->
                fun reason  ->
                  def_check_prob (Prims.op_Hat reason ".mk_c.arg") orig;
                  (let uu____2366 =
                     mk_problem wl scope orig lhs rel rhs elt reason  in
                   match uu____2366 with
                   | (p,wl1) ->
                       (def_check_prob (Prims.op_Hat reason ".mk_c")
                          (FStar_TypeChecker_Common.CProb p);
                        ((FStar_TypeChecker_Common.CProb p), wl1)))
  
let new_problem :
  'Auu____2404 .
    worklist ->
      FStar_TypeChecker_Env.env ->
        'Auu____2404 ->
          FStar_TypeChecker_Common.rel ->
            'Auu____2404 ->
              FStar_Syntax_Syntax.bv FStar_Pervasives_Native.option ->
                FStar_Range.range ->
                  Prims.string ->
                    ('Auu____2404 FStar_TypeChecker_Common.problem *
                      worklist)
  =
  fun wl  ->
    fun env  ->
      fun lhs  ->
        fun rel  ->
          fun rhs  ->
            fun subject  ->
              fun loc  ->
                fun reason  ->
                  let lg_ty =
                    match subject with
                    | FStar_Pervasives_Native.None  ->
                        FStar_Syntax_Util.ktype0
                    | FStar_Pervasives_Native.Some x ->
                        let bs =
                          let uu____2472 = FStar_Syntax_Syntax.mk_binder x
                             in
                          [uu____2472]  in
                        let uu____2491 =
                          FStar_Syntax_Syntax.mk_Total
                            FStar_Syntax_Util.ktype0
                           in
                        FStar_Syntax_Util.arrow bs uu____2491
                     in
                  let uu____2494 =
                    let uu____2501 = FStar_TypeChecker_Env.all_binders env
                       in
                    new_uvar
                      (Prims.op_Hat "new_problem: logical guard for " reason)
                      (let uu___350_2512 = wl  in
                       {
                         attempting = (uu___350_2512.attempting);
                         wl_deferred = (uu___350_2512.wl_deferred);
                         ctr = (uu___350_2512.ctr);
                         defer_ok = (uu___350_2512.defer_ok);
                         smt_ok = (uu___350_2512.smt_ok);
                         umax_heuristic_ok =
                           (uu___350_2512.umax_heuristic_ok);
                         tcenv = env;
                         wl_implicits = (uu___350_2512.wl_implicits)
                       }) loc env.FStar_TypeChecker_Env.gamma uu____2501
                      lg_ty FStar_Syntax_Syntax.Allow_untyped
                      FStar_Pervasives_Native.None
                     in
                  match uu____2494 with
                  | (ctx_uvar,lg,wl1) ->
                      let lg1 =
                        match subject with
                        | FStar_Pervasives_Native.None  -> lg
                        | FStar_Pervasives_Native.Some x ->
                            let uu____2530 =
                              let uu____2535 =
                                let uu____2536 =
                                  let uu____2545 =
                                    FStar_Syntax_Syntax.bv_to_name x  in
                                  FStar_All.pipe_left
                                    FStar_Syntax_Syntax.as_arg uu____2545
                                   in
                                [uu____2536]  in
                              FStar_Syntax_Syntax.mk_Tm_app lg uu____2535  in
                            uu____2530 FStar_Pervasives_Native.None loc
                         in
                      let prob =
                        let uu____2573 = next_pid ()  in
                        {
                          FStar_TypeChecker_Common.pid = uu____2573;
                          FStar_TypeChecker_Common.lhs = lhs;
                          FStar_TypeChecker_Common.relation = rel;
                          FStar_TypeChecker_Common.rhs = rhs;
                          FStar_TypeChecker_Common.element = subject;
                          FStar_TypeChecker_Common.logical_guard = lg1;
                          FStar_TypeChecker_Common.logical_guard_uvar =
                            ctx_uvar;
                          FStar_TypeChecker_Common.reason = [reason];
                          FStar_TypeChecker_Common.loc = loc;
                          FStar_TypeChecker_Common.rank =
                            FStar_Pervasives_Native.None
                        }  in
                      (prob, wl1)
  
let (problem_using_guard :
  FStar_TypeChecker_Common.prob ->
    FStar_Syntax_Syntax.typ ->
      FStar_TypeChecker_Common.rel ->
        FStar_Syntax_Syntax.typ ->
          FStar_Syntax_Syntax.bv FStar_Pervasives_Native.option ->
            Prims.string ->
              FStar_Syntax_Syntax.typ FStar_TypeChecker_Common.problem)
  =
  fun orig  ->
    fun lhs  ->
      fun rel  ->
        fun rhs  ->
          fun elt  ->
            fun reason  ->
              let p =
                let uu____2621 = next_pid ()  in
                {
                  FStar_TypeChecker_Common.pid = uu____2621;
                  FStar_TypeChecker_Common.lhs = lhs;
                  FStar_TypeChecker_Common.relation = rel;
                  FStar_TypeChecker_Common.rhs = rhs;
                  FStar_TypeChecker_Common.element = elt;
                  FStar_TypeChecker_Common.logical_guard = (p_guard orig);
                  FStar_TypeChecker_Common.logical_guard_uvar =
                    (p_guard_uvar orig);
                  FStar_TypeChecker_Common.reason = (reason ::
                    (p_reason orig));
                  FStar_TypeChecker_Common.loc = (p_loc orig);
                  FStar_TypeChecker_Common.rank =
                    FStar_Pervasives_Native.None
                }  in
              def_check_prob reason (FStar_TypeChecker_Common.TProb p); p
  
let guard_on_element :
  'Auu____2636 .
    worklist ->
      'Auu____2636 FStar_TypeChecker_Common.problem ->
        FStar_Syntax_Syntax.bv ->
          FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
            FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax
  =
  fun wl  ->
    fun problem  ->
      fun x  ->
        fun phi  ->
          match problem.FStar_TypeChecker_Common.element with
          | FStar_Pervasives_Native.None  ->
              let u =
                (wl.tcenv).FStar_TypeChecker_Env.universe_of wl.tcenv
                  x.FStar_Syntax_Syntax.sort
                 in
              FStar_Syntax_Util.mk_forall u x phi
          | FStar_Pervasives_Native.Some e ->
              let uu____2669 =
                let uu____2672 =
                  let uu____2673 =
                    let uu____2680 = FStar_Syntax_Syntax.bv_to_name e  in
                    (x, uu____2680)  in
                  FStar_Syntax_Syntax.NT uu____2673  in
                [uu____2672]  in
              FStar_Syntax_Subst.subst uu____2669 phi
  
let (explain :
  FStar_TypeChecker_Env.env ->
    FStar_TypeChecker_Common.prob -> lstring -> Prims.string)
  =
  fun env  ->
    fun d  ->
      fun s  ->
        let uu____2702 =
          (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
             (FStar_Options.Other "ExplainRel"))
            ||
            (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
               (FStar_Options.Other "Rel"))
           in
        if uu____2702
        then
          let uu____2710 =
            FStar_All.pipe_left FStar_Range.string_of_range (p_loc d)  in
          let uu____2713 = prob_to_string env d  in
          let uu____2715 =
            FStar_All.pipe_right (p_reason d) (FStar_String.concat "\n\t>")
             in
          let uu____2722 = FStar_Thunk.force s  in
          FStar_Util.format4
            "(%s) Failed to solve the sub-problem\n%s\nWhich arose because:\n\t%s\nFailed because:%s\n"
            uu____2710 uu____2713 uu____2715 uu____2722
        else
          (let d1 = maybe_invert_p d  in
           let rel =
             match p_rel d1 with
             | FStar_TypeChecker_Common.EQ  -> "equal to"
             | FStar_TypeChecker_Common.SUB  -> "a subtype of"
             | uu____2734 -> failwith "impossible"  in
           let uu____2737 =
             match d1 with
             | FStar_TypeChecker_Common.TProb tp ->
                 let uu____2753 =
                   FStar_TypeChecker_Normalize.term_to_string env
                     tp.FStar_TypeChecker_Common.lhs
                    in
                 let uu____2755 =
                   FStar_TypeChecker_Normalize.term_to_string env
                     tp.FStar_TypeChecker_Common.rhs
                    in
                 (uu____2753, uu____2755)
             | FStar_TypeChecker_Common.CProb cp ->
                 let uu____2762 =
                   FStar_TypeChecker_Normalize.comp_to_string env
                     cp.FStar_TypeChecker_Common.lhs
                    in
                 let uu____2764 =
                   FStar_TypeChecker_Normalize.comp_to_string env
                     cp.FStar_TypeChecker_Common.rhs
                    in
                 (uu____2762, uu____2764)
              in
           match uu____2737 with
           | (lhs,rhs) ->
               FStar_Util.format3 "%s is not %s the expected type %s" lhs rel
                 rhs)
  
let (commit : uvi Prims.list -> unit) =
  fun uvis  ->
    FStar_All.pipe_right uvis
      (FStar_List.iter
         (fun uu___15_2792  ->
            match uu___15_2792 with
            | UNIV (u,t) ->
                (match t with
                 | FStar_Syntax_Syntax.U_unif u' ->
                     FStar_Syntax_Unionfind.univ_union u u'
                 | uu____2804 -> FStar_Syntax_Unionfind.univ_change u t)
            | TERM (u,t) ->
                ((let uu____2808 =
                    FStar_List.map FStar_Pervasives_Native.fst
                      u.FStar_Syntax_Syntax.ctx_uvar_binders
                     in
                  FStar_TypeChecker_Env.def_check_closed_in
                    t.FStar_Syntax_Syntax.pos "commit" uu____2808 t);
                 FStar_Syntax_Util.set_uvar
                   u.FStar_Syntax_Syntax.ctx_uvar_head t)))
  
let (find_term_uvar :
  FStar_Syntax_Syntax.uvar ->
    uvi Prims.list -> FStar_Syntax_Syntax.term FStar_Pervasives_Native.option)
  =
  fun uv  ->
    fun s  ->
      FStar_Util.find_map s
        (fun uu___16_2839  ->
           match uu___16_2839 with
           | UNIV uu____2842 -> FStar_Pervasives_Native.None
           | TERM (u,t) ->
               let uu____2849 =
                 FStar_Syntax_Unionfind.equiv uv
                   u.FStar_Syntax_Syntax.ctx_uvar_head
                  in
               if uu____2849
               then FStar_Pervasives_Native.Some t
               else FStar_Pervasives_Native.None)
  
let (find_univ_uvar :
  FStar_Syntax_Syntax.universe_uvar ->
    uvi Prims.list ->
      FStar_Syntax_Syntax.universe FStar_Pervasives_Native.option)
  =
  fun u  ->
    fun s  ->
      FStar_Util.find_map s
        (fun uu___17_2877  ->
           match uu___17_2877 with
           | UNIV (u',t) ->
               let uu____2882 = FStar_Syntax_Unionfind.univ_equiv u u'  in
               if uu____2882
               then FStar_Pervasives_Native.Some t
               else FStar_Pervasives_Native.None
           | uu____2889 -> FStar_Pervasives_Native.None)
  
let (whnf' :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term)
  =
  fun env  ->
    fun t  ->
      let uu____2901 =
        let uu____2902 =
          let uu____2903 = FStar_Syntax_Util.unmeta t  in
          FStar_TypeChecker_Normalize.normalize
            [FStar_TypeChecker_Env.Beta;
            FStar_TypeChecker_Env.Reify;
            FStar_TypeChecker_Env.Weak;
            FStar_TypeChecker_Env.HNF] env uu____2903
           in
        FStar_Syntax_Subst.compress uu____2902  in
      FStar_All.pipe_right uu____2901 FStar_Syntax_Util.unlazy_emb
  
let (sn :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term)
  =
  fun env  ->
    fun t  ->
      let uu____2915 =
        let uu____2916 =
          FStar_TypeChecker_Normalize.normalize
            [FStar_TypeChecker_Env.Beta; FStar_TypeChecker_Env.Reify] env t
           in
        FStar_Syntax_Subst.compress uu____2916  in
      FStar_All.pipe_right uu____2915 FStar_Syntax_Util.unlazy_emb
  
let (should_strongly_reduce : FStar_Syntax_Syntax.term -> Prims.bool) =
  fun t  ->
    let uu____2924 = FStar_Syntax_Util.head_and_args t  in
    match uu____2924 with
    | (h,uu____2943) ->
        let uu____2968 =
          let uu____2969 = FStar_Syntax_Subst.compress h  in
          uu____2969.FStar_Syntax_Syntax.n  in
        (match uu____2968 with
         | FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_reify ) -> true
         | uu____2974 -> false)
  
let (whnf :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term)
  =
  fun env  ->
    fun t  ->
      let uu____2987 = should_strongly_reduce t  in
      if uu____2987
      then
        let uu____2990 =
          let uu____2991 =
            FStar_TypeChecker_Normalize.normalize
              [FStar_TypeChecker_Env.Beta;
              FStar_TypeChecker_Env.Reify;
              FStar_TypeChecker_Env.Exclude FStar_TypeChecker_Env.Zeta;
              FStar_TypeChecker_Env.UnfoldUntil
                FStar_Syntax_Syntax.delta_constant] env t
             in
          FStar_Syntax_Subst.compress uu____2991  in
        FStar_All.pipe_right uu____2990 FStar_Syntax_Util.unlazy_emb
      else whnf' env t
  
let norm_arg :
  'Auu____3001 .
    FStar_TypeChecker_Env.env ->
      (FStar_Syntax_Syntax.term * 'Auu____3001) ->
        (FStar_Syntax_Syntax.term * 'Auu____3001)
  =
  fun env  ->
    fun t  ->
      let uu____3024 = sn env (FStar_Pervasives_Native.fst t)  in
      (uu____3024, (FStar_Pervasives_Native.snd t))
  
let (sn_binders :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.binders ->
      (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.arg_qualifier
        FStar_Pervasives_Native.option) Prims.list)
  =
  fun env  ->
    fun binders  ->
      FStar_All.pipe_right binders
        (FStar_List.map
           (fun uu____3076  ->
              match uu____3076 with
              | (x,imp) ->
                  let uu____3095 =
                    let uu___447_3096 = x  in
                    let uu____3097 = sn env x.FStar_Syntax_Syntax.sort  in
                    {
                      FStar_Syntax_Syntax.ppname =
                        (uu___447_3096.FStar_Syntax_Syntax.ppname);
                      FStar_Syntax_Syntax.index =
                        (uu___447_3096.FStar_Syntax_Syntax.index);
                      FStar_Syntax_Syntax.sort = uu____3097
                    }  in
                  (uu____3095, imp)))
  
let (norm_univ :
  worklist -> FStar_Syntax_Syntax.universe -> FStar_Syntax_Syntax.universe) =
  fun wl  ->
    fun u  ->
      let rec aux u1 =
        let u2 = FStar_Syntax_Subst.compress_univ u1  in
        match u2 with
        | FStar_Syntax_Syntax.U_succ u3 ->
            let uu____3121 = aux u3  in FStar_Syntax_Syntax.U_succ uu____3121
        | FStar_Syntax_Syntax.U_max us ->
            let uu____3125 = FStar_List.map aux us  in
            FStar_Syntax_Syntax.U_max uu____3125
        | uu____3128 -> u2  in
      let uu____3129 = aux u  in
      FStar_TypeChecker_Normalize.normalize_universe wl.tcenv uu____3129
  
let (base_and_refinement_maybe_delta :
  Prims.bool ->
    FStar_TypeChecker_Env.env ->
      FStar_Syntax_Syntax.term ->
        (FStar_Syntax_Syntax.term * (FStar_Syntax_Syntax.bv *
          FStar_Syntax_Syntax.term) FStar_Pervasives_Native.option))
  =
  fun should_delta  ->
    fun env  ->
      fun t1  ->
        let norm_refinement env1 t =
          let steps =
            if should_delta
            then
              [FStar_TypeChecker_Env.Weak;
              FStar_TypeChecker_Env.HNF;
              FStar_TypeChecker_Env.UnfoldUntil
                FStar_Syntax_Syntax.delta_constant]
            else [FStar_TypeChecker_Env.Weak; FStar_TypeChecker_Env.HNF]  in
          FStar_TypeChecker_Normalize.normalize_refinement steps env1 t  in
        let rec aux norm1 t11 =
          let t12 = FStar_Syntax_Util.unmeta t11  in
          match t12.FStar_Syntax_Syntax.n with
          | FStar_Syntax_Syntax.Tm_refine (x,phi) ->
              if norm1
              then
                ((x.FStar_Syntax_Syntax.sort),
                  (FStar_Pervasives_Native.Some (x, phi)))
              else
                (let uu____3250 = norm_refinement env t12  in
                 match uu____3250 with
                 | {
                     FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_refine
                       (x1,phi1);
                     FStar_Syntax_Syntax.pos = uu____3265;
                     FStar_Syntax_Syntax.vars = uu____3266;_} ->
                     ((x1.FStar_Syntax_Syntax.sort),
                       (FStar_Pervasives_Native.Some (x1, phi1)))
                 | tt ->
                     let uu____3290 =
                       let uu____3292 = FStar_Syntax_Print.term_to_string tt
                          in
                       let uu____3294 = FStar_Syntax_Print.tag_of_term tt  in
                       FStar_Util.format2 "impossible: Got %s ... %s\n"
                         uu____3292 uu____3294
                        in
                     failwith uu____3290)
          | FStar_Syntax_Syntax.Tm_lazy i ->
              let uu____3310 = FStar_Syntax_Util.unfold_lazy i  in
              aux norm1 uu____3310
          | FStar_Syntax_Syntax.Tm_uinst uu____3311 ->
              if norm1
              then (t12, FStar_Pervasives_Native.None)
              else
                (let t1' = norm_refinement env t12  in
                 let uu____3348 =
                   let uu____3349 = FStar_Syntax_Subst.compress t1'  in
                   uu____3349.FStar_Syntax_Syntax.n  in
                 match uu____3348 with
                 | FStar_Syntax_Syntax.Tm_refine uu____3364 -> aux true t1'
                 | uu____3372 -> (t12, FStar_Pervasives_Native.None))
          | FStar_Syntax_Syntax.Tm_fvar uu____3387 ->
              if norm1
              then (t12, FStar_Pervasives_Native.None)
              else
                (let t1' = norm_refinement env t12  in
                 let uu____3418 =
                   let uu____3419 = FStar_Syntax_Subst.compress t1'  in
                   uu____3419.FStar_Syntax_Syntax.n  in
                 match uu____3418 with
                 | FStar_Syntax_Syntax.Tm_refine uu____3434 -> aux true t1'
                 | uu____3442 -> (t12, FStar_Pervasives_Native.None))
          | FStar_Syntax_Syntax.Tm_app uu____3457 ->
              if norm1
              then (t12, FStar_Pervasives_Native.None)
              else
                (let t1' = norm_refinement env t12  in
                 let uu____3504 =
                   let uu____3505 = FStar_Syntax_Subst.compress t1'  in
                   uu____3505.FStar_Syntax_Syntax.n  in
                 match uu____3504 with
                 | FStar_Syntax_Syntax.Tm_refine uu____3520 -> aux true t1'
                 | uu____3528 -> (t12, FStar_Pervasives_Native.None))
          | FStar_Syntax_Syntax.Tm_type uu____3543 ->
              (t12, FStar_Pervasives_Native.None)
          | FStar_Syntax_Syntax.Tm_constant uu____3558 ->
              (t12, FStar_Pervasives_Native.None)
          | FStar_Syntax_Syntax.Tm_name uu____3573 ->
              (t12, FStar_Pervasives_Native.None)
          | FStar_Syntax_Syntax.Tm_bvar uu____3588 ->
              (t12, FStar_Pervasives_Native.None)
          | FStar_Syntax_Syntax.Tm_arrow uu____3603 ->
              (t12, FStar_Pervasives_Native.None)
          | FStar_Syntax_Syntax.Tm_abs uu____3632 ->
              (t12, FStar_Pervasives_Native.None)
          | FStar_Syntax_Syntax.Tm_quoted uu____3665 ->
              (t12, FStar_Pervasives_Native.None)
          | FStar_Syntax_Syntax.Tm_uvar uu____3686 ->
              (t12, FStar_Pervasives_Native.None)
          | FStar_Syntax_Syntax.Tm_let uu____3713 ->
              (t12, FStar_Pervasives_Native.None)
          | FStar_Syntax_Syntax.Tm_match uu____3741 ->
              (t12, FStar_Pervasives_Native.None)
          | FStar_Syntax_Syntax.Tm_meta uu____3778 ->
              let uu____3785 =
                let uu____3787 = FStar_Syntax_Print.term_to_string t12  in
                let uu____3789 = FStar_Syntax_Print.tag_of_term t12  in
                FStar_Util.format2 "impossible (outer): Got %s ... %s\n"
                  uu____3787 uu____3789
                 in
              failwith uu____3785
          | FStar_Syntax_Syntax.Tm_ascribed uu____3804 ->
              let uu____3831 =
                let uu____3833 = FStar_Syntax_Print.term_to_string t12  in
                let uu____3835 = FStar_Syntax_Print.tag_of_term t12  in
                FStar_Util.format2 "impossible (outer): Got %s ... %s\n"
                  uu____3833 uu____3835
                 in
              failwith uu____3831
          | FStar_Syntax_Syntax.Tm_delayed uu____3850 ->
              let uu____3865 =
                let uu____3867 = FStar_Syntax_Print.term_to_string t12  in
                let uu____3869 = FStar_Syntax_Print.tag_of_term t12  in
                FStar_Util.format2 "impossible (outer): Got %s ... %s\n"
                  uu____3867 uu____3869
                 in
              failwith uu____3865
          | FStar_Syntax_Syntax.Tm_unknown  ->
              let uu____3884 =
                let uu____3886 = FStar_Syntax_Print.term_to_string t12  in
                let uu____3888 = FStar_Syntax_Print.tag_of_term t12  in
                FStar_Util.format2 "impossible (outer): Got %s ... %s\n"
                  uu____3886 uu____3888
                 in
              failwith uu____3884
           in
        let uu____3903 = whnf env t1  in aux false uu____3903
  
let (base_and_refinement :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term ->
      (FStar_Syntax_Syntax.term * (FStar_Syntax_Syntax.bv *
        FStar_Syntax_Syntax.term) FStar_Pervasives_Native.option))
  = fun env  -> fun t  -> base_and_refinement_maybe_delta false env t 
let (normalize_refinement :
  FStar_TypeChecker_Env.steps ->
    FStar_TypeChecker_Env.env ->
      FStar_Syntax_Syntax.typ -> FStar_Syntax_Syntax.term)
  =
  fun steps  ->
    fun env  ->
      fun t0  ->
        FStar_TypeChecker_Normalize.normalize_refinement steps env t0
  
let (unrefine :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.typ -> FStar_Syntax_Syntax.typ)
  =
  fun env  ->
    fun t  ->
      let uu____3964 = base_and_refinement env t  in
      FStar_All.pipe_right uu____3964 FStar_Pervasives_Native.fst
  
let (trivial_refinement :
  FStar_Syntax_Syntax.term ->
    (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.term))
  =
  fun t  ->
    let uu____4005 = FStar_Syntax_Syntax.null_bv t  in
    (uu____4005, FStar_Syntax_Util.t_true)
  
let (as_refinement :
  Prims.bool ->
    FStar_TypeChecker_Env.env ->
      FStar_Syntax_Syntax.term ->
        (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.term))
  =
  fun delta1  ->
    fun env  ->
      fun t  ->
        let uu____4032 = base_and_refinement_maybe_delta delta1 env t  in
        match uu____4032 with
        | (t_base,refinement) ->
            (match refinement with
             | FStar_Pervasives_Native.None  -> trivial_refinement t_base
             | FStar_Pervasives_Native.Some (x,phi) -> (x, phi))
  
let (force_refinement :
  (FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax *
    (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.term)
    FStar_Pervasives_Native.option) -> FStar_Syntax_Syntax.term)
  =
  fun uu____4092  ->
    match uu____4092 with
    | (t_base,refopt) ->
        let uu____4123 =
          match refopt with
          | FStar_Pervasives_Native.Some (y,phi) -> (y, phi)
          | FStar_Pervasives_Native.None  -> trivial_refinement t_base  in
        (match uu____4123 with
         | (y,phi) ->
             FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_refine (y, phi))
               FStar_Pervasives_Native.None t_base.FStar_Syntax_Syntax.pos)
  
let (wl_prob_to_string :
  worklist -> FStar_TypeChecker_Common.prob -> Prims.string) =
  fun wl  -> fun prob  -> prob_to_string wl.tcenv prob 
let (wl_to_string : worklist -> Prims.string) =
  fun wl  ->
    let uu____4165 =
      let uu____4169 =
        let uu____4172 =
          FStar_All.pipe_right wl.wl_deferred
            (FStar_List.map
               (fun uu____4197  ->
                  match uu____4197 with | (uu____4205,uu____4206,x) -> x))
           in
        FStar_List.append wl.attempting uu____4172  in
      FStar_List.map (wl_prob_to_string wl) uu____4169  in
    FStar_All.pipe_right uu____4165 (FStar_String.concat "\n\t")
  
type flex_t =
  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.ctx_uvar *
    FStar_Syntax_Syntax.args)
let flex_t_to_string :
  'Auu____4227 .
    ('Auu____4227 * FStar_Syntax_Syntax.ctx_uvar * FStar_Syntax_Syntax.args)
      -> Prims.string
  =
  fun uu____4239  ->
    match uu____4239 with
    | (uu____4246,c,args) ->
        let uu____4249 = print_ctx_uvar c  in
        let uu____4251 = FStar_Syntax_Print.args_to_string args  in
        FStar_Util.format2 "%s [%s]" uu____4249 uu____4251
  
let (is_flex : FStar_Syntax_Syntax.term -> Prims.bool) =
  fun t  ->
    let uu____4261 = FStar_Syntax_Util.head_and_args t  in
    match uu____4261 with
    | (head1,_args) ->
        let uu____4305 =
          let uu____4306 = FStar_Syntax_Subst.compress head1  in
          uu____4306.FStar_Syntax_Syntax.n  in
        (match uu____4305 with
         | FStar_Syntax_Syntax.Tm_uvar uu____4310 -> true
         | uu____4324 -> false)
  
let (flex_uvar_head :
  FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.ctx_uvar) =
  fun t  ->
    let uu____4332 = FStar_Syntax_Util.head_and_args t  in
    match uu____4332 with
    | (head1,_args) ->
        let uu____4375 =
          let uu____4376 = FStar_Syntax_Subst.compress head1  in
          uu____4376.FStar_Syntax_Syntax.n  in
        (match uu____4375 with
         | FStar_Syntax_Syntax.Tm_uvar (u,uu____4380) -> u
         | uu____4397 -> failwith "Not a flex-uvar")
  
let (destruct_flex_t :
  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
    worklist -> (flex_t * worklist))
  =
  fun t  ->
    fun wl  ->
      let uu____4422 = FStar_Syntax_Util.head_and_args t  in
      match uu____4422 with
      | (head1,args) ->
          let uu____4469 =
            let uu____4470 = FStar_Syntax_Subst.compress head1  in
            uu____4470.FStar_Syntax_Syntax.n  in
          (match uu____4469 with
           | FStar_Syntax_Syntax.Tm_uvar (uv,([],uu____4478)) ->
               ((t, uv, args), wl)
           | FStar_Syntax_Syntax.Tm_uvar (uv,s) ->
               let uu____4511 =
                 FStar_All.pipe_right uv.FStar_Syntax_Syntax.ctx_uvar_gamma
                   (FStar_List.partition
                      (fun uu___18_4536  ->
                         match uu___18_4536 with
                         | FStar_Syntax_Syntax.Binding_var x ->
                             let t_x = FStar_Syntax_Syntax.bv_to_name x  in
                             let t_x' = FStar_Syntax_Subst.subst' s t_x  in
                             let uu____4541 =
                               let uu____4542 =
                                 FStar_Syntax_Subst.compress t_x'  in
                               uu____4542.FStar_Syntax_Syntax.n  in
                             (match uu____4541 with
                              | FStar_Syntax_Syntax.Tm_name y ->
                                  FStar_Syntax_Syntax.bv_eq x y
                              | uu____4547 -> false)
                         | uu____4549 -> true))
                  in
               (match uu____4511 with
                | (new_gamma,dom_binders_rev) ->
                    let dom_binders =
                      let uu____4574 =
                        FStar_List.collect
                          (fun uu___19_4586  ->
                             match uu___19_4586 with
                             | FStar_Syntax_Syntax.Binding_var x ->
                                 let uu____4590 =
                                   FStar_Syntax_Syntax.mk_binder x  in
                                 [uu____4590]
                             | uu____4591 -> []) dom_binders_rev
                         in
                      FStar_All.pipe_right uu____4574 FStar_List.rev  in
                    let uu____4614 =
                      let uu____4621 =
                        let uu____4630 =
                          FStar_All.pipe_right new_gamma
                            (FStar_List.collect
                               (fun uu___20_4652  ->
                                  match uu___20_4652 with
                                  | FStar_Syntax_Syntax.Binding_var x ->
                                      let uu____4656 =
                                        FStar_Syntax_Syntax.mk_binder x  in
                                      [uu____4656]
                                  | uu____4657 -> []))
                           in
                        FStar_All.pipe_right uu____4630 FStar_List.rev  in
                      let uu____4680 =
                        let uu____4683 =
                          FStar_Syntax_Syntax.mk_Total
                            uv.FStar_Syntax_Syntax.ctx_uvar_typ
                           in
                        FStar_Syntax_Util.arrow dom_binders uu____4683  in
                      new_uvar
                        (Prims.op_Hat uv.FStar_Syntax_Syntax.ctx_uvar_reason
                           "; force delayed") wl t.FStar_Syntax_Syntax.pos
                        new_gamma uu____4621 uu____4680
                        uv.FStar_Syntax_Syntax.ctx_uvar_should_check
                        uv.FStar_Syntax_Syntax.ctx_uvar_meta
                       in
                    (match uu____4614 with
                     | (v1,t_v,wl1) ->
                         let args_sol =
                           FStar_List.map
                             (fun uu____4719  ->
                                match uu____4719 with
                                | (x,i) ->
                                    let uu____4738 =
                                      FStar_Syntax_Syntax.bv_to_name x  in
                                    (uu____4738, i)) dom_binders
                            in
                         let sol =
                           FStar_Syntax_Syntax.mk_Tm_app t_v args_sol
                             FStar_Pervasives_Native.None
                             t.FStar_Syntax_Syntax.pos
                            in
                         let args_sol_s =
                           FStar_List.map
                             (fun uu____4769  ->
                                match uu____4769 with
                                | (a,i) ->
                                    let uu____4788 =
                                      FStar_Syntax_Subst.subst' s a  in
                                    (uu____4788, i)) args_sol
                            in
                         let all_args = FStar_List.append args_sol_s args  in
                         let t1 =
                           FStar_Syntax_Syntax.mk_Tm_app t_v all_args
                             FStar_Pervasives_Native.None
                             t.FStar_Syntax_Syntax.pos
                            in
                         (FStar_Syntax_Unionfind.change
                            uv.FStar_Syntax_Syntax.ctx_uvar_head sol;
                          ((t1, v1, all_args), wl1))))
           | uu____4810 -> failwith "Not a flex-uvar")
  
let (u_abs :
  FStar_Syntax_Syntax.typ ->
    FStar_Syntax_Syntax.binders ->
      FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term)
  =
  fun k  ->
    fun ys  ->
      fun t  ->
        let uu____4832 =
          let uu____4855 =
            let uu____4856 = FStar_Syntax_Subst.compress k  in
            uu____4856.FStar_Syntax_Syntax.n  in
          match uu____4855 with
          | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
              if (FStar_List.length bs) = (FStar_List.length ys)
              then
                let uu____4938 = FStar_Syntax_Subst.open_comp bs c  in
                ((ys, t), uu____4938)
              else
                (let uu____4973 = FStar_Syntax_Util.abs_formals t  in
                 match uu____4973 with
                 | (ys',t1,uu____5006) ->
                     let uu____5011 = FStar_Syntax_Util.arrow_formals_comp k
                        in
                     (((FStar_List.append ys ys'), t1), uu____5011))
          | uu____5050 ->
              let uu____5051 =
                let uu____5056 = FStar_Syntax_Syntax.mk_Total k  in
                ([], uu____5056)  in
              ((ys, t), uu____5051)
           in
        match uu____4832 with
        | ((ys1,t1),(xs,c)) ->
            if (FStar_List.length xs) <> (FStar_List.length ys1)
            then
              FStar_Syntax_Util.abs ys1 t1
                (FStar_Pervasives_Native.Some
                   (FStar_Syntax_Util.mk_residual_comp
                      FStar_Parser_Const.effect_Tot_lid
                      FStar_Pervasives_Native.None []))
            else
              (let c1 =
                 let uu____5151 = FStar_Syntax_Util.rename_binders xs ys1  in
                 FStar_Syntax_Subst.subst_comp uu____5151 c  in
               FStar_Syntax_Util.abs ys1 t1
                 (FStar_Pervasives_Native.Some
                    (FStar_Syntax_Util.residual_comp_of_comp c1)))
  
let (solve_prob' :
  Prims.bool ->
    FStar_TypeChecker_Common.prob ->
      FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax
        FStar_Pervasives_Native.option ->
        uvi Prims.list -> worklist -> worklist)
  =
  fun resolve_ok  ->
    fun prob  ->
      fun logical_guard  ->
        fun uvis  ->
          fun wl  ->
            def_check_prob "solve_prob'" prob;
            (let phi =
               match logical_guard with
               | FStar_Pervasives_Native.None  -> FStar_Syntax_Util.t_true
               | FStar_Pervasives_Native.Some phi -> phi  in
             let assign_solution xs uv phi1 =
               (let uu____5229 =
                  FStar_All.pipe_left (FStar_TypeChecker_Env.debug wl.tcenv)
                    (FStar_Options.Other "Rel")
                   in
                if uu____5229
                then
                  let uu____5234 = FStar_Util.string_of_int (p_pid prob)  in
                  let uu____5236 = print_ctx_uvar uv  in
                  let uu____5238 = FStar_Syntax_Print.term_to_string phi1  in
                  FStar_Util.print3 "Solving %s (%s) with formula %s\n"
                    uu____5234 uu____5236 uu____5238
                else ());
               (let phi2 =
                  FStar_Syntax_Util.abs xs phi1
                    (FStar_Pervasives_Native.Some
                       (FStar_Syntax_Util.residual_tot
                          FStar_Syntax_Util.ktype0))
                   in
                (let uu____5247 =
                   let uu____5249 = FStar_Util.string_of_int (p_pid prob)  in
                   Prims.op_Hat "solve_prob'.sol." uu____5249  in
                 let uu____5252 =
                   let uu____5255 = p_scope prob  in
                   FStar_All.pipe_left
                     (FStar_List.map FStar_Pervasives_Native.fst) uu____5255
                    in
                 FStar_TypeChecker_Env.def_check_closed_in (p_loc prob)
                   uu____5247 uu____5252 phi2);
                FStar_Syntax_Util.set_uvar
                  uv.FStar_Syntax_Syntax.ctx_uvar_head phi2)
                in
             let uv = p_guard_uvar prob  in
             let fail1 uu____5288 =
               let uu____5289 =
                 let uu____5291 = FStar_Syntax_Print.ctx_uvar_to_string uv
                    in
                 let uu____5293 =
                   FStar_Syntax_Print.term_to_string (p_guard prob)  in
                 FStar_Util.format2
                   "Impossible: this instance %s has already been assigned a solution\n%s\n"
                   uu____5291 uu____5293
                  in
               failwith uu____5289  in
             let args_as_binders args =
               FStar_All.pipe_right args
                 (FStar_List.collect
                    (fun uu____5359  ->
                       match uu____5359 with
                       | (a,i) ->
                           let uu____5380 =
                             let uu____5381 = FStar_Syntax_Subst.compress a
                                in
                             uu____5381.FStar_Syntax_Syntax.n  in
                           (match uu____5380 with
                            | FStar_Syntax_Syntax.Tm_name x -> [(x, i)]
                            | uu____5407 -> (fail1 (); []))))
                in
             let wl1 =
               let g = whnf wl.tcenv (p_guard prob)  in
               let uu____5417 =
                 let uu____5419 = is_flex g  in Prims.op_Negation uu____5419
                  in
               if uu____5417
               then (if resolve_ok then wl else (fail1 (); wl))
               else
                 (let uu____5428 = destruct_flex_t g wl  in
                  match uu____5428 with
                  | ((uu____5433,uv1,args),wl1) ->
                      ((let uu____5438 = args_as_binders args  in
                        assign_solution uu____5438 uv1 phi);
                       wl1))
                in
             commit uvis;
             (let uu___699_5440 = wl1  in
              {
                attempting = (uu___699_5440.attempting);
                wl_deferred = (uu___699_5440.wl_deferred);
                ctr = (wl1.ctr + Prims.int_one);
                defer_ok = (uu___699_5440.defer_ok);
                smt_ok = (uu___699_5440.smt_ok);
                umax_heuristic_ok = (uu___699_5440.umax_heuristic_ok);
                tcenv = (uu___699_5440.tcenv);
                wl_implicits = (uu___699_5440.wl_implicits)
              }))
  
let (extend_solution : Prims.int -> uvi Prims.list -> worklist -> worklist) =
  fun pid  ->
    fun sol  ->
      fun wl  ->
        (let uu____5465 =
           FStar_All.pipe_left (FStar_TypeChecker_Env.debug wl.tcenv)
             (FStar_Options.Other "Rel")
            in
         if uu____5465
         then
           let uu____5470 = FStar_Util.string_of_int pid  in
           let uu____5472 =
             let uu____5474 = FStar_List.map (uvi_to_string wl.tcenv) sol  in
             FStar_All.pipe_right uu____5474 (FStar_String.concat ", ")  in
           FStar_Util.print2 "Solving %s: with [%s]\n" uu____5470 uu____5472
         else ());
        commit sol;
        (let uu___707_5488 = wl  in
         {
           attempting = (uu___707_5488.attempting);
           wl_deferred = (uu___707_5488.wl_deferred);
           ctr = (wl.ctr + Prims.int_one);
           defer_ok = (uu___707_5488.defer_ok);
           smt_ok = (uu___707_5488.smt_ok);
           umax_heuristic_ok = (uu___707_5488.umax_heuristic_ok);
           tcenv = (uu___707_5488.tcenv);
           wl_implicits = (uu___707_5488.wl_implicits)
         })
  
let (solve_prob :
  FStar_TypeChecker_Common.prob ->
    FStar_Syntax_Syntax.term FStar_Pervasives_Native.option ->
      uvi Prims.list -> worklist -> worklist)
  =
  fun prob  ->
    fun logical_guard  ->
      fun uvis  ->
        fun wl  ->
          def_check_prob "solve_prob.prob" prob;
          FStar_Util.iter_opt logical_guard
            (def_check_scoped "solve_prob.guard" prob);
          (let conj_guard1 t g =
             match (t, g) with
             | (uu____5554,FStar_TypeChecker_Common.Trivial ) -> t
             | (FStar_Pervasives_Native.None
                ,FStar_TypeChecker_Common.NonTrivial f) ->
                 FStar_Pervasives_Native.Some f
             | (FStar_Pervasives_Native.Some
                t1,FStar_TypeChecker_Common.NonTrivial f) ->
                 let uu____5582 = FStar_Syntax_Util.mk_conj t1 f  in
                 FStar_Pervasives_Native.Some uu____5582
              in
           (let uu____5588 =
              FStar_All.pipe_left (FStar_TypeChecker_Env.debug wl.tcenv)
                (FStar_Options.Other "Rel")
               in
            if uu____5588
            then
              let uu____5593 =
                FStar_All.pipe_left FStar_Util.string_of_int (p_pid prob)  in
              let uu____5597 =
                let uu____5599 = FStar_List.map (uvi_to_string wl.tcenv) uvis
                   in
                FStar_All.pipe_right uu____5599 (FStar_String.concat ", ")
                 in
              FStar_Util.print2 "Solving %s: with %s\n" uu____5593 uu____5597
            else ());
           solve_prob' false prob logical_guard uvis wl)
  
let (occurs :
  FStar_Syntax_Syntax.ctx_uvar ->
    FStar_Syntax_Syntax.term ->
      (FStar_Syntax_Syntax.ctx_uvar Prims.list * Prims.bool))
  =
  fun uk  ->
    fun t  ->
      let uvars1 =
        let uu____5634 = FStar_Syntax_Free.uvars t  in
        FStar_All.pipe_right uu____5634 FStar_Util.set_elements  in
      let occurs =
        FStar_All.pipe_right uvars1
          (FStar_Util.for_some
             (fun uv  ->
                FStar_Syntax_Unionfind.equiv
                  uv.FStar_Syntax_Syntax.ctx_uvar_head
                  uk.FStar_Syntax_Syntax.ctx_uvar_head))
         in
      (uvars1, occurs)
  
let (occurs_check :
  FStar_Syntax_Syntax.ctx_uvar ->
    FStar_Syntax_Syntax.term ->
      (FStar_Syntax_Syntax.ctx_uvar Prims.list * Prims.bool * Prims.string
        FStar_Pervasives_Native.option))
  =
  fun uk  ->
    fun t  ->
      let uu____5674 = occurs uk t  in
      match uu____5674 with
      | (uvars1,occurs1) ->
          let msg =
            if Prims.op_Negation occurs1
            then FStar_Pervasives_Native.None
            else
              (let uu____5713 =
                 let uu____5715 =
                   FStar_Syntax_Print.uvar_to_string
                     uk.FStar_Syntax_Syntax.ctx_uvar_head
                    in
                 let uu____5717 = FStar_Syntax_Print.term_to_string t  in
                 FStar_Util.format2 "occurs-check failed (%s occurs in %s)"
                   uu____5715 uu____5717
                  in
               FStar_Pervasives_Native.Some uu____5713)
             in
          (uvars1, (Prims.op_Negation occurs1), msg)
  
let rec (maximal_prefix :
  FStar_Syntax_Syntax.binders ->
    FStar_Syntax_Syntax.binders ->
      (FStar_Syntax_Syntax.binders * (FStar_Syntax_Syntax.binders *
        FStar_Syntax_Syntax.binders)))
  =
  fun bs  ->
    fun bs'  ->
      match (bs, bs') with
      | ((b,i)::bs_tail,(b',i')::bs'_tail) ->
          if FStar_Syntax_Syntax.bv_eq b b'
          then
            let uu____5837 = maximal_prefix bs_tail bs'_tail  in
            (match uu____5837 with | (pfx,rest) -> (((b, i) :: pfx), rest))
          else ([], (bs, bs'))
      | uu____5888 -> ([], (bs, bs'))
  
let (extend_gamma :
  FStar_Syntax_Syntax.gamma ->
    FStar_Syntax_Syntax.binders -> FStar_Syntax_Syntax.binding Prims.list)
  =
  fun g  ->
    fun bs  ->
      FStar_List.fold_left
        (fun g1  ->
           fun uu____5945  ->
             match uu____5945 with
             | (x,uu____5957) -> (FStar_Syntax_Syntax.Binding_var x) :: g1) g
        bs
  
let (gamma_until :
  FStar_Syntax_Syntax.gamma ->
    FStar_Syntax_Syntax.binders -> FStar_Syntax_Syntax.binding Prims.list)
  =
  fun g  ->
    fun bs  ->
      let uu____5975 = FStar_List.last bs  in
      match uu____5975 with
      | FStar_Pervasives_Native.None  -> []
      | FStar_Pervasives_Native.Some (x,uu____5999) ->
          let uu____6010 =
            FStar_Util.prefix_until
              (fun uu___21_6025  ->
                 match uu___21_6025 with
                 | FStar_Syntax_Syntax.Binding_var x' ->
                     FStar_Syntax_Syntax.bv_eq x x'
                 | uu____6028 -> false) g
             in
          (match uu____6010 with
           | FStar_Pervasives_Native.None  -> []
           | FStar_Pervasives_Native.Some (uu____6042,bx,rest) -> bx :: rest)
  
let (restrict_ctx :
  FStar_Syntax_Syntax.ctx_uvar ->
    FStar_Syntax_Syntax.ctx_uvar -> worklist -> worklist)
  =
  fun tgt  ->
    fun src  ->
      fun wl  ->
        let uu____6079 =
          maximal_prefix tgt.FStar_Syntax_Syntax.ctx_uvar_binders
            src.FStar_Syntax_Syntax.ctx_uvar_binders
           in
        match uu____6079 with
        | (pfx,uu____6089) ->
            let g = gamma_until src.FStar_Syntax_Syntax.ctx_uvar_gamma pfx
               in
            let uu____6101 =
              new_uvar
                (Prims.op_Hat "restrict:"
                   src.FStar_Syntax_Syntax.ctx_uvar_reason) wl
                src.FStar_Syntax_Syntax.ctx_uvar_range g pfx
                src.FStar_Syntax_Syntax.ctx_uvar_typ
                src.FStar_Syntax_Syntax.ctx_uvar_should_check
                src.FStar_Syntax_Syntax.ctx_uvar_meta
               in
            (match uu____6101 with
             | (uu____6109,src',wl1) ->
                 (FStar_Syntax_Unionfind.change
                    src.FStar_Syntax_Syntax.ctx_uvar_head src';
                  wl1))
  
let (restrict_all_uvars :
  FStar_Syntax_Syntax.ctx_uvar ->
    FStar_Syntax_Syntax.ctx_uvar Prims.list -> worklist -> worklist)
  =
  fun tgt  ->
    fun sources  ->
      fun wl  -> FStar_List.fold_right (restrict_ctx tgt) sources wl
  
let (intersect_binders :
  FStar_Syntax_Syntax.gamma ->
    FStar_Syntax_Syntax.binders ->
      FStar_Syntax_Syntax.binders -> FStar_Syntax_Syntax.binders)
  =
  fun g  ->
    fun v1  ->
      fun v2  ->
        let as_set1 v3 =
          FStar_All.pipe_right v3
            (FStar_List.fold_left
               (fun out  ->
                  fun x  ->
                    FStar_Util.set_add (FStar_Pervasives_Native.fst x) out)
               FStar_Syntax_Syntax.no_names)
           in
        let v1_set = as_set1 v1  in
        let ctx_binders =
          FStar_List.fold_left
            (fun out  ->
               fun b  ->
                 match b with
                 | FStar_Syntax_Syntax.Binding_var x ->
                     FStar_Util.set_add x out
                 | uu____6223 -> out) FStar_Syntax_Syntax.no_names g
           in
        let uu____6224 =
          FStar_All.pipe_right v2
            (FStar_List.fold_left
               (fun uu____6288  ->
                  fun uu____6289  ->
                    match (uu____6288, uu____6289) with
                    | ((isect,isect_set),(x,imp)) ->
                        let uu____6392 =
                          let uu____6394 = FStar_Util.set_mem x v1_set  in
                          FStar_All.pipe_left Prims.op_Negation uu____6394
                           in
                        if uu____6392
                        then (isect, isect_set)
                        else
                          (let fvs =
                             FStar_Syntax_Free.names
                               x.FStar_Syntax_Syntax.sort
                              in
                           let uu____6428 =
                             FStar_Util.set_is_subset_of fvs isect_set  in
                           if uu____6428
                           then
                             let uu____6445 = FStar_Util.set_add x isect_set
                                in
                             (((x, imp) :: isect), uu____6445)
                           else (isect, isect_set))) ([], ctx_binders))
           in
        match uu____6224 with | (isect,uu____6495) -> FStar_List.rev isect
  
let binders_eq :
  'Auu____6531 'Auu____6532 .
    (FStar_Syntax_Syntax.bv * 'Auu____6531) Prims.list ->
      (FStar_Syntax_Syntax.bv * 'Auu____6532) Prims.list -> Prims.bool
  =
  fun v1  ->
    fun v2  ->
      ((FStar_List.length v1) = (FStar_List.length v2)) &&
        (FStar_List.forall2
           (fun uu____6590  ->
              fun uu____6591  ->
                match (uu____6590, uu____6591) with
                | ((a,uu____6610),(b,uu____6612)) ->
                    FStar_Syntax_Syntax.bv_eq a b) v1 v2)
  
let name_exists_in_binders :
  'Auu____6628 .
    FStar_Syntax_Syntax.bv ->
      (FStar_Syntax_Syntax.bv * 'Auu____6628) Prims.list -> Prims.bool
  =
  fun x  ->
    fun bs  ->
      FStar_Util.for_some
        (fun uu____6659  ->
           match uu____6659 with
           | (y,uu____6666) -> FStar_Syntax_Syntax.bv_eq x y) bs
  
let pat_vars :
  'Auu____6676 .
    FStar_TypeChecker_Env.env ->
      (FStar_Syntax_Syntax.bv * 'Auu____6676) Prims.list ->
        (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.arg_qualifier
          FStar_Pervasives_Native.option) Prims.list ->
          FStar_Syntax_Syntax.binders FStar_Pervasives_Native.option
  =
  fun env  ->
    fun ctx  ->
      fun args  ->
        let rec aux seen args1 =
          match args1 with
          | [] -> FStar_Pervasives_Native.Some (FStar_List.rev seen)
          | (arg,i)::args2 ->
              let hd1 = sn env arg  in
              (match hd1.FStar_Syntax_Syntax.n with
               | FStar_Syntax_Syntax.Tm_name a ->
                   let uu____6838 =
                     (name_exists_in_binders a seen) ||
                       (name_exists_in_binders a ctx)
                      in
                   if uu____6838
                   then FStar_Pervasives_Native.None
                   else aux ((a, i) :: seen) args2
               | uu____6871 -> FStar_Pervasives_Native.None)
           in
        aux [] args
  
type match_result =
  | MisMatch of (FStar_Syntax_Syntax.delta_depth
  FStar_Pervasives_Native.option * FStar_Syntax_Syntax.delta_depth
  FStar_Pervasives_Native.option) 
  | HeadMatch of Prims.bool 
  | FullMatch 
let (uu___is_MisMatch : match_result -> Prims.bool) =
  fun projectee  ->
    match projectee with | MisMatch _0 -> true | uu____6923 -> false
  
let (__proj__MisMatch__item___0 :
  match_result ->
    (FStar_Syntax_Syntax.delta_depth FStar_Pervasives_Native.option *
      FStar_Syntax_Syntax.delta_depth FStar_Pervasives_Native.option))
  = fun projectee  -> match projectee with | MisMatch _0 -> _0 
let (uu___is_HeadMatch : match_result -> Prims.bool) =
  fun projectee  ->
    match projectee with | HeadMatch _0 -> true | uu____6967 -> false
  
let (__proj__HeadMatch__item___0 : match_result -> Prims.bool) =
  fun projectee  -> match projectee with | HeadMatch _0 -> _0 
let (uu___is_FullMatch : match_result -> Prims.bool) =
  fun projectee  ->
    match projectee with | FullMatch  -> true | uu____6988 -> false
  
let (string_of_match_result : match_result -> Prims.string) =
  fun uu___22_6996  ->
    match uu___22_6996 with
    | MisMatch (d1,d2) ->
        let uu____7008 =
          let uu____7010 =
            FStar_Common.string_of_option
              FStar_Syntax_Print.delta_depth_to_string d1
             in
          let uu____7012 =
            let uu____7014 =
              let uu____7016 =
                FStar_Common.string_of_option
                  FStar_Syntax_Print.delta_depth_to_string d2
                 in
              Prims.op_Hat uu____7016 ")"  in
            Prims.op_Hat ") (" uu____7014  in
          Prims.op_Hat uu____7010 uu____7012  in
        Prims.op_Hat "MisMatch (" uu____7008
    | HeadMatch u ->
        let uu____7023 = FStar_Util.string_of_bool u  in
        Prims.op_Hat "HeadMatch " uu____7023
    | FullMatch  -> "FullMatch"
  
let (head_match : match_result -> match_result) =
  fun uu___23_7032  ->
    match uu___23_7032 with
    | MisMatch (i,j) -> MisMatch (i, j)
    | HeadMatch (true ) -> HeadMatch true
    | uu____7049 -> HeadMatch false
  
let (fv_delta_depth :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.fv -> FStar_Syntax_Syntax.delta_depth)
  =
  fun env  ->
    fun fv  ->
      let d = FStar_TypeChecker_Env.delta_depth_of_fv env fv  in
      match d with
      | FStar_Syntax_Syntax.Delta_abstract d1 ->
          if
            ((env.FStar_TypeChecker_Env.curmodule).FStar_Ident.str =
               ((fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v).FStar_Ident.nsstr)
              && (Prims.op_Negation env.FStar_TypeChecker_Env.is_iface)
          then d1
          else FStar_Syntax_Syntax.delta_constant
      | FStar_Syntax_Syntax.Delta_constant_at_level i when i > Prims.int_zero
          ->
          let uu____7071 =
            FStar_TypeChecker_Env.lookup_definition
              [FStar_TypeChecker_Env.Unfold
                 FStar_Syntax_Syntax.delta_constant] env
              (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
             in
          (match uu____7071 with
           | FStar_Pervasives_Native.None  ->
               FStar_Syntax_Syntax.delta_constant
           | uu____7082 -> d)
      | d1 -> d1
  
let rec (delta_depth_of_term :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term ->
      FStar_Syntax_Syntax.delta_depth FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun t  ->
      let t1 = FStar_Syntax_Util.unmeta t  in
      match t1.FStar_Syntax_Syntax.n with
      | FStar_Syntax_Syntax.Tm_meta uu____7106 -> failwith "Impossible"
      | FStar_Syntax_Syntax.Tm_delayed uu____7116 -> failwith "Impossible"
      | FStar_Syntax_Syntax.Tm_lazy i ->
          let uu____7135 = FStar_Syntax_Util.unfold_lazy i  in
          delta_depth_of_term env uu____7135
      | FStar_Syntax_Syntax.Tm_unknown  -> FStar_Pervasives_Native.None
      | FStar_Syntax_Syntax.Tm_bvar uu____7136 ->
          FStar_Pervasives_Native.None
      | FStar_Syntax_Syntax.Tm_name uu____7137 ->
          FStar_Pervasives_Native.None
      | FStar_Syntax_Syntax.Tm_uvar uu____7138 ->
          FStar_Pervasives_Native.None
      | FStar_Syntax_Syntax.Tm_let uu____7151 -> FStar_Pervasives_Native.None
      | FStar_Syntax_Syntax.Tm_match uu____7165 ->
          FStar_Pervasives_Native.None
      | FStar_Syntax_Syntax.Tm_uinst (t2,uu____7189) ->
          delta_depth_of_term env t2
      | FStar_Syntax_Syntax.Tm_ascribed (t2,uu____7195,uu____7196) ->
          delta_depth_of_term env t2
      | FStar_Syntax_Syntax.Tm_app (t2,uu____7238) ->
          delta_depth_of_term env t2
      | FStar_Syntax_Syntax.Tm_refine
          ({ FStar_Syntax_Syntax.ppname = uu____7263;
             FStar_Syntax_Syntax.index = uu____7264;
             FStar_Syntax_Syntax.sort = t2;_},uu____7266)
          -> delta_depth_of_term env t2
      | FStar_Syntax_Syntax.Tm_constant uu____7274 ->
          FStar_Pervasives_Native.Some FStar_Syntax_Syntax.delta_constant
      | FStar_Syntax_Syntax.Tm_type uu____7275 ->
          FStar_Pervasives_Native.Some FStar_Syntax_Syntax.delta_constant
      | FStar_Syntax_Syntax.Tm_arrow uu____7276 ->
          FStar_Pervasives_Native.Some FStar_Syntax_Syntax.delta_constant
      | FStar_Syntax_Syntax.Tm_quoted uu____7291 ->
          FStar_Pervasives_Native.Some FStar_Syntax_Syntax.delta_constant
      | FStar_Syntax_Syntax.Tm_abs uu____7298 ->
          FStar_Pervasives_Native.Some FStar_Syntax_Syntax.delta_constant
      | FStar_Syntax_Syntax.Tm_fvar fv ->
          let uu____7318 = fv_delta_depth env fv  in
          FStar_Pervasives_Native.Some uu____7318
  
let rec (head_matches :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term -> match_result)
  =
  fun env  ->
    fun t1  ->
      fun t2  ->
        let t11 = FStar_Syntax_Util.unmeta t1  in
        let t21 = FStar_Syntax_Util.unmeta t2  in
        match ((t11.FStar_Syntax_Syntax.n), (t21.FStar_Syntax_Syntax.n)) with
        | (FStar_Syntax_Syntax.Tm_lazy
           { FStar_Syntax_Syntax.blob = uu____7337;
             FStar_Syntax_Syntax.lkind = FStar_Syntax_Syntax.Lazy_embedding
               uu____7338;
             FStar_Syntax_Syntax.ltyp = uu____7339;
             FStar_Syntax_Syntax.rng = uu____7340;_},uu____7341)
            ->
            let uu____7352 = FStar_Syntax_Util.unlazy t11  in
            head_matches env uu____7352 t21
        | (uu____7353,FStar_Syntax_Syntax.Tm_lazy
           { FStar_Syntax_Syntax.blob = uu____7354;
             FStar_Syntax_Syntax.lkind = FStar_Syntax_Syntax.Lazy_embedding
               uu____7355;
             FStar_Syntax_Syntax.ltyp = uu____7356;
             FStar_Syntax_Syntax.rng = uu____7357;_})
            ->
            let uu____7368 = FStar_Syntax_Util.unlazy t21  in
            head_matches env t11 uu____7368
        | (FStar_Syntax_Syntax.Tm_name x,FStar_Syntax_Syntax.Tm_name y) ->
            if FStar_Syntax_Syntax.bv_eq x y
            then FullMatch
            else
              MisMatch
                (FStar_Pervasives_Native.None, FStar_Pervasives_Native.None)
        | (FStar_Syntax_Syntax.Tm_fvar f,FStar_Syntax_Syntax.Tm_fvar g) ->
            let uu____7380 = FStar_Syntax_Syntax.fv_eq f g  in
            if uu____7380
            then FullMatch
            else
              (let uu____7385 =
                 let uu____7394 =
                   let uu____7397 = fv_delta_depth env f  in
                   FStar_Pervasives_Native.Some uu____7397  in
                 let uu____7398 =
                   let uu____7401 = fv_delta_depth env g  in
                   FStar_Pervasives_Native.Some uu____7401  in
                 (uu____7394, uu____7398)  in
               MisMatch uu____7385)
        | (FStar_Syntax_Syntax.Tm_uinst
           (f,uu____7407),FStar_Syntax_Syntax.Tm_uinst (g,uu____7409)) ->
            let uu____7418 = head_matches env f g  in
            FStar_All.pipe_right uu____7418 head_match
        | (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_reify
           ),FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_reify )) ->
            FullMatch
        | (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_reify
           ),uu____7419) -> HeadMatch true
        | (uu____7421,FStar_Syntax_Syntax.Tm_constant
           (FStar_Const.Const_reify )) -> HeadMatch true
        | (FStar_Syntax_Syntax.Tm_constant c,FStar_Syntax_Syntax.Tm_constant
           d) ->
            let uu____7425 = FStar_Const.eq_const c d  in
            if uu____7425
            then FullMatch
            else
              MisMatch
                (FStar_Pervasives_Native.None, FStar_Pervasives_Native.None)
        | (FStar_Syntax_Syntax.Tm_uvar
           (uv,uu____7435),FStar_Syntax_Syntax.Tm_uvar (uv',uu____7437)) ->
            let uu____7470 =
              FStar_Syntax_Unionfind.equiv
                uv.FStar_Syntax_Syntax.ctx_uvar_head
                uv'.FStar_Syntax_Syntax.ctx_uvar_head
               in
            if uu____7470
            then FullMatch
            else
              MisMatch
                (FStar_Pervasives_Native.None, FStar_Pervasives_Native.None)
        | (FStar_Syntax_Syntax.Tm_refine
           (x,uu____7480),FStar_Syntax_Syntax.Tm_refine (y,uu____7482)) ->
            let uu____7491 =
              head_matches env x.FStar_Syntax_Syntax.sort
                y.FStar_Syntax_Syntax.sort
               in
            FStar_All.pipe_right uu____7491 head_match
        | (FStar_Syntax_Syntax.Tm_refine (x,uu____7493),uu____7494) ->
            let uu____7499 = head_matches env x.FStar_Syntax_Syntax.sort t21
               in
            FStar_All.pipe_right uu____7499 head_match
        | (uu____7500,FStar_Syntax_Syntax.Tm_refine (x,uu____7502)) ->
            let uu____7507 = head_matches env t11 x.FStar_Syntax_Syntax.sort
               in
            FStar_All.pipe_right uu____7507 head_match
        | (FStar_Syntax_Syntax.Tm_type uu____7508,FStar_Syntax_Syntax.Tm_type
           uu____7509) -> HeadMatch false
        | (FStar_Syntax_Syntax.Tm_arrow
           uu____7511,FStar_Syntax_Syntax.Tm_arrow uu____7512) ->
            HeadMatch false
        | (FStar_Syntax_Syntax.Tm_app
           (head1,uu____7543),FStar_Syntax_Syntax.Tm_app (head',uu____7545))
            ->
            let uu____7594 = head_matches env head1 head'  in
            FStar_All.pipe_right uu____7594 head_match
        | (FStar_Syntax_Syntax.Tm_app (head1,uu____7596),uu____7597) ->
            let uu____7622 = head_matches env head1 t21  in
            FStar_All.pipe_right uu____7622 head_match
        | (uu____7623,FStar_Syntax_Syntax.Tm_app (head1,uu____7625)) ->
            let uu____7650 = head_matches env t11 head1  in
            FStar_All.pipe_right uu____7650 head_match
        | (FStar_Syntax_Syntax.Tm_let uu____7651,FStar_Syntax_Syntax.Tm_let
           uu____7652) -> HeadMatch true
        | (FStar_Syntax_Syntax.Tm_match
           uu____7680,FStar_Syntax_Syntax.Tm_match uu____7681) ->
            HeadMatch true
        | (FStar_Syntax_Syntax.Tm_abs uu____7727,FStar_Syntax_Syntax.Tm_abs
           uu____7728) -> HeadMatch true
        | uu____7766 ->
            let uu____7771 =
              let uu____7780 = delta_depth_of_term env t11  in
              let uu____7783 = delta_depth_of_term env t21  in
              (uu____7780, uu____7783)  in
            MisMatch uu____7771
  
let (head_matches_delta :
  FStar_TypeChecker_Env.env ->
    worklist ->
      FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
        FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
          (match_result * (FStar_Syntax_Syntax.typ * FStar_Syntax_Syntax.typ)
            FStar_Pervasives_Native.option))
  =
  fun env  ->
    fun wl  ->
      fun t1  ->
        fun t2  ->
          let maybe_inline t =
            let head1 =
              let uu____7852 = unrefine env t  in
              FStar_Syntax_Util.head_of uu____7852  in
            (let uu____7854 =
               FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                 (FStar_Options.Other "RelDelta")
                in
             if uu____7854
             then
               let uu____7859 = FStar_Syntax_Print.term_to_string t  in
               let uu____7861 = FStar_Syntax_Print.term_to_string head1  in
               FStar_Util.print2 "Head of %s is %s\n" uu____7859 uu____7861
             else ());
            (let uu____7866 =
               let uu____7867 = FStar_Syntax_Util.un_uinst head1  in
               uu____7867.FStar_Syntax_Syntax.n  in
             match uu____7866 with
             | FStar_Syntax_Syntax.Tm_fvar fv ->
                 let uu____7873 =
                   FStar_TypeChecker_Env.lookup_definition
                     [FStar_TypeChecker_Env.Unfold
                        FStar_Syntax_Syntax.delta_constant;
                     FStar_TypeChecker_Env.Eager_unfolding_only] env
                     (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                    in
                 (match uu____7873 with
                  | FStar_Pervasives_Native.None  ->
                      ((let uu____7887 =
                          FStar_All.pipe_left
                            (FStar_TypeChecker_Env.debug env)
                            (FStar_Options.Other "RelDelta")
                           in
                        if uu____7887
                        then
                          let uu____7892 =
                            FStar_Syntax_Print.term_to_string head1  in
                          FStar_Util.print1 "No definition found for %s\n"
                            uu____7892
                        else ());
                       FStar_Pervasives_Native.None)
                  | FStar_Pervasives_Native.Some uu____7897 ->
                      let basic_steps =
                        [FStar_TypeChecker_Env.UnfoldUntil
                           FStar_Syntax_Syntax.delta_constant;
                        FStar_TypeChecker_Env.Weak;
                        FStar_TypeChecker_Env.HNF;
                        FStar_TypeChecker_Env.Primops;
                        FStar_TypeChecker_Env.Beta;
                        FStar_TypeChecker_Env.Eager_unfolding;
                        FStar_TypeChecker_Env.Iota]  in
                      let steps =
                        if wl.smt_ok
                        then basic_steps
                        else
                          (FStar_TypeChecker_Env.Exclude
                             FStar_TypeChecker_Env.Zeta)
                          :: basic_steps
                         in
                      let t' =
                        FStar_TypeChecker_Normalize.normalize steps env t  in
                      let uu____7914 =
                        let uu____7916 = FStar_Syntax_Util.eq_tm t t'  in
                        uu____7916 = FStar_Syntax_Util.Equal  in
                      if uu____7914
                      then FStar_Pervasives_Native.None
                      else
                        ((let uu____7923 =
                            FStar_All.pipe_left
                              (FStar_TypeChecker_Env.debug env)
                              (FStar_Options.Other "RelDelta")
                             in
                          if uu____7923
                          then
                            let uu____7928 =
                              FStar_Syntax_Print.term_to_string t  in
                            let uu____7930 =
                              FStar_Syntax_Print.term_to_string t'  in
                            FStar_Util.print2 "Inlined %s to %s\n" uu____7928
                              uu____7930
                          else ());
                         FStar_Pervasives_Native.Some t'))
             | uu____7935 -> FStar_Pervasives_Native.None)
             in
          let success d r t11 t21 =
            (r,
              (if d > Prims.int_zero
               then FStar_Pervasives_Native.Some (t11, t21)
               else FStar_Pervasives_Native.None))
             in
          let fail1 d r t11 t21 =
            (r,
              (if d > Prims.int_zero
               then FStar_Pervasives_Native.Some (t11, t21)
               else FStar_Pervasives_Native.None))
             in
          let rec aux retry n_delta t11 t21 =
            let r = head_matches env t11 t21  in
            (let uu____8087 =
               FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                 (FStar_Options.Other "RelDelta")
                in
             if uu____8087
             then
               let uu____8092 = FStar_Syntax_Print.term_to_string t11  in
               let uu____8094 = FStar_Syntax_Print.term_to_string t21  in
               let uu____8096 = string_of_match_result r  in
               FStar_Util.print3 "head_matches (%s, %s) = %s\n" uu____8092
                 uu____8094 uu____8096
             else ());
            (let reduce_one_and_try_again d1 d2 =
               let d1_greater_than_d2 =
                 FStar_TypeChecker_Common.delta_depth_greater_than d1 d2  in
               let uu____8124 =
                 if d1_greater_than_d2
                 then
                   let t1' =
                     normalize_refinement
                       [FStar_TypeChecker_Env.UnfoldUntil d2;
                       FStar_TypeChecker_Env.Weak;
                       FStar_TypeChecker_Env.HNF] env t11
                      in
                   (t1', t21)
                 else
                   (let t2' =
                      normalize_refinement
                        [FStar_TypeChecker_Env.UnfoldUntil d1;
                        FStar_TypeChecker_Env.Weak;
                        FStar_TypeChecker_Env.HNF] env t21
                       in
                    (t11, t2'))
                  in
               match uu____8124 with
               | (t12,t22) -> aux retry (n_delta + Prims.int_one) t12 t22  in
             let reduce_both_and_try_again d r1 =
               let uu____8172 = FStar_TypeChecker_Common.decr_delta_depth d
                  in
               match uu____8172 with
               | FStar_Pervasives_Native.None  -> fail1 n_delta r1 t11 t21
               | FStar_Pervasives_Native.Some d1 ->
                   let t12 =
                     normalize_refinement
                       [FStar_TypeChecker_Env.UnfoldUntil d1;
                       FStar_TypeChecker_Env.Weak;
                       FStar_TypeChecker_Env.HNF] env t11
                      in
                   let t22 =
                     normalize_refinement
                       [FStar_TypeChecker_Env.UnfoldUntil d1;
                       FStar_TypeChecker_Env.Weak;
                       FStar_TypeChecker_Env.HNF] env t21
                      in
                   aux retry (n_delta + Prims.int_one) t12 t22
                in
             match r with
             | MisMatch
                 (FStar_Pervasives_Native.Some
                  (FStar_Syntax_Syntax.Delta_equational_at_level
                  i),FStar_Pervasives_Native.Some
                  (FStar_Syntax_Syntax.Delta_equational_at_level j))
                 when
                 ((i > Prims.int_zero) || (j > Prims.int_zero)) && (i <> j)
                 ->
                 reduce_one_and_try_again
                   (FStar_Syntax_Syntax.Delta_equational_at_level i)
                   (FStar_Syntax_Syntax.Delta_equational_at_level j)
             | MisMatch
                 (FStar_Pervasives_Native.Some
                  (FStar_Syntax_Syntax.Delta_equational_at_level
                  uu____8210),uu____8211)
                 ->
                 if Prims.op_Negation retry
                 then fail1 n_delta r t11 t21
                 else
                   (let uu____8232 =
                      let uu____8241 = maybe_inline t11  in
                      let uu____8244 = maybe_inline t21  in
                      (uu____8241, uu____8244)  in
                    match uu____8232 with
                    | (FStar_Pervasives_Native.None
                       ,FStar_Pervasives_Native.None ) ->
                        fail1 n_delta r t11 t21
                    | (FStar_Pervasives_Native.Some
                       t12,FStar_Pervasives_Native.None ) ->
                        aux false (n_delta + Prims.int_one) t12 t21
                    | (FStar_Pervasives_Native.None
                       ,FStar_Pervasives_Native.Some t22) ->
                        aux false (n_delta + Prims.int_one) t11 t22
                    | (FStar_Pervasives_Native.Some
                       t12,FStar_Pervasives_Native.Some t22) ->
                        aux false (n_delta + Prims.int_one) t12 t22)
             | MisMatch
                 (uu____8287,FStar_Pervasives_Native.Some
                  (FStar_Syntax_Syntax.Delta_equational_at_level uu____8288))
                 ->
                 if Prims.op_Negation retry
                 then fail1 n_delta r t11 t21
                 else
                   (let uu____8309 =
                      let uu____8318 = maybe_inline t11  in
                      let uu____8321 = maybe_inline t21  in
                      (uu____8318, uu____8321)  in
                    match uu____8309 with
                    | (FStar_Pervasives_Native.None
                       ,FStar_Pervasives_Native.None ) ->
                        fail1 n_delta r t11 t21
                    | (FStar_Pervasives_Native.Some
                       t12,FStar_Pervasives_Native.None ) ->
                        aux false (n_delta + Prims.int_one) t12 t21
                    | (FStar_Pervasives_Native.None
                       ,FStar_Pervasives_Native.Some t22) ->
                        aux false (n_delta + Prims.int_one) t11 t22
                    | (FStar_Pervasives_Native.Some
                       t12,FStar_Pervasives_Native.Some t22) ->
                        aux false (n_delta + Prims.int_one) t12 t22)
             | MisMatch
                 (FStar_Pervasives_Native.Some
                  d1,FStar_Pervasives_Native.Some d2)
                 when d1 = d2 -> reduce_both_and_try_again d1 r
             | MisMatch
                 (FStar_Pervasives_Native.Some
                  d1,FStar_Pervasives_Native.Some d2)
                 -> reduce_one_and_try_again d1 d2
             | MisMatch uu____8376 -> fail1 n_delta r t11 t21
             | uu____8385 -> success n_delta r t11 t21)
             in
          let r = aux true Prims.int_zero t1 t2  in
          (let uu____8400 =
             FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
               (FStar_Options.Other "RelDelta")
              in
           if uu____8400
           then
             let uu____8405 = FStar_Syntax_Print.term_to_string t1  in
             let uu____8407 = FStar_Syntax_Print.term_to_string t2  in
             let uu____8409 =
               string_of_match_result (FStar_Pervasives_Native.fst r)  in
             let uu____8417 =
               if FStar_Option.isNone (FStar_Pervasives_Native.snd r)
               then "None"
               else
                 (let uu____8434 =
                    FStar_All.pipe_right (FStar_Pervasives_Native.snd r)
                      FStar_Util.must
                     in
                  FStar_All.pipe_right uu____8434
                    (fun uu____8469  ->
                       match uu____8469 with
                       | (t11,t21) ->
                           let uu____8477 =
                             FStar_Syntax_Print.term_to_string t11  in
                           let uu____8479 =
                             let uu____8481 =
                               FStar_Syntax_Print.term_to_string t21  in
                             Prims.op_Hat "; " uu____8481  in
                           Prims.op_Hat uu____8477 uu____8479))
                in
             FStar_Util.print4 "head_matches_delta (%s, %s) = %s (%s)\n"
               uu____8405 uu____8407 uu____8409 uu____8417
           else ());
          r
  
let (kind_type :
  FStar_Syntax_Syntax.binders -> FStar_Range.range -> FStar_Syntax_Syntax.typ)
  =
  fun binders  ->
    fun r  ->
      let uu____8498 = FStar_Syntax_Util.type_u ()  in
      FStar_All.pipe_right uu____8498 FStar_Pervasives_Native.fst
  
let (rank_t_num : FStar_TypeChecker_Common.rank_t -> Prims.int) =
  fun uu___24_8513  ->
    match uu___24_8513 with
    | FStar_TypeChecker_Common.Rigid_rigid  -> Prims.int_zero
    | FStar_TypeChecker_Common.Flex_rigid_eq  -> Prims.int_one
    | FStar_TypeChecker_Common.Flex_flex_pattern_eq  -> (Prims.of_int (2))
    | FStar_TypeChecker_Common.Flex_rigid  -> (Prims.of_int (3))
    | FStar_TypeChecker_Common.Rigid_flex  -> (Prims.of_int (4))
    | FStar_TypeChecker_Common.Flex_flex  -> (Prims.of_int (5))
  
let (rank_leq :
  FStar_TypeChecker_Common.rank_t ->
    FStar_TypeChecker_Common.rank_t -> Prims.bool)
  = fun r1  -> fun r2  -> (rank_t_num r1) <= (rank_t_num r2) 
let (rank_less_than :
  FStar_TypeChecker_Common.rank_t ->
    FStar_TypeChecker_Common.rank_t -> Prims.bool)
  = fun r1  -> fun r2  -> (r1 <> r2) && ((rank_t_num r1) <= (rank_t_num r2)) 
let (compress_tprob :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term FStar_TypeChecker_Common.problem ->
      FStar_Syntax_Syntax.term FStar_TypeChecker_Common.problem)
  =
  fun tcenv  ->
    fun p  ->
      let uu___1211_8562 = p  in
      let uu____8565 = whnf tcenv p.FStar_TypeChecker_Common.lhs  in
      let uu____8566 = whnf tcenv p.FStar_TypeChecker_Common.rhs  in
      {
        FStar_TypeChecker_Common.pid =
          (uu___1211_8562.FStar_TypeChecker_Common.pid);
        FStar_TypeChecker_Common.lhs = uu____8565;
        FStar_TypeChecker_Common.relation =
          (uu___1211_8562.FStar_TypeChecker_Common.relation);
        FStar_TypeChecker_Common.rhs = uu____8566;
        FStar_TypeChecker_Common.element =
          (uu___1211_8562.FStar_TypeChecker_Common.element);
        FStar_TypeChecker_Common.logical_guard =
          (uu___1211_8562.FStar_TypeChecker_Common.logical_guard);
        FStar_TypeChecker_Common.logical_guard_uvar =
          (uu___1211_8562.FStar_TypeChecker_Common.logical_guard_uvar);
        FStar_TypeChecker_Common.reason =
          (uu___1211_8562.FStar_TypeChecker_Common.reason);
        FStar_TypeChecker_Common.loc =
          (uu___1211_8562.FStar_TypeChecker_Common.loc);
        FStar_TypeChecker_Common.rank =
          (uu___1211_8562.FStar_TypeChecker_Common.rank)
      }
  
let (compress_prob :
  FStar_TypeChecker_Env.env ->
    FStar_TypeChecker_Common.prob -> FStar_TypeChecker_Common.prob)
  =
  fun tcenv  ->
    fun p  ->
      match p with
      | FStar_TypeChecker_Common.TProb p1 ->
          let uu____8581 = compress_tprob tcenv p1  in
          FStar_All.pipe_right uu____8581
            (fun _8586  -> FStar_TypeChecker_Common.TProb _8586)
      | FStar_TypeChecker_Common.CProb uu____8587 -> p
  
let (rank :
  FStar_TypeChecker_Env.env ->
    FStar_TypeChecker_Common.prob ->
      (FStar_TypeChecker_Common.rank_t * FStar_TypeChecker_Common.prob))
  =
  fun tcenv  ->
    fun pr  ->
      let prob =
        let uu____8610 = compress_prob tcenv pr  in
        FStar_All.pipe_right uu____8610 maybe_invert_p  in
      match prob with
      | FStar_TypeChecker_Common.TProb tp ->
          let uu____8618 =
            FStar_Syntax_Util.head_and_args tp.FStar_TypeChecker_Common.lhs
             in
          (match uu____8618 with
           | (lh,lhs_args) ->
               let uu____8665 =
                 FStar_Syntax_Util.head_and_args
                   tp.FStar_TypeChecker_Common.rhs
                  in
               (match uu____8665 with
                | (rh,rhs_args) ->
                    let uu____8712 =
                      match ((lh.FStar_Syntax_Syntax.n),
                              (rh.FStar_Syntax_Syntax.n))
                      with
                      | (FStar_Syntax_Syntax.Tm_uvar
                         uu____8725,FStar_Syntax_Syntax.Tm_uvar uu____8726)
                          ->
                          (match (lhs_args, rhs_args) with
                           | ([],[]) when
                               tp.FStar_TypeChecker_Common.relation =
                                 FStar_TypeChecker_Common.EQ
                               ->
                               (FStar_TypeChecker_Common.Flex_flex_pattern_eq,
                                 tp)
                           | uu____8815 ->
                               (FStar_TypeChecker_Common.Flex_flex, tp))
                      | (FStar_Syntax_Syntax.Tm_uvar uu____8842,uu____8843)
                          when
                          tp.FStar_TypeChecker_Common.relation =
                            FStar_TypeChecker_Common.EQ
                          -> (FStar_TypeChecker_Common.Flex_rigid_eq, tp)
                      | (uu____8858,FStar_Syntax_Syntax.Tm_uvar uu____8859)
                          when
                          tp.FStar_TypeChecker_Common.relation =
                            FStar_TypeChecker_Common.EQ
                          -> (FStar_TypeChecker_Common.Flex_rigid_eq, tp)
                      | (FStar_Syntax_Syntax.Tm_uvar
                         uu____8874,FStar_Syntax_Syntax.Tm_arrow uu____8875)
                          ->
                          (FStar_TypeChecker_Common.Flex_rigid_eq,
                            (let uu___1262_8905 = tp  in
                             {
                               FStar_TypeChecker_Common.pid =
                                 (uu___1262_8905.FStar_TypeChecker_Common.pid);
                               FStar_TypeChecker_Common.lhs =
                                 (uu___1262_8905.FStar_TypeChecker_Common.lhs);
                               FStar_TypeChecker_Common.relation =
                                 FStar_TypeChecker_Common.EQ;
                               FStar_TypeChecker_Common.rhs =
                                 (uu___1262_8905.FStar_TypeChecker_Common.rhs);
                               FStar_TypeChecker_Common.element =
                                 (uu___1262_8905.FStar_TypeChecker_Common.element);
                               FStar_TypeChecker_Common.logical_guard =
                                 (uu___1262_8905.FStar_TypeChecker_Common.logical_guard);
                               FStar_TypeChecker_Common.logical_guard_uvar =
                                 (uu___1262_8905.FStar_TypeChecker_Common.logical_guard_uvar);
                               FStar_TypeChecker_Common.reason =
                                 (uu___1262_8905.FStar_TypeChecker_Common.reason);
                               FStar_TypeChecker_Common.loc =
                                 (uu___1262_8905.FStar_TypeChecker_Common.loc);
                               FStar_TypeChecker_Common.rank =
                                 (uu___1262_8905.FStar_TypeChecker_Common.rank)
                             }))
                      | (FStar_Syntax_Syntax.Tm_uvar
                         uu____8908,FStar_Syntax_Syntax.Tm_type uu____8909)
                          ->
                          (FStar_TypeChecker_Common.Flex_rigid_eq,
                            (let uu___1262_8925 = tp  in
                             {
                               FStar_TypeChecker_Common.pid =
                                 (uu___1262_8925.FStar_TypeChecker_Common.pid);
                               FStar_TypeChecker_Common.lhs =
                                 (uu___1262_8925.FStar_TypeChecker_Common.lhs);
                               FStar_TypeChecker_Common.relation =
                                 FStar_TypeChecker_Common.EQ;
                               FStar_TypeChecker_Common.rhs =
                                 (uu___1262_8925.FStar_TypeChecker_Common.rhs);
                               FStar_TypeChecker_Common.element =
                                 (uu___1262_8925.FStar_TypeChecker_Common.element);
                               FStar_TypeChecker_Common.logical_guard =
                                 (uu___1262_8925.FStar_TypeChecker_Common.logical_guard);
                               FStar_TypeChecker_Common.logical_guard_uvar =
                                 (uu___1262_8925.FStar_TypeChecker_Common.logical_guard_uvar);
                               FStar_TypeChecker_Common.reason =
                                 (uu___1262_8925.FStar_TypeChecker_Common.reason);
                               FStar_TypeChecker_Common.loc =
                                 (uu___1262_8925.FStar_TypeChecker_Common.loc);
                               FStar_TypeChecker_Common.rank =
                                 (uu___1262_8925.FStar_TypeChecker_Common.rank)
                             }))
                      | (FStar_Syntax_Syntax.Tm_type
                         uu____8928,FStar_Syntax_Syntax.Tm_uvar uu____8929)
                          ->
                          (FStar_TypeChecker_Common.Flex_rigid_eq,
                            (let uu___1262_8945 = tp  in
                             {
                               FStar_TypeChecker_Common.pid =
                                 (uu___1262_8945.FStar_TypeChecker_Common.pid);
                               FStar_TypeChecker_Common.lhs =
                                 (uu___1262_8945.FStar_TypeChecker_Common.lhs);
                               FStar_TypeChecker_Common.relation =
                                 FStar_TypeChecker_Common.EQ;
                               FStar_TypeChecker_Common.rhs =
                                 (uu___1262_8945.FStar_TypeChecker_Common.rhs);
                               FStar_TypeChecker_Common.element =
                                 (uu___1262_8945.FStar_TypeChecker_Common.element);
                               FStar_TypeChecker_Common.logical_guard =
                                 (uu___1262_8945.FStar_TypeChecker_Common.logical_guard);
                               FStar_TypeChecker_Common.logical_guard_uvar =
                                 (uu___1262_8945.FStar_TypeChecker_Common.logical_guard_uvar);
                               FStar_TypeChecker_Common.reason =
                                 (uu___1262_8945.FStar_TypeChecker_Common.reason);
                               FStar_TypeChecker_Common.loc =
                                 (uu___1262_8945.FStar_TypeChecker_Common.loc);
                               FStar_TypeChecker_Common.rank =
                                 (uu___1262_8945.FStar_TypeChecker_Common.rank)
                             }))
                      | (uu____8948,FStar_Syntax_Syntax.Tm_uvar uu____8949)
                          -> (FStar_TypeChecker_Common.Rigid_flex, tp)
                      | (FStar_Syntax_Syntax.Tm_uvar uu____8964,uu____8965)
                          -> (FStar_TypeChecker_Common.Flex_rigid, tp)
                      | (uu____8980,FStar_Syntax_Syntax.Tm_uvar uu____8981)
                          -> (FStar_TypeChecker_Common.Rigid_flex, tp)
                      | (uu____8996,uu____8997) ->
                          (FStar_TypeChecker_Common.Rigid_rigid, tp)
                       in
                    (match uu____8712 with
                     | (rank,tp1) ->
                         let uu____9010 =
                           FStar_All.pipe_right
                             (let uu___1282_9014 = tp1  in
                              {
                                FStar_TypeChecker_Common.pid =
                                  (uu___1282_9014.FStar_TypeChecker_Common.pid);
                                FStar_TypeChecker_Common.lhs =
                                  (uu___1282_9014.FStar_TypeChecker_Common.lhs);
                                FStar_TypeChecker_Common.relation =
                                  (uu___1282_9014.FStar_TypeChecker_Common.relation);
                                FStar_TypeChecker_Common.rhs =
                                  (uu___1282_9014.FStar_TypeChecker_Common.rhs);
                                FStar_TypeChecker_Common.element =
                                  (uu___1282_9014.FStar_TypeChecker_Common.element);
                                FStar_TypeChecker_Common.logical_guard =
                                  (uu___1282_9014.FStar_TypeChecker_Common.logical_guard);
                                FStar_TypeChecker_Common.logical_guard_uvar =
                                  (uu___1282_9014.FStar_TypeChecker_Common.logical_guard_uvar);
                                FStar_TypeChecker_Common.reason =
                                  (uu___1282_9014.FStar_TypeChecker_Common.reason);
                                FStar_TypeChecker_Common.loc =
                                  (uu___1282_9014.FStar_TypeChecker_Common.loc);
                                FStar_TypeChecker_Common.rank =
                                  (FStar_Pervasives_Native.Some rank)
                              })
                             (fun _9017  ->
                                FStar_TypeChecker_Common.TProb _9017)
                            in
                         (rank, uu____9010))))
      | FStar_TypeChecker_Common.CProb cp ->
          let uu____9021 =
            FStar_All.pipe_right
              (let uu___1286_9025 = cp  in
               {
                 FStar_TypeChecker_Common.pid =
                   (uu___1286_9025.FStar_TypeChecker_Common.pid);
                 FStar_TypeChecker_Common.lhs =
                   (uu___1286_9025.FStar_TypeChecker_Common.lhs);
                 FStar_TypeChecker_Common.relation =
                   (uu___1286_9025.FStar_TypeChecker_Common.relation);
                 FStar_TypeChecker_Common.rhs =
                   (uu___1286_9025.FStar_TypeChecker_Common.rhs);
                 FStar_TypeChecker_Common.element =
                   (uu___1286_9025.FStar_TypeChecker_Common.element);
                 FStar_TypeChecker_Common.logical_guard =
                   (uu___1286_9025.FStar_TypeChecker_Common.logical_guard);
                 FStar_TypeChecker_Common.logical_guard_uvar =
                   (uu___1286_9025.FStar_TypeChecker_Common.logical_guard_uvar);
                 FStar_TypeChecker_Common.reason =
                   (uu___1286_9025.FStar_TypeChecker_Common.reason);
                 FStar_TypeChecker_Common.loc =
                   (uu___1286_9025.FStar_TypeChecker_Common.loc);
                 FStar_TypeChecker_Common.rank =
                   (FStar_Pervasives_Native.Some
                      FStar_TypeChecker_Common.Rigid_rigid)
               }) (fun _9028  -> FStar_TypeChecker_Common.CProb _9028)
             in
          (FStar_TypeChecker_Common.Rigid_rigid, uu____9021)
  
let (next_prob :
  worklist ->
    (FStar_TypeChecker_Common.prob * FStar_TypeChecker_Common.prob Prims.list
      * FStar_TypeChecker_Common.rank_t) FStar_Pervasives_Native.option)
  =
  fun wl  ->
    let rec aux uu____9088 probs =
      match uu____9088 with
      | (min_rank,min1,out) ->
          (match probs with
           | [] ->
               (match (min1, min_rank) with
                | (FStar_Pervasives_Native.Some
                   p,FStar_Pervasives_Native.Some r) ->
                    FStar_Pervasives_Native.Some (p, out, r)
                | uu____9169 -> FStar_Pervasives_Native.None)
           | hd1::tl1 ->
               let uu____9190 = rank wl.tcenv hd1  in
               (match uu____9190 with
                | (rank1,hd2) ->
                    if rank_leq rank1 FStar_TypeChecker_Common.Flex_rigid_eq
                    then
                      (match min1 with
                       | FStar_Pervasives_Native.None  ->
                           FStar_Pervasives_Native.Some
                             (hd2, (FStar_List.append out tl1), rank1)
                       | FStar_Pervasives_Native.Some m ->
                           FStar_Pervasives_Native.Some
                             (hd2, (FStar_List.append out (m :: tl1)), rank1))
                    else
                      (let uu____9251 =
                         (min_rank = FStar_Pervasives_Native.None) ||
                           (let uu____9256 = FStar_Option.get min_rank  in
                            rank_less_than rank1 uu____9256)
                          in
                       if uu____9251
                       then
                         match min1 with
                         | FStar_Pervasives_Native.None  ->
                             aux
                               ((FStar_Pervasives_Native.Some rank1),
                                 (FStar_Pervasives_Native.Some hd2), out) tl1
                         | FStar_Pervasives_Native.Some m ->
                             aux
                               ((FStar_Pervasives_Native.Some rank1),
                                 (FStar_Pervasives_Native.Some hd2), (m ::
                                 out)) tl1
                       else aux (min_rank, min1, (hd2 :: out)) tl1)))
       in
    aux (FStar_Pervasives_Native.None, FStar_Pervasives_Native.None, [])
      wl.attempting
  
let (flex_prob_closing :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.binders ->
      FStar_TypeChecker_Common.prob -> Prims.bool)
  =
  fun tcenv  ->
    fun bs  ->
      fun p  ->
        let flex_will_be_closed t =
          let uu____9329 = FStar_Syntax_Util.head_and_args t  in
          match uu____9329 with
          | (hd1,uu____9348) ->
              let uu____9373 =
                let uu____9374 = FStar_Syntax_Subst.compress hd1  in
                uu____9374.FStar_Syntax_Syntax.n  in
              (match uu____9373 with
               | FStar_Syntax_Syntax.Tm_uvar (u,uu____9379) ->
                   FStar_All.pipe_right
                     u.FStar_Syntax_Syntax.ctx_uvar_binders
                     (FStar_Util.for_some
                        (fun uu____9414  ->
                           match uu____9414 with
                           | (y,uu____9423) ->
                               FStar_All.pipe_right bs
                                 (FStar_Util.for_some
                                    (fun uu____9446  ->
                                       match uu____9446 with
                                       | (x,uu____9455) ->
                                           FStar_Syntax_Syntax.bv_eq x y))))
               | uu____9460 -> false)
           in
        let uu____9462 = rank tcenv p  in
        match uu____9462 with
        | (r,p1) ->
            (match p1 with
             | FStar_TypeChecker_Common.CProb uu____9471 -> true
             | FStar_TypeChecker_Common.TProb p2 ->
                 (match r with
                  | FStar_TypeChecker_Common.Rigid_rigid  -> true
                  | FStar_TypeChecker_Common.Flex_rigid_eq  -> true
                  | FStar_TypeChecker_Common.Flex_flex_pattern_eq  -> true
                  | FStar_TypeChecker_Common.Flex_rigid  ->
                      flex_will_be_closed p2.FStar_TypeChecker_Common.lhs
                  | FStar_TypeChecker_Common.Rigid_flex  ->
                      flex_will_be_closed p2.FStar_TypeChecker_Common.rhs
                  | FStar_TypeChecker_Common.Flex_flex  ->
                      (p2.FStar_TypeChecker_Common.relation =
                         FStar_TypeChecker_Common.EQ)
                        &&
                        ((flex_will_be_closed p2.FStar_TypeChecker_Common.lhs)
                           ||
                           (flex_will_be_closed
                              p2.FStar_TypeChecker_Common.rhs))))
  
type univ_eq_sol =
  | UDeferred of worklist 
  | USolved of worklist 
  | UFailed of lstring 
let (uu___is_UDeferred : univ_eq_sol -> Prims.bool) =
  fun projectee  ->
    match projectee with | UDeferred _0 -> true | uu____9526 -> false
  
let (__proj__UDeferred__item___0 : univ_eq_sol -> worklist) =
  fun projectee  -> match projectee with | UDeferred _0 -> _0 
let (uu___is_USolved : univ_eq_sol -> Prims.bool) =
  fun projectee  ->
    match projectee with | USolved _0 -> true | uu____9545 -> false
  
let (__proj__USolved__item___0 : univ_eq_sol -> worklist) =
  fun projectee  -> match projectee with | USolved _0 -> _0 
let (uu___is_UFailed : univ_eq_sol -> Prims.bool) =
  fun projectee  ->
    match projectee with | UFailed _0 -> true | uu____9564 -> false
  
let (__proj__UFailed__item___0 : univ_eq_sol -> lstring) =
  fun projectee  -> match projectee with | UFailed _0 -> _0 
let (ufailed_simple : Prims.string -> univ_eq_sol) =
  fun s  -> let uu____9581 = FStar_Thunk.mkv s  in UFailed uu____9581 
let (ufailed_thunk : (unit -> Prims.string) -> univ_eq_sol) =
  fun s  -> let uu____9596 = FStar_Thunk.mk s  in UFailed uu____9596 
let rec (really_solve_universe_eq :
  Prims.int ->
    worklist ->
      FStar_Syntax_Syntax.universe ->
        FStar_Syntax_Syntax.universe -> univ_eq_sol)
  =
  fun pid_orig  ->
    fun wl  ->
      fun u1  ->
        fun u2  ->
          let u11 =
            FStar_TypeChecker_Normalize.normalize_universe wl.tcenv u1  in
          let u21 =
            FStar_TypeChecker_Normalize.normalize_universe wl.tcenv u2  in
          let rec occurs_univ v1 u =
            match u with
            | FStar_Syntax_Syntax.U_max us ->
                FStar_All.pipe_right us
                  (FStar_Util.for_some
                     (fun u3  ->
                        let uu____9648 = FStar_Syntax_Util.univ_kernel u3  in
                        match uu____9648 with
                        | (k,uu____9656) ->
                            (match k with
                             | FStar_Syntax_Syntax.U_unif v2 ->
                                 FStar_Syntax_Unionfind.univ_equiv v1 v2
                             | uu____9669 -> false)))
            | uu____9671 -> occurs_univ v1 (FStar_Syntax_Syntax.U_max [u])
             in
          let rec filter_out_common_univs u12 u22 =
            let common_elts =
              FStar_All.pipe_right u12
                (FStar_List.fold_left
                   (fun uvs  ->
                      fun uv1  ->
                        let uu____9723 =
                          FStar_All.pipe_right u22
                            (FStar_List.existsML
                               (fun uv2  ->
                                  let uu____9731 =
                                    FStar_Syntax_Util.compare_univs uv1 uv2
                                     in
                                  uu____9731 = Prims.int_zero))
                           in
                        if uu____9723 then uv1 :: uvs else uvs) [])
               in
            let filter1 =
              FStar_List.filter
                (fun u  ->
                   let uu____9752 =
                     FStar_All.pipe_right common_elts
                       (FStar_List.existsML
                          (fun u'  ->
                             let uu____9760 =
                               FStar_Syntax_Util.compare_univs u u'  in
                             uu____9760 = Prims.int_zero))
                      in
                   Prims.op_Negation uu____9752)
               in
            let uu____9764 = filter1 u12  in
            let uu____9767 = filter1 u22  in (uu____9764, uu____9767)  in
          let try_umax_components u12 u22 msg =
            if Prims.op_Negation wl.umax_heuristic_ok
            then ufailed_simple "Unable to unify universe terms with umax"
            else
              (match (u12, u22) with
               | (FStar_Syntax_Syntax.U_max us1,FStar_Syntax_Syntax.U_max
                  us2) ->
                   let uu____9802 = filter_out_common_univs us1 us2  in
                   (match uu____9802 with
                    | (us11,us21) ->
                        if
                          (FStar_List.length us11) = (FStar_List.length us21)
                        then
                          let rec aux wl1 us12 us22 =
                            match (us12, us22) with
                            | (u13::us13,u23::us23) ->
                                let uu____9862 =
                                  really_solve_universe_eq pid_orig wl1 u13
                                    u23
                                   in
                                (match uu____9862 with
                                 | USolved wl2 -> aux wl2 us13 us23
                                 | failed -> failed)
                            | uu____9865 -> USolved wl1  in
                          aux wl us11 us21
                        else
                          ufailed_thunk
                            (fun uu____9882  ->
                               let uu____9883 =
                                 FStar_Syntax_Print.univ_to_string u12  in
                               let uu____9885 =
                                 FStar_Syntax_Print.univ_to_string u22  in
                               FStar_Util.format2
                                 "Unable to unify universes: %s and %s"
                                 uu____9883 uu____9885))
               | (FStar_Syntax_Syntax.U_max us,u') ->
                   let rec aux wl1 us1 =
                     match us1 with
                     | [] -> USolved wl1
                     | u::us2 ->
                         let uu____9911 =
                           really_solve_universe_eq pid_orig wl1 u u'  in
                         (match uu____9911 with
                          | USolved wl2 -> aux wl2 us2
                          | failed -> failed)
                      in
                   aux wl us
               | (u',FStar_Syntax_Syntax.U_max us) ->
                   let rec aux wl1 us1 =
                     match us1 with
                     | [] -> USolved wl1
                     | u::us2 ->
                         let uu____9937 =
                           really_solve_universe_eq pid_orig wl1 u u'  in
                         (match uu____9937 with
                          | USolved wl2 -> aux wl2 us2
                          | failed -> failed)
                      in
                   aux wl us
               | uu____9940 ->
                   ufailed_thunk
                     (fun uu____9951  ->
                        let uu____9952 =
                          FStar_Syntax_Print.univ_to_string u12  in
                        let uu____9954 =
                          FStar_Syntax_Print.univ_to_string u22  in
                        FStar_Util.format3
                          "Unable to unify universes: %s and %s (%s)"
                          uu____9952 uu____9954 msg))
             in
          match (u11, u21) with
          | (FStar_Syntax_Syntax.U_bvar uu____9957,uu____9958) ->
              let uu____9960 =
                let uu____9962 = FStar_Syntax_Print.univ_to_string u11  in
                let uu____9964 = FStar_Syntax_Print.univ_to_string u21  in
                FStar_Util.format2
                  "Impossible: found an de Bruijn universe variable or unknown universe: %s, %s"
                  uu____9962 uu____9964
                 in
              failwith uu____9960
          | (FStar_Syntax_Syntax.U_unknown ,uu____9967) ->
              let uu____9968 =
                let uu____9970 = FStar_Syntax_Print.univ_to_string u11  in
                let uu____9972 = FStar_Syntax_Print.univ_to_string u21  in
                FStar_Util.format2
                  "Impossible: found an de Bruijn universe variable or unknown universe: %s, %s"
                  uu____9970 uu____9972
                 in
              failwith uu____9968
          | (uu____9975,FStar_Syntax_Syntax.U_bvar uu____9976) ->
              let uu____9978 =
                let uu____9980 = FStar_Syntax_Print.univ_to_string u11  in
                let uu____9982 = FStar_Syntax_Print.univ_to_string u21  in
                FStar_Util.format2
                  "Impossible: found an de Bruijn universe variable or unknown universe: %s, %s"
                  uu____9980 uu____9982
                 in
              failwith uu____9978
          | (uu____9985,FStar_Syntax_Syntax.U_unknown ) ->
              let uu____9986 =
                let uu____9988 = FStar_Syntax_Print.univ_to_string u11  in
                let uu____9990 = FStar_Syntax_Print.univ_to_string u21  in
                FStar_Util.format2
                  "Impossible: found an de Bruijn universe variable or unknown universe: %s, %s"
                  uu____9988 uu____9990
                 in
              failwith uu____9986
          | (FStar_Syntax_Syntax.U_name x,FStar_Syntax_Syntax.U_name y) ->
              if x.FStar_Ident.idText = y.FStar_Ident.idText
              then USolved wl
              else ufailed_simple "Incompatible universes"
          | (FStar_Syntax_Syntax.U_zero ,FStar_Syntax_Syntax.U_zero ) ->
              USolved wl
          | (FStar_Syntax_Syntax.U_succ u12,FStar_Syntax_Syntax.U_succ u22)
              -> really_solve_universe_eq pid_orig wl u12 u22
          | (FStar_Syntax_Syntax.U_unif v1,FStar_Syntax_Syntax.U_unif v2) ->
              let uu____10020 = FStar_Syntax_Unionfind.univ_equiv v1 v2  in
              if uu____10020
              then USolved wl
              else
                (let wl1 = extend_solution pid_orig [UNIV (v1, u21)] wl  in
                 USolved wl1)
          | (FStar_Syntax_Syntax.U_unif v1,u) ->
              let u3 = norm_univ wl u  in
              let uu____10037 = occurs_univ v1 u3  in
              if uu____10037
              then
                let uu____10040 =
                  let uu____10042 =
                    FStar_Syntax_Print.univ_to_string
                      (FStar_Syntax_Syntax.U_unif v1)
                     in
                  let uu____10044 = FStar_Syntax_Print.univ_to_string u3  in
                  FStar_Util.format2 "Failed occurs check: %s occurs in %s"
                    uu____10042 uu____10044
                   in
                try_umax_components u11 u21 uu____10040
              else
                (let uu____10049 =
                   extend_solution pid_orig [UNIV (v1, u3)] wl  in
                 USolved uu____10049)
          | (u,FStar_Syntax_Syntax.U_unif v1) ->
              let u3 = norm_univ wl u  in
              let uu____10061 = occurs_univ v1 u3  in
              if uu____10061
              then
                let uu____10064 =
                  let uu____10066 =
                    FStar_Syntax_Print.univ_to_string
                      (FStar_Syntax_Syntax.U_unif v1)
                     in
                  let uu____10068 = FStar_Syntax_Print.univ_to_string u3  in
                  FStar_Util.format2 "Failed occurs check: %s occurs in %s"
                    uu____10066 uu____10068
                   in
                try_umax_components u11 u21 uu____10064
              else
                (let uu____10073 =
                   extend_solution pid_orig [UNIV (v1, u3)] wl  in
                 USolved uu____10073)
          | (FStar_Syntax_Syntax.U_max uu____10074,uu____10075) ->
              if wl.defer_ok
              then UDeferred wl
              else
                (let u12 = norm_univ wl u11  in
                 let u22 = norm_univ wl u21  in
                 let uu____10083 = FStar_Syntax_Util.eq_univs u12 u22  in
                 if uu____10083
                 then USolved wl
                 else try_umax_components u12 u22 "")
          | (uu____10089,FStar_Syntax_Syntax.U_max uu____10090) ->
              if wl.defer_ok
              then UDeferred wl
              else
                (let u12 = norm_univ wl u11  in
                 let u22 = norm_univ wl u21  in
                 let uu____10098 = FStar_Syntax_Util.eq_univs u12 u22  in
                 if uu____10098
                 then USolved wl
                 else try_umax_components u12 u22 "")
          | (FStar_Syntax_Syntax.U_succ
             uu____10104,FStar_Syntax_Syntax.U_zero ) ->
              ufailed_simple "Incompatible universes"
          | (FStar_Syntax_Syntax.U_succ
             uu____10106,FStar_Syntax_Syntax.U_name uu____10107) ->
              ufailed_simple "Incompatible universes"
          | (FStar_Syntax_Syntax.U_zero ,FStar_Syntax_Syntax.U_succ
             uu____10109) -> ufailed_simple "Incompatible universes"
          | (FStar_Syntax_Syntax.U_zero ,FStar_Syntax_Syntax.U_name
             uu____10111) -> ufailed_simple "Incompatible universes"
          | (FStar_Syntax_Syntax.U_name
             uu____10113,FStar_Syntax_Syntax.U_succ uu____10114) ->
              ufailed_simple "Incompatible universes"
          | (FStar_Syntax_Syntax.U_name
             uu____10116,FStar_Syntax_Syntax.U_zero ) ->
              ufailed_simple "Incompatible universes"
  
let (solve_universe_eq :
  Prims.int ->
    worklist ->
      FStar_Syntax_Syntax.universe ->
        FStar_Syntax_Syntax.universe -> univ_eq_sol)
  =
  fun orig  ->
    fun wl  ->
      fun u1  ->
        fun u2  ->
          if (wl.tcenv).FStar_TypeChecker_Env.lax_universes
          then USolved wl
          else really_solve_universe_eq orig wl u1 u2
  
let match_num_binders :
  'a 'b .
    ('a Prims.list * ('a Prims.list -> 'b)) ->
      ('a Prims.list * ('a Prims.list -> 'b)) ->
        (('a Prims.list * 'b) * ('a Prims.list * 'b))
  =
  fun bc1  ->
    fun bc2  ->
      let uu____10223 = bc1  in
      match uu____10223 with
      | (bs1,mk_cod1) ->
          let uu____10267 = bc2  in
          (match uu____10267 with
           | (bs2,mk_cod2) ->
               let rec aux bs11 bs21 =
                 match (bs11, bs21) with
                 | (x::xs,y::ys) ->
                     let uu____10378 = aux xs ys  in
                     (match uu____10378 with
                      | ((xs1,xr),(ys1,yr)) ->
                          (((x :: xs1), xr), ((y :: ys1), yr)))
                 | (xs,ys) ->
                     let uu____10461 =
                       let uu____10468 = mk_cod1 xs  in ([], uu____10468)  in
                     let uu____10471 =
                       let uu____10478 = mk_cod2 ys  in ([], uu____10478)  in
                     (uu____10461, uu____10471)
                  in
               aux bs1 bs2)
  
let (guard_of_prob :
  FStar_TypeChecker_Env.env ->
    worklist ->
      tprob ->
        FStar_Syntax_Syntax.term ->
          FStar_Syntax_Syntax.term -> (FStar_Syntax_Syntax.term * worklist))
  =
  fun env  ->
    fun wl  ->
      fun problem  ->
        fun t1  ->
          fun t2  ->
            let has_type_guard t11 t21 =
              match problem.FStar_TypeChecker_Common.element with
              | FStar_Pervasives_Native.Some t ->
                  let uu____10547 = FStar_Syntax_Syntax.bv_to_name t  in
                  FStar_Syntax_Util.mk_has_type t11 uu____10547 t21
              | FStar_Pervasives_Native.None  ->
                  let x =
                    FStar_Syntax_Syntax.new_bv FStar_Pervasives_Native.None
                      t11
                     in
                  let u_x = env.FStar_TypeChecker_Env.universe_of env t11  in
                  let uu____10550 =
                    let uu____10551 = FStar_Syntax_Syntax.bv_to_name x  in
                    FStar_Syntax_Util.mk_has_type t11 uu____10551 t21  in
                  FStar_Syntax_Util.mk_forall u_x x uu____10550
               in
            match problem.FStar_TypeChecker_Common.relation with
            | FStar_TypeChecker_Common.EQ  ->
                mk_eq2 wl env (FStar_TypeChecker_Common.TProb problem) t1 t2
            | FStar_TypeChecker_Common.SUB  ->
                let uu____10556 = has_type_guard t1 t2  in (uu____10556, wl)
            | FStar_TypeChecker_Common.SUBINV  ->
                let uu____10557 = has_type_guard t2 t1  in (uu____10557, wl)
  
let is_flex_pat :
  'Auu____10567 'Auu____10568 'Auu____10569 .
    ('Auu____10567 * 'Auu____10568 * 'Auu____10569 Prims.list) -> Prims.bool
  =
  fun uu___25_10583  ->
    match uu___25_10583 with
    | (uu____10592,uu____10593,[]) -> true
    | uu____10597 -> false
  
let (quasi_pattern :
  FStar_TypeChecker_Env.env ->
    flex_t ->
      (FStar_Syntax_Syntax.binders * FStar_Syntax_Syntax.typ)
        FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun f  ->
      let uu____10630 = f  in
      match uu____10630 with
      | (uu____10637,{ FStar_Syntax_Syntax.ctx_uvar_head = uu____10638;
                       FStar_Syntax_Syntax.ctx_uvar_gamma = uu____10639;
                       FStar_Syntax_Syntax.ctx_uvar_binders = ctx;
                       FStar_Syntax_Syntax.ctx_uvar_typ = t_hd;
                       FStar_Syntax_Syntax.ctx_uvar_reason = uu____10642;
                       FStar_Syntax_Syntax.ctx_uvar_should_check =
                         uu____10643;
                       FStar_Syntax_Syntax.ctx_uvar_range = uu____10644;
                       FStar_Syntax_Syntax.ctx_uvar_meta = uu____10645;_},args)
          ->
          let name_exists_in x bs =
            FStar_Util.for_some
              (fun uu____10715  ->
                 match uu____10715 with
                 | (y,uu____10724) -> FStar_Syntax_Syntax.bv_eq x y) bs
             in
          let rec aux pat_binders formals t_res args1 =
            match (formals, args1) with
            | ([],[]) ->
                let uu____10878 =
                  let uu____10893 =
                    let uu____10896 = FStar_Syntax_Syntax.mk_Total t_res  in
                    FStar_Syntax_Util.arrow formals uu____10896  in
                  ((FStar_List.rev pat_binders), uu____10893)  in
                FStar_Pervasives_Native.Some uu____10878
            | (uu____10929,[]) ->
                let uu____10960 =
                  let uu____10975 =
                    let uu____10978 = FStar_Syntax_Syntax.mk_Total t_res  in
                    FStar_Syntax_Util.arrow formals uu____10978  in
                  ((FStar_List.rev pat_binders), uu____10975)  in
                FStar_Pervasives_Native.Some uu____10960
            | ((formal,formal_imp)::formals1,(a,a_imp)::args2) ->
                let uu____11069 =
                  let uu____11070 = FStar_Syntax_Subst.compress a  in
                  uu____11070.FStar_Syntax_Syntax.n  in
                (match uu____11069 with
                 | FStar_Syntax_Syntax.Tm_name x ->
                     let uu____11090 =
                       (name_exists_in x ctx) ||
                         (name_exists_in x pat_binders)
                        in
                     if uu____11090
                     then
                       aux ((formal, formal_imp) :: pat_binders) formals1
                         t_res args2
                     else
                       (let x1 =
                          let uu___1614_11120 = x  in
                          {
                            FStar_Syntax_Syntax.ppname =
                              (uu___1614_11120.FStar_Syntax_Syntax.ppname);
                            FStar_Syntax_Syntax.index =
                              (uu___1614_11120.FStar_Syntax_Syntax.index);
                            FStar_Syntax_Syntax.sort =
                              (formal.FStar_Syntax_Syntax.sort)
                          }  in
                        let subst1 =
                          let uu____11124 =
                            let uu____11125 =
                              let uu____11132 =
                                FStar_Syntax_Syntax.bv_to_name x1  in
                              (formal, uu____11132)  in
                            FStar_Syntax_Syntax.NT uu____11125  in
                          [uu____11124]  in
                        let formals2 =
                          FStar_Syntax_Subst.subst_binders subst1 formals1
                           in
                        let t_res1 = FStar_Syntax_Subst.subst subst1 t_res
                           in
                        aux
                          (((let uu___1620_11148 = x1  in
                             {
                               FStar_Syntax_Syntax.ppname =
                                 (uu___1620_11148.FStar_Syntax_Syntax.ppname);
                               FStar_Syntax_Syntax.index =
                                 (uu___1620_11148.FStar_Syntax_Syntax.index);
                               FStar_Syntax_Syntax.sort =
                                 (formal.FStar_Syntax_Syntax.sort)
                             }), a_imp) :: pat_binders) formals2 t_res1 args2)
                 | uu____11149 ->
                     aux ((formal, formal_imp) :: pat_binders) formals1 t_res
                       args2)
            | ([],args2) ->
                let uu____11189 =
                  let uu____11204 =
                    FStar_TypeChecker_Normalize.unfold_whnf env t_res  in
                  FStar_Syntax_Util.arrow_formals uu____11204  in
                (match uu____11189 with
                 | (more_formals,t_res1) ->
                     (match more_formals with
                      | [] -> FStar_Pervasives_Native.None
                      | uu____11279 ->
                          aux pat_binders more_formals t_res1 args2))
             in
          (match args with
           | [] -> FStar_Pervasives_Native.Some ([], t_hd)
           | uu____11312 ->
               let uu____11313 = FStar_Syntax_Util.arrow_formals t_hd  in
               (match uu____11313 with
                | (formals,t_res) -> aux [] formals t_res args))
  
let rec (solve : FStar_TypeChecker_Env.env -> worklist -> solution) =
  fun env  ->
    fun probs  ->
      (let uu____11637 =
         FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
           (FStar_Options.Other "Rel")
          in
       if uu____11637
       then
         let uu____11642 = wl_to_string probs  in
         FStar_Util.print1 "solve:\n\t%s\n" uu____11642
       else ());
      (let uu____11647 = next_prob probs  in
       match uu____11647 with
       | FStar_Pervasives_Native.Some (hd1,tl1,rank1) ->
           let probs1 =
             let uu___1645_11674 = probs  in
             {
               attempting = tl1;
               wl_deferred = (uu___1645_11674.wl_deferred);
               ctr = (uu___1645_11674.ctr);
               defer_ok = (uu___1645_11674.defer_ok);
               smt_ok = (uu___1645_11674.smt_ok);
               umax_heuristic_ok = (uu___1645_11674.umax_heuristic_ok);
               tcenv = (uu___1645_11674.tcenv);
               wl_implicits = (uu___1645_11674.wl_implicits)
             }  in
           (def_check_prob "solve,hd" hd1;
            (match hd1 with
             | FStar_TypeChecker_Common.CProb cp ->
                 solve_c env (maybe_invert cp) probs1
             | FStar_TypeChecker_Common.TProb tp ->
                 let uu____11683 =
                   FStar_Util.physical_equality
                     tp.FStar_TypeChecker_Common.lhs
                     tp.FStar_TypeChecker_Common.rhs
                    in
                 if uu____11683
                 then
                   let uu____11686 =
                     solve_prob hd1 FStar_Pervasives_Native.None [] probs1
                      in
                   solve env uu____11686
                 else
                   if
                     (rank1 = FStar_TypeChecker_Common.Rigid_rigid) ||
                       ((tp.FStar_TypeChecker_Common.relation =
                           FStar_TypeChecker_Common.EQ)
                          && (rank1 <> FStar_TypeChecker_Common.Flex_flex))
                   then solve_t env tp probs1
                   else
                     if probs1.defer_ok
                     then
                       (let uu____11693 =
                          defer_lit
                            "deferring flex_rigid or flex_flex subtyping" hd1
                            probs1
                           in
                        solve env uu____11693)
                     else
                       if rank1 = FStar_TypeChecker_Common.Flex_flex
                       then
                         solve_t env
                           (let uu___1657_11699 = tp  in
                            {
                              FStar_TypeChecker_Common.pid =
                                (uu___1657_11699.FStar_TypeChecker_Common.pid);
                              FStar_TypeChecker_Common.lhs =
                                (uu___1657_11699.FStar_TypeChecker_Common.lhs);
                              FStar_TypeChecker_Common.relation =
                                FStar_TypeChecker_Common.EQ;
                              FStar_TypeChecker_Common.rhs =
                                (uu___1657_11699.FStar_TypeChecker_Common.rhs);
                              FStar_TypeChecker_Common.element =
                                (uu___1657_11699.FStar_TypeChecker_Common.element);
                              FStar_TypeChecker_Common.logical_guard =
                                (uu___1657_11699.FStar_TypeChecker_Common.logical_guard);
                              FStar_TypeChecker_Common.logical_guard_uvar =
                                (uu___1657_11699.FStar_TypeChecker_Common.logical_guard_uvar);
                              FStar_TypeChecker_Common.reason =
                                (uu___1657_11699.FStar_TypeChecker_Common.reason);
                              FStar_TypeChecker_Common.loc =
                                (uu___1657_11699.FStar_TypeChecker_Common.loc);
                              FStar_TypeChecker_Common.rank =
                                (uu___1657_11699.FStar_TypeChecker_Common.rank)
                            }) probs1
                       else
                         solve_rigid_flex_or_flex_rigid_subtyping rank1 env
                           tp probs1))
       | FStar_Pervasives_Native.None  ->
           (match probs.wl_deferred with
            | [] -> Success ([], (probs.wl_implicits))
            | uu____11724 ->
                let uu____11734 =
                  FStar_All.pipe_right probs.wl_deferred
                    (FStar_List.partition
                       (fun uu____11799  ->
                          match uu____11799 with
                          | (c,uu____11809,uu____11810) -> c < probs.ctr))
                   in
                (match uu____11734 with
                 | (attempt1,rest) ->
                     (match attempt1 with
                      | [] ->
                          let uu____11858 =
                            let uu____11863 =
                              FStar_List.map
                                (fun uu____11884  ->
                                   match uu____11884 with
                                   | (uu____11900,x,y) ->
                                       let uu____11911 = FStar_Thunk.force x
                                          in
                                       (uu____11911, y)) probs.wl_deferred
                               in
                            (uu____11863, (probs.wl_implicits))  in
                          Success uu____11858
                      | uu____11915 ->
                          let uu____11925 =
                            let uu___1675_11926 = probs  in
                            let uu____11927 =
                              FStar_All.pipe_right attempt1
                                (FStar_List.map
                                   (fun uu____11948  ->
                                      match uu____11948 with
                                      | (uu____11956,uu____11957,y) -> y))
                               in
                            {
                              attempting = uu____11927;
                              wl_deferred = rest;
                              ctr = (uu___1675_11926.ctr);
                              defer_ok = (uu___1675_11926.defer_ok);
                              smt_ok = (uu___1675_11926.smt_ok);
                              umax_heuristic_ok =
                                (uu___1675_11926.umax_heuristic_ok);
                              tcenv = (uu___1675_11926.tcenv);
                              wl_implicits = (uu___1675_11926.wl_implicits)
                            }  in
                          solve env uu____11925))))

and (solve_one_universe_eq :
  FStar_TypeChecker_Env.env ->
    FStar_TypeChecker_Common.prob ->
      FStar_Syntax_Syntax.universe ->
        FStar_Syntax_Syntax.universe -> worklist -> solution)
  =
  fun env  ->
    fun orig  ->
      fun u1  ->
        fun u2  ->
          fun wl  ->
            let uu____11966 = solve_universe_eq (p_pid orig) wl u1 u2  in
            match uu____11966 with
            | USolved wl1 ->
                let uu____11968 =
                  solve_prob orig FStar_Pervasives_Native.None [] wl1  in
                solve env uu____11968
            | UFailed msg -> giveup env msg orig
            | UDeferred wl1 ->
                let uu____11971 = defer_lit "" orig wl1  in
                solve env uu____11971

and (solve_maybe_uinsts :
  FStar_TypeChecker_Env.env ->
    FStar_TypeChecker_Common.prob ->
      FStar_Syntax_Syntax.term ->
        FStar_Syntax_Syntax.term -> worklist -> univ_eq_sol)
  =
  fun env  ->
    fun orig  ->
      fun t1  ->
        fun t2  ->
          fun wl  ->
            let rec aux wl1 us1 us2 =
              match (us1, us2) with
              | ([],[]) -> USolved wl1
              | (u1::us11,u2::us21) ->
                  let uu____12022 = solve_universe_eq (p_pid orig) wl1 u1 u2
                     in
                  (match uu____12022 with
                   | USolved wl2 -> aux wl2 us11 us21
                   | failed_or_deferred -> failed_or_deferred)
              | uu____12025 -> ufailed_simple "Unequal number of universes"
               in
            let t11 = whnf env t1  in
            let t21 = whnf env t2  in
            match ((t11.FStar_Syntax_Syntax.n), (t21.FStar_Syntax_Syntax.n))
            with
            | (FStar_Syntax_Syntax.Tm_uinst
               ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar f;
                  FStar_Syntax_Syntax.pos = uu____12038;
                  FStar_Syntax_Syntax.vars = uu____12039;_},us1),FStar_Syntax_Syntax.Tm_uinst
               ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar g;
                  FStar_Syntax_Syntax.pos = uu____12042;
                  FStar_Syntax_Syntax.vars = uu____12043;_},us2))
                -> let b = FStar_Syntax_Syntax.fv_eq f g  in aux wl us1 us2
            | (FStar_Syntax_Syntax.Tm_uinst uu____12056,uu____12057) ->
                failwith "Impossible: expect head symbols to match"
            | (uu____12065,FStar_Syntax_Syntax.Tm_uinst uu____12066) ->
                failwith "Impossible: expect head symbols to match"
            | uu____12074 -> USolved wl

and (giveup_or_defer :
  FStar_TypeChecker_Env.env ->
    FStar_TypeChecker_Common.prob -> worklist -> lstring -> solution)
  =
  fun env  ->
    fun orig  ->
      fun wl  ->
        fun msg  ->
          if wl.defer_ok
          then
            ((let uu____12085 =
                FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                  (FStar_Options.Other "Rel")
                 in
              if uu____12085
              then
                let uu____12090 = prob_to_string env orig  in
                let uu____12092 = FStar_Thunk.force msg  in
                FStar_Util.print2 "\n\t\tDeferring %s\n\t\tBecause %s\n"
                  uu____12090 uu____12092
              else ());
             solve env (defer msg orig wl))
          else giveup env msg orig

and (solve_rigid_flex_or_flex_rigid_subtyping :
  FStar_TypeChecker_Common.rank_t ->
    FStar_TypeChecker_Env.env -> tprob -> worklist -> solution)
  =
  fun rank1  ->
    fun env  ->
      fun tp  ->
        fun wl  ->
          def_check_prob "solve_rigid_flex_or_flex_rigid_subtyping"
            (FStar_TypeChecker_Common.TProb tp);
          (let flip = rank1 = FStar_TypeChecker_Common.Flex_rigid  in
           let meet_or_join op ts env1 wl1 =
             let eq_prob t1 t2 wl2 =
               let uu____12185 =
                 new_problem wl2 env1 t1 FStar_TypeChecker_Common.EQ t2
                   FStar_Pervasives_Native.None t1.FStar_Syntax_Syntax.pos
                   "join/meet refinements"
                  in
               match uu____12185 with
               | (p,wl3) ->
                   (def_check_prob "meet_or_join"
                      (FStar_TypeChecker_Common.TProb p);
                    ((FStar_TypeChecker_Common.TProb p), wl3))
                in
             let pairwise t1 t2 wl2 =
               (let uu____12240 =
                  FStar_All.pipe_left (FStar_TypeChecker_Env.debug env1)
                    (FStar_Options.Other "Rel")
                   in
                if uu____12240
                then
                  let uu____12245 = FStar_Syntax_Print.term_to_string t1  in
                  let uu____12247 = FStar_Syntax_Print.term_to_string t2  in
                  FStar_Util.print2 "[meet/join]: pairwise: %s and %s\n"
                    uu____12245 uu____12247
                else ());
               (let uu____12252 = head_matches_delta env1 wl2 t1 t2  in
                match uu____12252 with
                | (mr,ts1) ->
                    (match mr with
                     | HeadMatch (true ) ->
                         let uu____12298 = eq_prob t1 t2 wl2  in
                         (match uu____12298 with | (p,wl3) -> (t1, [p], wl3))
                     | MisMatch uu____12319 ->
                         let uu____12328 = eq_prob t1 t2 wl2  in
                         (match uu____12328 with | (p,wl3) -> (t1, [p], wl3))
                     | FullMatch  ->
                         (match ts1 with
                          | FStar_Pervasives_Native.None  -> (t1, [], wl2)
                          | FStar_Pervasives_Native.Some (t11,t21) ->
                              (t11, [], wl2))
                     | HeadMatch (false ) ->
                         let uu____12378 =
                           match ts1 with
                           | FStar_Pervasives_Native.Some (t11,t21) ->
                               let uu____12393 =
                                 FStar_Syntax_Subst.compress t11  in
                               let uu____12394 =
                                 FStar_Syntax_Subst.compress t21  in
                               (uu____12393, uu____12394)
                           | FStar_Pervasives_Native.None  ->
                               let uu____12399 =
                                 FStar_Syntax_Subst.compress t1  in
                               let uu____12400 =
                                 FStar_Syntax_Subst.compress t2  in
                               (uu____12399, uu____12400)
                            in
                         (match uu____12378 with
                          | (t11,t21) ->
                              let try_eq t12 t22 wl3 =
                                let uu____12431 =
                                  FStar_Syntax_Util.head_and_args t12  in
                                match uu____12431 with
                                | (t1_hd,t1_args) ->
                                    let uu____12476 =
                                      FStar_Syntax_Util.head_and_args t22  in
                                    (match uu____12476 with
                                     | (t2_hd,t2_args) ->
                                         if
                                           (FStar_List.length t1_args) <>
                                             (FStar_List.length t2_args)
                                         then FStar_Pervasives_Native.None
                                         else
                                           (let uu____12542 =
                                              let uu____12549 =
                                                let uu____12560 =
                                                  FStar_Syntax_Syntax.as_arg
                                                    t1_hd
                                                   in
                                                uu____12560 :: t1_args  in
                                              let uu____12577 =
                                                let uu____12586 =
                                                  FStar_Syntax_Syntax.as_arg
                                                    t2_hd
                                                   in
                                                uu____12586 :: t2_args  in
                                              FStar_List.fold_left2
                                                (fun uu____12635  ->
                                                   fun uu____12636  ->
                                                     fun uu____12637  ->
                                                       match (uu____12635,
                                                               uu____12636,
                                                               uu____12637)
                                                       with
                                                       | ((probs,wl4),
                                                          (a1,uu____12687),
                                                          (a2,uu____12689))
                                                           ->
                                                           let uu____12726 =
                                                             eq_prob a1 a2
                                                               wl4
                                                              in
                                                           (match uu____12726
                                                            with
                                                            | (p,wl5) ->
                                                                ((p ::
                                                                  probs),
                                                                  wl5)))
                                                ([], wl3) uu____12549
                                                uu____12577
                                               in
                                            match uu____12542 with
                                            | (probs,wl4) ->
                                                let wl' =
                                                  let uu___1829_12752 = wl4
                                                     in
                                                  {
                                                    attempting = probs;
                                                    wl_deferred = [];
                                                    ctr =
                                                      (uu___1829_12752.ctr);
                                                    defer_ok = false;
                                                    smt_ok = false;
                                                    umax_heuristic_ok =
                                                      (uu___1829_12752.umax_heuristic_ok);
                                                    tcenv =
                                                      (uu___1829_12752.tcenv);
                                                    wl_implicits = []
                                                  }  in
                                                let tx =
                                                  FStar_Syntax_Unionfind.new_transaction
                                                    ()
                                                   in
                                                let uu____12763 =
                                                  solve env1 wl'  in
                                                (match uu____12763 with
                                                 | Success (uu____12766,imps)
                                                     ->
                                                     (FStar_Syntax_Unionfind.commit
                                                        tx;
                                                      FStar_Pervasives_Native.Some
                                                        ((let uu___1838_12770
                                                            = wl4  in
                                                          {
                                                            attempting =
                                                              (uu___1838_12770.attempting);
                                                            wl_deferred =
                                                              (uu___1838_12770.wl_deferred);
                                                            ctr =
                                                              (uu___1838_12770.ctr);
                                                            defer_ok =
                                                              (uu___1838_12770.defer_ok);
                                                            smt_ok =
                                                              (uu___1838_12770.smt_ok);
                                                            umax_heuristic_ok
                                                              =
                                                              (uu___1838_12770.umax_heuristic_ok);
                                                            tcenv =
                                                              (uu___1838_12770.tcenv);
                                                            wl_implicits =
                                                              (FStar_List.append
                                                                 wl4.wl_implicits
                                                                 imps)
                                                          })))
                                                 | Failed uu____12771 ->
                                                     (FStar_Syntax_Unionfind.rollback
                                                        tx;
                                                      FStar_Pervasives_Native.None))))
                                 in
                              let combine t12 t22 wl3 =
                                let uu____12803 =
                                  base_and_refinement_maybe_delta false env1
                                    t12
                                   in
                                match uu____12803 with
                                | (t1_base,p1_opt) ->
                                    let uu____12839 =
                                      base_and_refinement_maybe_delta false
                                        env1 t22
                                       in
                                    (match uu____12839 with
                                     | (t2_base,p2_opt) ->
                                         let combine_refinements t_base
                                           p1_opt1 p2_opt1 =
                                           let refine1 x t =
                                             let uu____12938 =
                                               FStar_Syntax_Util.is_t_true t
                                                in
                                             if uu____12938
                                             then x.FStar_Syntax_Syntax.sort
                                             else
                                               FStar_Syntax_Util.refine x t
                                              in
                                           match (p1_opt1, p2_opt1) with
                                           | (FStar_Pervasives_Native.Some
                                              (x,phi1),FStar_Pervasives_Native.Some
                                              (y,phi2)) ->
                                               let x1 =
                                                 FStar_Syntax_Syntax.freshen_bv
                                                   x
                                                  in
                                               let subst1 =
                                                 [FStar_Syntax_Syntax.DB
                                                    (Prims.int_zero, x1)]
                                                  in
                                               let phi11 =
                                                 FStar_Syntax_Subst.subst
                                                   subst1 phi1
                                                  in
                                               let phi21 =
                                                 FStar_Syntax_Subst.subst
                                                   subst1 phi2
                                                  in
                                               let uu____12991 =
                                                 op phi11 phi21  in
                                               refine1 x1 uu____12991
                                           | (FStar_Pervasives_Native.None
                                              ,FStar_Pervasives_Native.Some
                                              (x,phi)) ->
                                               let x1 =
                                                 FStar_Syntax_Syntax.freshen_bv
                                                   x
                                                  in
                                               let subst1 =
                                                 [FStar_Syntax_Syntax.DB
                                                    (Prims.int_zero, x1)]
                                                  in
                                               let phi1 =
                                                 FStar_Syntax_Subst.subst
                                                   subst1 phi
                                                  in
                                               let uu____13023 =
                                                 op FStar_Syntax_Util.t_true
                                                   phi1
                                                  in
                                               refine1 x1 uu____13023
                                           | (FStar_Pervasives_Native.Some
                                              (x,phi),FStar_Pervasives_Native.None
                                              ) ->
                                               let x1 =
                                                 FStar_Syntax_Syntax.freshen_bv
                                                   x
                                                  in
                                               let subst1 =
                                                 [FStar_Syntax_Syntax.DB
                                                    (Prims.int_zero, x1)]
                                                  in
                                               let phi1 =
                                                 FStar_Syntax_Subst.subst
                                                   subst1 phi
                                                  in
                                               let uu____13055 =
                                                 op FStar_Syntax_Util.t_true
                                                   phi1
                                                  in
                                               refine1 x1 uu____13055
                                           | uu____13058 -> t_base  in
                                         let uu____13075 =
                                           try_eq t1_base t2_base wl3  in
                                         (match uu____13075 with
                                          | FStar_Pervasives_Native.Some wl4
                                              ->
                                              let uu____13089 =
                                                combine_refinements t1_base
                                                  p1_opt p2_opt
                                                 in
                                              (uu____13089, [], wl4)
                                          | FStar_Pervasives_Native.None  ->
                                              let uu____13096 =
                                                base_and_refinement_maybe_delta
                                                  true env1 t12
                                                 in
                                              (match uu____13096 with
                                               | (t1_base1,p1_opt1) ->
                                                   let uu____13132 =
                                                     base_and_refinement_maybe_delta
                                                       true env1 t22
                                                      in
                                                   (match uu____13132 with
                                                    | (t2_base1,p2_opt1) ->
                                                        let uu____13168 =
                                                          eq_prob t1_base1
                                                            t2_base1 wl3
                                                           in
                                                        (match uu____13168
                                                         with
                                                         | (p,wl4) ->
                                                             let t =
                                                               combine_refinements
                                                                 t1_base1
                                                                 p1_opt1
                                                                 p2_opt1
                                                                in
                                                             (t, [p], wl4))))))
                                 in
                              let uu____13192 = combine t11 t21 wl2  in
                              (match uu____13192 with
                               | (t12,ps,wl3) ->
                                   ((let uu____13225 =
                                       FStar_All.pipe_left
                                         (FStar_TypeChecker_Env.debug env1)
                                         (FStar_Options.Other "Rel")
                                        in
                                     if uu____13225
                                     then
                                       let uu____13230 =
                                         FStar_Syntax_Print.term_to_string
                                           t12
                                          in
                                       FStar_Util.print1
                                         "pairwise fallback2 succeeded: %s"
                                         uu____13230
                                     else ());
                                    (t12, ps, wl3))))))
                in
             let rec aux uu____13272 ts1 =
               match uu____13272 with
               | (out,probs,wl2) ->
                   (match ts1 with
                    | [] -> (out, probs, wl2)
                    | t::ts2 ->
                        let uu____13335 = pairwise out t wl2  in
                        (match uu____13335 with
                         | (out1,probs',wl3) ->
                             aux
                               (out1, (FStar_List.append probs probs'), wl3)
                               ts2))
                in
             let uu____13371 =
               let uu____13382 = FStar_List.hd ts  in (uu____13382, [], wl1)
                in
             let uu____13391 = FStar_List.tl ts  in
             aux uu____13371 uu____13391  in
           let uu____13398 =
             if flip
             then
               ((tp.FStar_TypeChecker_Common.lhs),
                 (tp.FStar_TypeChecker_Common.rhs))
             else
               ((tp.FStar_TypeChecker_Common.rhs),
                 (tp.FStar_TypeChecker_Common.lhs))
              in
           match uu____13398 with
           | (this_flex,this_rigid) ->
               let uu____13424 =
                 let uu____13425 = FStar_Syntax_Subst.compress this_rigid  in
                 uu____13425.FStar_Syntax_Syntax.n  in
               (match uu____13424 with
                | FStar_Syntax_Syntax.Tm_arrow (_bs,comp) ->
                    let uu____13450 =
                      FStar_Syntax_Util.is_tot_or_gtot_comp comp  in
                    if uu____13450
                    then
                      let uu____13453 = destruct_flex_t this_flex wl  in
                      (match uu____13453 with
                       | (flex,wl1) ->
                           let uu____13460 = quasi_pattern env flex  in
                           (match uu____13460 with
                            | FStar_Pervasives_Native.None  ->
                                giveup_lit env
                                  "flex-arrow subtyping, not a quasi pattern"
                                  (FStar_TypeChecker_Common.TProb tp)
                            | FStar_Pervasives_Native.Some (flex_bs,flex_t)
                                ->
                                ((let uu____13479 =
                                    FStar_All.pipe_left
                                      (FStar_TypeChecker_Env.debug env)
                                      (FStar_Options.Other "Rel")
                                     in
                                  if uu____13479
                                  then
                                    let uu____13484 =
                                      FStar_Util.string_of_int
                                        tp.FStar_TypeChecker_Common.pid
                                       in
                                    FStar_Util.print1
                                      "Trying to solve by imitating arrow:%s\n"
                                      uu____13484
                                  else ());
                                 imitate_arrow
                                   (FStar_TypeChecker_Common.TProb tp) env
                                   wl1 flex flex_bs flex_t
                                   tp.FStar_TypeChecker_Common.relation
                                   this_rigid)))
                    else
                      (let uu____13491 =
                         attempt
                           [FStar_TypeChecker_Common.TProb
                              ((let uu___1940_13494 = tp  in
                                {
                                  FStar_TypeChecker_Common.pid =
                                    (uu___1940_13494.FStar_TypeChecker_Common.pid);
                                  FStar_TypeChecker_Common.lhs =
                                    (uu___1940_13494.FStar_TypeChecker_Common.lhs);
                                  FStar_TypeChecker_Common.relation =
                                    FStar_TypeChecker_Common.EQ;
                                  FStar_TypeChecker_Common.rhs =
                                    (uu___1940_13494.FStar_TypeChecker_Common.rhs);
                                  FStar_TypeChecker_Common.element =
                                    (uu___1940_13494.FStar_TypeChecker_Common.element);
                                  FStar_TypeChecker_Common.logical_guard =
                                    (uu___1940_13494.FStar_TypeChecker_Common.logical_guard);
                                  FStar_TypeChecker_Common.logical_guard_uvar
                                    =
                                    (uu___1940_13494.FStar_TypeChecker_Common.logical_guard_uvar);
                                  FStar_TypeChecker_Common.reason =
                                    (uu___1940_13494.FStar_TypeChecker_Common.reason);
                                  FStar_TypeChecker_Common.loc =
                                    (uu___1940_13494.FStar_TypeChecker_Common.loc);
                                  FStar_TypeChecker_Common.rank =
                                    (uu___1940_13494.FStar_TypeChecker_Common.rank)
                                }))] wl
                          in
                       solve env uu____13491)
                | uu____13495 ->
                    ((let uu____13497 =
                        FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                          (FStar_Options.Other "Rel")
                         in
                      if uu____13497
                      then
                        let uu____13502 =
                          FStar_Util.string_of_int
                            tp.FStar_TypeChecker_Common.pid
                           in
                        FStar_Util.print1
                          "Trying to solve by meeting refinements:%s\n"
                          uu____13502
                      else ());
                     (let uu____13507 =
                        FStar_Syntax_Util.head_and_args this_flex  in
                      match uu____13507 with
                      | (u,_args) ->
                          let uu____13550 =
                            let uu____13551 = FStar_Syntax_Subst.compress u
                               in
                            uu____13551.FStar_Syntax_Syntax.n  in
                          (match uu____13550 with
                           | FStar_Syntax_Syntax.Tm_uvar (ctx_uvar,_subst) ->
                               let equiv1 t =
                                 let uu____13579 =
                                   FStar_Syntax_Util.head_and_args t  in
                                 match uu____13579 with
                                 | (u',uu____13598) ->
                                     let uu____13623 =
                                       let uu____13624 = whnf env u'  in
                                       uu____13624.FStar_Syntax_Syntax.n  in
                                     (match uu____13623 with
                                      | FStar_Syntax_Syntax.Tm_uvar
                                          (ctx_uvar',_subst') ->
                                          FStar_Syntax_Unionfind.equiv
                                            ctx_uvar.FStar_Syntax_Syntax.ctx_uvar_head
                                            ctx_uvar'.FStar_Syntax_Syntax.ctx_uvar_head
                                      | uu____13646 -> false)
                                  in
                               let uu____13648 =
                                 FStar_All.pipe_right wl.attempting
                                   (FStar_List.partition
                                      (fun uu___26_13671  ->
                                         match uu___26_13671 with
                                         | FStar_TypeChecker_Common.TProb tp1
                                             ->
                                             let tp2 = maybe_invert tp1  in
                                             (match tp2.FStar_TypeChecker_Common.rank
                                              with
                                              | FStar_Pervasives_Native.Some
                                                  rank' when rank1 = rank' ->
                                                  if flip
                                                  then
                                                    equiv1
                                                      tp2.FStar_TypeChecker_Common.lhs
                                                  else
                                                    equiv1
                                                      tp2.FStar_TypeChecker_Common.rhs
                                              | uu____13685 -> false)
                                         | uu____13689 -> false))
                                  in
                               (match uu____13648 with
                                | (bounds_probs,rest) ->
                                    let bounds_typs =
                                      let uu____13704 = whnf env this_rigid
                                         in
                                      let uu____13705 =
                                        FStar_List.collect
                                          (fun uu___27_13711  ->
                                             match uu___27_13711 with
                                             | FStar_TypeChecker_Common.TProb
                                                 p ->
                                                 let uu____13717 =
                                                   if flip
                                                   then
                                                     whnf env
                                                       (maybe_invert p).FStar_TypeChecker_Common.rhs
                                                   else
                                                     whnf env
                                                       (maybe_invert p).FStar_TypeChecker_Common.lhs
                                                    in
                                                 [uu____13717]
                                             | uu____13721 -> [])
                                          bounds_probs
                                         in
                                      uu____13704 :: uu____13705  in
                                    let uu____13722 =
                                      meet_or_join
                                        (if flip
                                         then FStar_Syntax_Util.mk_conj_simp
                                         else FStar_Syntax_Util.mk_disj_simp)
                                        bounds_typs env wl
                                       in
                                    (match uu____13722 with
                                     | (bound,sub_probs,wl1) ->
                                         let uu____13755 =
                                           let flex_u =
                                             flex_uvar_head this_flex  in
                                           let bound1 =
                                             let uu____13770 =
                                               let uu____13771 =
                                                 FStar_Syntax_Subst.compress
                                                   bound
                                                  in
                                               uu____13771.FStar_Syntax_Syntax.n
                                                in
                                             match uu____13770 with
                                             | FStar_Syntax_Syntax.Tm_refine
                                                 (x,phi) when
                                                 (tp.FStar_TypeChecker_Common.relation
                                                    =
                                                    FStar_TypeChecker_Common.SUB)
                                                   &&
                                                   (let uu____13783 =
                                                      occurs flex_u
                                                        x.FStar_Syntax_Syntax.sort
                                                       in
                                                    FStar_Pervasives_Native.snd
                                                      uu____13783)
                                                 ->
                                                 x.FStar_Syntax_Syntax.sort
                                             | uu____13794 -> bound  in
                                           let uu____13795 =
                                             new_problem wl1 env bound1
                                               FStar_TypeChecker_Common.EQ
                                               this_flex
                                               FStar_Pervasives_Native.None
                                               tp.FStar_TypeChecker_Common.loc
                                               (if flip
                                                then "joining refinements"
                                                else "meeting refinements")
                                              in
                                           (bound1, uu____13795)  in
                                         (match uu____13755 with
                                          | (bound_typ,(eq_prob,wl')) ->
                                              (def_check_prob "meet_or_join2"
                                                 (FStar_TypeChecker_Common.TProb
                                                    eq_prob);
                                               (let uu____13830 =
                                                  FStar_All.pipe_left
                                                    (FStar_TypeChecker_Env.debug
                                                       env)
                                                    (FStar_Options.Other
                                                       "Rel")
                                                   in
                                                if uu____13830
                                                then
                                                  let wl'1 =
                                                    let uu___2000_13836 = wl1
                                                       in
                                                    {
                                                      attempting =
                                                        ((FStar_TypeChecker_Common.TProb
                                                            eq_prob) ::
                                                        sub_probs);
                                                      wl_deferred =
                                                        (uu___2000_13836.wl_deferred);
                                                      ctr =
                                                        (uu___2000_13836.ctr);
                                                      defer_ok =
                                                        (uu___2000_13836.defer_ok);
                                                      smt_ok =
                                                        (uu___2000_13836.smt_ok);
                                                      umax_heuristic_ok =
                                                        (uu___2000_13836.umax_heuristic_ok);
                                                      tcenv =
                                                        (uu___2000_13836.tcenv);
                                                      wl_implicits =
                                                        (uu___2000_13836.wl_implicits)
                                                    }  in
                                                  let uu____13837 =
                                                    wl_to_string wl'1  in
                                                  FStar_Util.print1
                                                    "After meet/join refinements: %s\n"
                                                    uu____13837
                                                else ());
                                               (let tx =
                                                  FStar_Syntax_Unionfind.new_transaction
                                                    ()
                                                   in
                                                let uu____13843 =
                                                  solve_t env eq_prob
                                                    (let uu___2005_13845 =
                                                       wl'  in
                                                     {
                                                       attempting = sub_probs;
                                                       wl_deferred =
                                                         (uu___2005_13845.wl_deferred);
                                                       ctr =
                                                         (uu___2005_13845.ctr);
                                                       defer_ok = false;
                                                       smt_ok =
                                                         (uu___2005_13845.smt_ok);
                                                       umax_heuristic_ok =
                                                         (uu___2005_13845.umax_heuristic_ok);
                                                       tcenv =
                                                         (uu___2005_13845.tcenv);
                                                       wl_implicits = []
                                                     })
                                                   in
                                                match uu____13843 with
                                                | Success (uu____13847,imps)
                                                    ->
                                                    let wl2 =
                                                      let uu___2011_13850 =
                                                        wl'  in
                                                      {
                                                        attempting = rest;
                                                        wl_deferred =
                                                          (uu___2011_13850.wl_deferred);
                                                        ctr =
                                                          (uu___2011_13850.ctr);
                                                        defer_ok =
                                                          (uu___2011_13850.defer_ok);
                                                        smt_ok =
                                                          (uu___2011_13850.smt_ok);
                                                        umax_heuristic_ok =
                                                          (uu___2011_13850.umax_heuristic_ok);
                                                        tcenv =
                                                          (uu___2011_13850.tcenv);
                                                        wl_implicits =
                                                          (uu___2011_13850.wl_implicits)
                                                      }  in
                                                    let wl3 =
                                                      let uu___2014_13852 =
                                                        wl2  in
                                                      {
                                                        attempting =
                                                          (uu___2014_13852.attempting);
                                                        wl_deferred =
                                                          (uu___2014_13852.wl_deferred);
                                                        ctr =
                                                          (uu___2014_13852.ctr);
                                                        defer_ok =
                                                          (uu___2014_13852.defer_ok);
                                                        smt_ok =
                                                          (uu___2014_13852.smt_ok);
                                                        umax_heuristic_ok =
                                                          (uu___2014_13852.umax_heuristic_ok);
                                                        tcenv =
                                                          (uu___2014_13852.tcenv);
                                                        wl_implicits =
                                                          (FStar_List.append
                                                             wl'.wl_implicits
                                                             imps)
                                                      }  in
                                                    let g =
                                                      FStar_List.fold_left
                                                        (fun g  ->
                                                           fun p  ->
                                                             FStar_Syntax_Util.mk_conj
                                                               g (p_guard p))
                                                        eq_prob.FStar_TypeChecker_Common.logical_guard
                                                        sub_probs
                                                       in
                                                    let wl4 =
                                                      solve_prob' false
                                                        (FStar_TypeChecker_Common.TProb
                                                           tp)
                                                        (FStar_Pervasives_Native.Some
                                                           g) [] wl3
                                                       in
                                                    let uu____13868 =
                                                      FStar_List.fold_left
                                                        (fun wl5  ->
                                                           fun p  ->
                                                             solve_prob' true
                                                               p
                                                               FStar_Pervasives_Native.None
                                                               [] wl5) wl4
                                                        bounds_probs
                                                       in
                                                    (FStar_Syntax_Unionfind.commit
                                                       tx;
                                                     solve env wl4)
                                                | Failed (p,msg) ->
                                                    ((let uu____13880 =
                                                        FStar_All.pipe_left
                                                          (FStar_TypeChecker_Env.debug
                                                             env)
                                                          (FStar_Options.Other
                                                             "Rel")
                                                         in
                                                      if uu____13880
                                                      then
                                                        let uu____13885 =
                                                          let uu____13887 =
                                                            FStar_List.map
                                                              (prob_to_string
                                                                 env)
                                                              ((FStar_TypeChecker_Common.TProb
                                                                  eq_prob) ::
                                                              sub_probs)
                                                             in
                                                          FStar_All.pipe_right
                                                            uu____13887
                                                            (FStar_String.concat
                                                               "\n")
                                                           in
                                                        FStar_Util.print1
                                                          "meet/join attempted and failed to solve problems:\n%s\n"
                                                          uu____13885
                                                      else ());
                                                     (let uu____13900 =
                                                        let uu____13915 =
                                                          base_and_refinement
                                                            env bound_typ
                                                           in
                                                        (rank1, uu____13915)
                                                         in
                                                      match uu____13900 with
                                                      | (FStar_TypeChecker_Common.Rigid_flex
                                                         ,(t_base,FStar_Pervasives_Native.Some
                                                           uu____13937))
                                                          ->
                                                          (FStar_Syntax_Unionfind.rollback
                                                             tx;
                                                           (let uu____13963 =
                                                              new_problem wl1
                                                                env t_base
                                                                FStar_TypeChecker_Common.EQ
                                                                this_flex
                                                                FStar_Pervasives_Native.None
                                                                tp.FStar_TypeChecker_Common.loc
                                                                "widened subtyping"
                                                               in
                                                            match uu____13963
                                                            with
                                                            | (eq_prob1,wl2)
                                                                ->
                                                                (def_check_prob
                                                                   "meet_or_join3"
                                                                   (FStar_TypeChecker_Common.TProb
                                                                    eq_prob1);
                                                                 (let wl3 =
                                                                    solve_prob'
                                                                    false
                                                                    (FStar_TypeChecker_Common.TProb
                                                                    tp)
                                                                    (FStar_Pervasives_Native.Some
                                                                    (p_guard
                                                                    (FStar_TypeChecker_Common.TProb
                                                                    eq_prob1)))
                                                                    [] wl2
                                                                     in
                                                                  let uu____13983
                                                                    =
                                                                    attempt
                                                                    [
                                                                    FStar_TypeChecker_Common.TProb
                                                                    eq_prob1]
                                                                    wl3  in
                                                                  solve env
                                                                    uu____13983))))
                                                      | (FStar_TypeChecker_Common.Flex_rigid
                                                         ,(t_base,FStar_Pervasives_Native.Some
                                                           (x,phi)))
                                                          ->
                                                          (FStar_Syntax_Unionfind.rollback
                                                             tx;
                                                           (let uu____14008 =
                                                              new_problem wl1
                                                                env t_base
                                                                FStar_TypeChecker_Common.EQ
                                                                this_flex
                                                                FStar_Pervasives_Native.None
                                                                tp.FStar_TypeChecker_Common.loc
                                                                "widened subtyping"
                                                               in
                                                            match uu____14008
                                                            with
                                                            | (eq_prob1,wl2)
                                                                ->
                                                                (def_check_prob
                                                                   "meet_or_join4"
                                                                   (FStar_TypeChecker_Common.TProb
                                                                    eq_prob1);
                                                                 (let phi1 =
                                                                    guard_on_element
                                                                    wl2 tp x
                                                                    phi  in
                                                                  let wl3 =
                                                                    let uu____14028
                                                                    =
                                                                    let uu____14033
                                                                    =
                                                                    FStar_Syntax_Util.mk_conj
                                                                    phi1
                                                                    (p_guard
                                                                    (FStar_TypeChecker_Common.TProb
                                                                    eq_prob1))
                                                                     in
                                                                    FStar_Pervasives_Native.Some
                                                                    uu____14033
                                                                     in
                                                                    solve_prob'
                                                                    false
                                                                    (FStar_TypeChecker_Common.TProb
                                                                    tp)
                                                                    uu____14028
                                                                    [] wl2
                                                                     in
                                                                  let uu____14039
                                                                    =
                                                                    attempt
                                                                    [
                                                                    FStar_TypeChecker_Common.TProb
                                                                    eq_prob1]
                                                                    wl3  in
                                                                  solve env
                                                                    uu____14039))))
                                                      | uu____14040 ->
                                                          let uu____14055 =
                                                            FStar_Thunk.map
                                                              (fun s  ->
                                                                 Prims.op_Hat
                                                                   "failed to solve the sub-problems: "
                                                                   s) msg
                                                             in
                                                          giveup env
                                                            uu____14055 p)))))))
                           | uu____14062 when flip ->
                               let uu____14063 =
                                 let uu____14065 =
                                   FStar_Util.string_of_int
                                     (rank_t_num rank1)
                                    in
                                 let uu____14067 =
                                   prob_to_string env
                                     (FStar_TypeChecker_Common.TProb tp)
                                    in
                                 FStar_Util.format2
                                   "Impossible: (rank=%s) Not a flex-rigid: %s"
                                   uu____14065 uu____14067
                                  in
                               failwith uu____14063
                           | uu____14070 ->
                               let uu____14071 =
                                 let uu____14073 =
                                   FStar_Util.string_of_int
                                     (rank_t_num rank1)
                                    in
                                 let uu____14075 =
                                   prob_to_string env
                                     (FStar_TypeChecker_Common.TProb tp)
                                    in
                                 FStar_Util.format2
                                   "Impossible: (rank=%s) Not a rigid-flex: %s"
                                   uu____14073 uu____14075
                                  in
                               failwith uu____14071)))))

and (imitate_arrow :
  FStar_TypeChecker_Common.prob ->
    FStar_TypeChecker_Env.env ->
      worklist ->
        flex_t ->
          FStar_Syntax_Syntax.binders ->
            FStar_Syntax_Syntax.term ->
              FStar_TypeChecker_Common.rel ->
                FStar_Syntax_Syntax.term -> solution)
  =
  fun orig  ->
    fun env  ->
      fun wl  ->
        fun lhs  ->
          fun bs_lhs  ->
            fun t_res_lhs  ->
              fun rel  ->
                fun arrow1  ->
                  let bs_lhs_args =
                    FStar_List.map
                      (fun uu____14111  ->
                         match uu____14111 with
                         | (x,i) ->
                             let uu____14130 =
                               FStar_Syntax_Syntax.bv_to_name x  in
                             (uu____14130, i)) bs_lhs
                     in
                  let uu____14133 = lhs  in
                  match uu____14133 with
                  | (uu____14134,u_lhs,uu____14136) ->
                      let imitate_comp bs bs_terms c wl1 =
                        let imitate_tot_or_gtot t uopt f wl2 =
                          let uu____14233 =
                            match uopt with
                            | FStar_Pervasives_Native.None  ->
                                FStar_Syntax_Util.type_u ()
                            | FStar_Pervasives_Native.Some univ ->
                                let uu____14243 =
                                  FStar_Syntax_Syntax.mk
                                    (FStar_Syntax_Syntax.Tm_type univ)
                                    FStar_Pervasives_Native.None
                                    t.FStar_Syntax_Syntax.pos
                                   in
                                (uu____14243, univ)
                             in
                          match uu____14233 with
                          | (k,univ) ->
                              let uu____14250 =
                                copy_uvar u_lhs (FStar_List.append bs_lhs bs)
                                  k wl2
                                 in
                              (match uu____14250 with
                               | (uu____14267,u,wl3) ->
                                   let uu____14270 =
                                     f u (FStar_Pervasives_Native.Some univ)
                                      in
                                   (uu____14270, wl3))
                           in
                        match c.FStar_Syntax_Syntax.n with
                        | FStar_Syntax_Syntax.Total (t,uopt) ->
                            imitate_tot_or_gtot t uopt
                              FStar_Syntax_Syntax.mk_Total' wl1
                        | FStar_Syntax_Syntax.GTotal (t,uopt) ->
                            imitate_tot_or_gtot t uopt
                              FStar_Syntax_Syntax.mk_GTotal' wl1
                        | FStar_Syntax_Syntax.Comp ct ->
                            let uu____14296 =
                              let uu____14309 =
                                let uu____14320 =
                                  FStar_Syntax_Syntax.as_arg
                                    ct.FStar_Syntax_Syntax.result_typ
                                   in
                                uu____14320 ::
                                  (ct.FStar_Syntax_Syntax.effect_args)
                                 in
                              FStar_List.fold_right
                                (fun uu____14371  ->
                                   fun uu____14372  ->
                                     match (uu____14371, uu____14372) with
                                     | ((a,i),(out_args,wl2)) ->
                                         let uu____14473 =
                                           let uu____14480 =
                                             let uu____14483 =
                                               FStar_Syntax_Util.type_u ()
                                                in
                                             FStar_All.pipe_left
                                               FStar_Pervasives_Native.fst
                                               uu____14483
                                              in
                                           copy_uvar u_lhs [] uu____14480 wl2
                                            in
                                         (match uu____14473 with
                                          | (uu____14512,t_a,wl3) ->
                                              let uu____14515 =
                                                copy_uvar u_lhs bs t_a wl3
                                                 in
                                              (match uu____14515 with
                                               | (uu____14534,a',wl4) ->
                                                   (((a', i) :: out_args),
                                                     wl4)))) uu____14309
                                ([], wl1)
                               in
                            (match uu____14296 with
                             | (out_args,wl2) ->
                                 let ct' =
                                   let uu___2125_14590 = ct  in
                                   let uu____14591 =
                                     let uu____14594 = FStar_List.hd out_args
                                        in
                                     FStar_Pervasives_Native.fst uu____14594
                                      in
                                   let uu____14609 = FStar_List.tl out_args
                                      in
                                   {
                                     FStar_Syntax_Syntax.comp_univs =
                                       (uu___2125_14590.FStar_Syntax_Syntax.comp_univs);
                                     FStar_Syntax_Syntax.effect_name =
                                       (uu___2125_14590.FStar_Syntax_Syntax.effect_name);
                                     FStar_Syntax_Syntax.result_typ =
                                       uu____14591;
                                     FStar_Syntax_Syntax.effect_args =
                                       uu____14609;
                                     FStar_Syntax_Syntax.flags =
                                       (uu___2125_14590.FStar_Syntax_Syntax.flags)
                                   }  in
                                 ((let uu___2128_14627 = c  in
                                   {
                                     FStar_Syntax_Syntax.n =
                                       (FStar_Syntax_Syntax.Comp ct');
                                     FStar_Syntax_Syntax.pos =
                                       (uu___2128_14627.FStar_Syntax_Syntax.pos);
                                     FStar_Syntax_Syntax.vars =
                                       (uu___2128_14627.FStar_Syntax_Syntax.vars)
                                   }), wl2))
                         in
                      let uu____14630 =
                        FStar_Syntax_Util.arrow_formals_comp arrow1  in
                      (match uu____14630 with
                       | (formals,c) ->
                           let rec aux bs bs_terms formals1 wl1 =
                             match formals1 with
                             | [] ->
                                 let uu____14692 =
                                   imitate_comp bs bs_terms c wl1  in
                                 (match uu____14692 with
                                  | (c',wl2) ->
                                      let lhs' =
                                        FStar_Syntax_Util.arrow bs c'  in
                                      let sol =
                                        let uu____14703 =
                                          let uu____14708 =
                                            FStar_Syntax_Util.abs bs_lhs lhs'
                                              (FStar_Pervasives_Native.Some
                                                 (FStar_Syntax_Util.residual_tot
                                                    t_res_lhs))
                                             in
                                          (u_lhs, uu____14708)  in
                                        TERM uu____14703  in
                                      let uu____14709 =
                                        mk_t_problem wl2 [] orig lhs' rel
                                          arrow1 FStar_Pervasives_Native.None
                                          "arrow imitation"
                                         in
                                      (match uu____14709 with
                                       | (sub_prob,wl3) ->
                                           let uu____14723 =
                                             let uu____14724 =
                                               solve_prob orig
                                                 FStar_Pervasives_Native.None
                                                 [sol] wl3
                                                in
                                             attempt [sub_prob] uu____14724
                                              in
                                           solve env uu____14723))
                             | (x,imp)::formals2 ->
                                 let uu____14746 =
                                   let uu____14753 =
                                     let uu____14756 =
                                       FStar_Syntax_Util.type_u ()  in
                                     FStar_All.pipe_right uu____14756
                                       FStar_Pervasives_Native.fst
                                      in
                                   copy_uvar u_lhs
                                     (FStar_List.append bs_lhs bs)
                                     uu____14753 wl1
                                    in
                                 (match uu____14746 with
                                  | (_ctx_u_x,u_x,wl2) ->
                                      let y =
                                        let uu____14777 =
                                          let uu____14780 =
                                            FStar_Syntax_Syntax.range_of_bv x
                                             in
                                          FStar_Pervasives_Native.Some
                                            uu____14780
                                           in
                                        FStar_Syntax_Syntax.new_bv
                                          uu____14777 u_x
                                         in
                                      let uu____14781 =
                                        let uu____14784 =
                                          let uu____14787 =
                                            let uu____14788 =
                                              FStar_Syntax_Syntax.bv_to_name
                                                y
                                               in
                                            (uu____14788, imp)  in
                                          [uu____14787]  in
                                        FStar_List.append bs_terms
                                          uu____14784
                                         in
                                      aux (FStar_List.append bs [(y, imp)])
                                        uu____14781 formals2 wl2)
                              in
                           let uu____14815 = occurs_check u_lhs arrow1  in
                           (match uu____14815 with
                            | (uu____14828,occurs_ok,msg) ->
                                if Prims.op_Negation occurs_ok
                                then
                                  let uu____14844 =
                                    FStar_Thunk.mk
                                      (fun uu____14848  ->
                                         let uu____14849 =
                                           FStar_Option.get msg  in
                                         Prims.op_Hat "occurs-check failed: "
                                           uu____14849)
                                     in
                                  giveup_or_defer env orig wl uu____14844
                                else aux [] [] formals wl))

and (solve_binders :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.binders ->
      FStar_Syntax_Syntax.binders ->
        FStar_TypeChecker_Common.prob ->
          worklist ->
            (worklist ->
               FStar_Syntax_Syntax.binders ->
                 FStar_TypeChecker_Env.env ->
                   FStar_Syntax_Syntax.subst_elt Prims.list ->
                     (FStar_TypeChecker_Common.prob * worklist))
              -> solution)
  =
  fun env  ->
    fun bs1  ->
      fun bs2  ->
        fun orig  ->
          fun wl  ->
            fun rhs  ->
              (let uu____14882 =
                 FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                   (FStar_Options.Other "Rel")
                  in
               if uu____14882
               then
                 let uu____14887 =
                   FStar_Syntax_Print.binders_to_string ", " bs1  in
                 let uu____14890 =
                   FStar_Syntax_Print.binders_to_string ", " bs2  in
                 FStar_Util.print3 "solve_binders\n\t%s\n%s\n\t%s\n"
                   uu____14887 (rel_to_string (p_rel orig)) uu____14890
               else ());
              (let rec aux wl1 scope env1 subst1 xs ys =
                 match (xs, ys) with
                 | ([],[]) ->
                     let uu____15021 = rhs wl1 scope env1 subst1  in
                     (match uu____15021 with
                      | (rhs_prob,wl2) ->
                          ((let uu____15044 =
                              FStar_All.pipe_left
                                (FStar_TypeChecker_Env.debug env1)
                                (FStar_Options.Other "Rel")
                               in
                            if uu____15044
                            then
                              let uu____15049 = prob_to_string env1 rhs_prob
                                 in
                              FStar_Util.print1 "rhs_prob = %s\n" uu____15049
                            else ());
                           (let formula = p_guard rhs_prob  in
                            (env1, (FStar_Util.Inl ([rhs_prob], formula)),
                              wl2))))
                 | ((hd1,imp)::xs1,(hd2,imp')::ys1) when
                     let uu____15127 = FStar_Syntax_Util.eq_aqual imp imp'
                        in
                     uu____15127 = FStar_Syntax_Util.Equal ->
                     let hd11 =
                       let uu___2198_15129 = hd1  in
                       let uu____15130 =
                         FStar_Syntax_Subst.subst subst1
                           hd1.FStar_Syntax_Syntax.sort
                          in
                       {
                         FStar_Syntax_Syntax.ppname =
                           (uu___2198_15129.FStar_Syntax_Syntax.ppname);
                         FStar_Syntax_Syntax.index =
                           (uu___2198_15129.FStar_Syntax_Syntax.index);
                         FStar_Syntax_Syntax.sort = uu____15130
                       }  in
                     let hd21 =
                       let uu___2201_15134 = hd2  in
                       let uu____15135 =
                         FStar_Syntax_Subst.subst subst1
                           hd2.FStar_Syntax_Syntax.sort
                          in
                       {
                         FStar_Syntax_Syntax.ppname =
                           (uu___2201_15134.FStar_Syntax_Syntax.ppname);
                         FStar_Syntax_Syntax.index =
                           (uu___2201_15134.FStar_Syntax_Syntax.index);
                         FStar_Syntax_Syntax.sort = uu____15135
                       }  in
                     let uu____15138 =
                       let uu____15143 =
                         FStar_All.pipe_left invert_rel (p_rel orig)  in
                       mk_t_problem wl1 scope orig
                         hd11.FStar_Syntax_Syntax.sort uu____15143
                         hd21.FStar_Syntax_Syntax.sort
                         FStar_Pervasives_Native.None "Formal parameter"
                        in
                     (match uu____15138 with
                      | (prob,wl2) ->
                          let hd12 = FStar_Syntax_Syntax.freshen_bv hd11  in
                          let subst2 =
                            let uu____15166 =
                              FStar_Syntax_Subst.shift_subst Prims.int_one
                                subst1
                               in
                            (FStar_Syntax_Syntax.DB (Prims.int_zero, hd12))
                              :: uu____15166
                             in
                          let env2 = FStar_TypeChecker_Env.push_bv env1 hd12
                             in
                          let uu____15173 =
                            aux wl2 (FStar_List.append scope [(hd12, imp)])
                              env2 subst2 xs1 ys1
                             in
                          (match uu____15173 with
                           | (env3,FStar_Util.Inl (sub_probs,phi),wl3) ->
                               let phi1 =
                                 let uu____15245 =
                                   FStar_TypeChecker_Env.close_forall env3
                                     [(hd12, imp)] phi
                                    in
                                 FStar_Syntax_Util.mk_conj (p_guard prob)
                                   uu____15245
                                  in
                               ((let uu____15263 =
                                   FStar_All.pipe_left
                                     (FStar_TypeChecker_Env.debug env3)
                                     (FStar_Options.Other "Rel")
                                    in
                                 if uu____15263
                                 then
                                   let uu____15268 =
                                     FStar_Syntax_Print.term_to_string phi1
                                      in
                                   let uu____15270 =
                                     FStar_Syntax_Print.bv_to_string hd12  in
                                   FStar_Util.print2
                                     "Formula is %s\n\thd1=%s\n" uu____15268
                                     uu____15270
                                 else ());
                                (env3,
                                  (FStar_Util.Inl ((prob :: sub_probs), phi1)),
                                  wl3))
                           | fail1 -> fail1))
                 | uu____15305 ->
                     (env1,
                       (FStar_Util.Inr "arity or argument-qualifier mismatch"),
                       wl1)
                  in
               let uu____15341 = aux wl [] env [] bs1 bs2  in
               match uu____15341 with
               | (env1,FStar_Util.Inr msg,wl1) -> giveup_lit env1 msg orig
               | (env1,FStar_Util.Inl (sub_probs,phi),wl1) ->
                   let wl2 =
                     solve_prob orig (FStar_Pervasives_Native.Some phi) []
                       wl1
                      in
                   let uu____15400 = attempt sub_probs wl2  in
                   solve env1 uu____15400)

and (try_solve_without_smt_or_else :
  FStar_TypeChecker_Common.prob ->
    FStar_TypeChecker_Env.env ->
      worklist ->
        (FStar_TypeChecker_Env.env -> worklist -> solution) ->
          (FStar_TypeChecker_Env.env ->
             worklist ->
               (FStar_TypeChecker_Common.prob * lstring) -> solution)
            -> solution)
  =
  fun orig  ->
    fun env  ->
      fun wl  ->
        fun try_solve  ->
          fun else_solve  ->
            let wl' =
              let uu___2240_15421 = wl  in
              {
                attempting = [];
                wl_deferred = [];
                ctr = (uu___2240_15421.ctr);
                defer_ok = false;
                smt_ok = false;
                umax_heuristic_ok = false;
                tcenv = (uu___2240_15421.tcenv);
                wl_implicits = []
              }  in
            let tx = FStar_Syntax_Unionfind.new_transaction ()  in
            let uu____15433 = try_solve env wl'  in
            match uu____15433 with
            | Success (uu____15434,imps) ->
                (FStar_Syntax_Unionfind.commit tx;
                 (let wl1 =
                    let uu___2249_15438 = wl  in
                    {
                      attempting = (uu___2249_15438.attempting);
                      wl_deferred = (uu___2249_15438.wl_deferred);
                      ctr = (uu___2249_15438.ctr);
                      defer_ok = (uu___2249_15438.defer_ok);
                      smt_ok = (uu___2249_15438.smt_ok);
                      umax_heuristic_ok = (uu___2249_15438.umax_heuristic_ok);
                      tcenv = (uu___2249_15438.tcenv);
                      wl_implicits = (FStar_List.append wl.wl_implicits imps)
                    }  in
                  solve env wl1))
            | Failed (p,s) ->
                ((let uu____15442 =
                    FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                      (FStar_Options.Other "Rel")
                     in
                  if uu____15442
                  then
                    let uu____15447 = prob_to_string env orig  in
                    let uu____15449 = prob_to_string env p  in
                    let uu____15451 = FStar_Thunk.force s  in
                    FStar_Util.print3
                      "Failed to solve %s because sub-problem %s is not solvable without SMT because %s"
                      uu____15447 uu____15449 uu____15451
                  else ());
                 FStar_Syntax_Unionfind.rollback tx;
                 else_solve env wl (p, s))

and (solve_t : FStar_TypeChecker_Env.env -> tprob -> worklist -> solution) =
  fun env  ->
    fun problem  ->
      fun wl  ->
        def_check_prob "solve_t" (FStar_TypeChecker_Common.TProb problem);
        (let uu____15463 = compress_tprob wl.tcenv problem  in
         solve_t' env uu____15463 wl)

and (solve_t_flex_rigid_eq :
  FStar_TypeChecker_Env.env ->
    FStar_TypeChecker_Common.prob ->
      worklist -> flex_t -> FStar_Syntax_Syntax.term -> solution)
  =
  fun env  ->
    fun orig  ->
      fun wl  ->
        fun lhs  ->
          fun rhs  ->
            let binders_as_bv_set bs =
              let uu____15477 = FStar_List.map FStar_Pervasives_Native.fst bs
                 in
              FStar_Util.as_set uu____15477 FStar_Syntax_Syntax.order_bv  in
            let mk_solution env1 lhs1 bs rhs1 =
              let uu____15511 = lhs1  in
              match uu____15511 with
              | (uu____15514,ctx_u,uu____15516) ->
                  let sol =
                    match bs with
                    | [] -> rhs1
                    | uu____15524 ->
                        let uu____15525 = sn_binders env1 bs  in
                        u_abs ctx_u.FStar_Syntax_Syntax.ctx_uvar_typ
                          uu____15525 rhs1
                     in
                  [TERM (ctx_u, sol)]
               in
            let try_quasi_pattern orig1 env1 wl1 lhs1 rhs1 =
              let uu____15574 = quasi_pattern env1 lhs1  in
              match uu____15574 with
              | FStar_Pervasives_Native.None  ->
                  ((FStar_Util.Inl "Not a quasi-pattern"), wl1)
              | FStar_Pervasives_Native.Some (bs,uu____15608) ->
                  let uu____15613 = lhs1  in
                  (match uu____15613 with
                   | (t_lhs,ctx_u,args) ->
                       let uu____15628 = occurs_check ctx_u rhs1  in
                       (match uu____15628 with
                        | (uvars1,occurs_ok,msg) ->
                            if Prims.op_Negation occurs_ok
                            then
                              let uu____15679 =
                                let uu____15687 =
                                  let uu____15689 = FStar_Option.get msg  in
                                  Prims.op_Hat
                                    "quasi-pattern, occurs-check failed: "
                                    uu____15689
                                   in
                                FStar_Util.Inl uu____15687  in
                              (uu____15679, wl1)
                            else
                              (let fvs_lhs =
                                 binders_as_bv_set
                                   (FStar_List.append
                                      ctx_u.FStar_Syntax_Syntax.ctx_uvar_binders
                                      bs)
                                  in
                               let fvs_rhs = FStar_Syntax_Free.names rhs1  in
                               let uu____15717 =
                                 let uu____15719 =
                                   FStar_Util.set_is_subset_of fvs_rhs
                                     fvs_lhs
                                    in
                                 Prims.op_Negation uu____15719  in
                               if uu____15717
                               then
                                 ((FStar_Util.Inl
                                     "quasi-pattern, free names on the RHS are not included in the LHS"),
                                   wl1)
                               else
                                 (let uu____15746 =
                                    let uu____15754 =
                                      mk_solution env1 lhs1 bs rhs1  in
                                    FStar_Util.Inr uu____15754  in
                                  let uu____15760 =
                                    restrict_all_uvars ctx_u uvars1 wl1  in
                                  (uu____15746, uu____15760)))))
               in
            let imitate_app orig1 env1 wl1 lhs1 bs_lhs t_res_lhs rhs1 =
              (let uu____15805 =
                 FStar_All.pipe_left (FStar_TypeChecker_Env.debug env1)
                   (FStar_Options.Other "Rel")
                  in
               if uu____15805
               then
                 let uu____15810 = flex_t_to_string lhs1  in
                 let uu____15812 =
                   FStar_Syntax_Print.binders_to_string ", " bs_lhs  in
                 let uu____15815 =
                   FStar_Syntax_Print.term_to_string t_res_lhs  in
                 let uu____15817 = FStar_Syntax_Print.term_to_string rhs1  in
                 FStar_Util.print4
                   "imitate_app 1:\n\tlhs=%s\n\tbs_lhs=%s\n\tt_res_lhs=%s\n\trhs=%s\n"
                   uu____15810 uu____15812 uu____15815 uu____15817
               else ());
              (let uu____15822 = FStar_Syntax_Util.head_and_args rhs1  in
               match uu____15822 with
               | (rhs_hd,args) ->
                   let uu____15865 = FStar_Util.prefix args  in
                   (match uu____15865 with
                    | (args_rhs,last_arg_rhs) ->
                        let rhs' =
                          FStar_Syntax_Syntax.mk_Tm_app rhs_hd args_rhs
                            FStar_Pervasives_Native.None
                            rhs1.FStar_Syntax_Syntax.pos
                           in
                        ((let uu____15938 =
                            FStar_All.pipe_left
                              (FStar_TypeChecker_Env.debug env1)
                              (FStar_Options.Other "Rel")
                             in
                          if uu____15938
                          then
                            let uu____15943 =
                              FStar_Syntax_Print.term_to_string rhs'  in
                            let uu____15945 =
                              FStar_Syntax_Print.args_to_string
                                [last_arg_rhs]
                               in
                            FStar_Util.print2
                              "imitate_app 2:\n\trhs'=%s\n\tlast_arg_rhs=%s\n"
                              uu____15943 uu____15945
                          else ());
                         (let uu____15966 = lhs1  in
                          match uu____15966 with
                          | (t_lhs,u_lhs,_lhs_args) ->
                              let uu____15970 =
                                let uu____15981 =
                                  let uu____15988 =
                                    let uu____15991 =
                                      FStar_Syntax_Util.type_u ()  in
                                    FStar_All.pipe_left
                                      FStar_Pervasives_Native.fst uu____15991
                                     in
                                  copy_uvar u_lhs [] uu____15988 wl1  in
                                match uu____15981 with
                                | (uu____16018,t_last_arg,wl2) ->
                                    let uu____16021 =
                                      let uu____16028 =
                                        let uu____16029 =
                                          let uu____16038 =
                                            FStar_Syntax_Syntax.null_binder
                                              t_last_arg
                                             in
                                          [uu____16038]  in
                                        FStar_List.append bs_lhs uu____16029
                                         in
                                      copy_uvar u_lhs uu____16028 t_res_lhs
                                        wl2
                                       in
                                    (match uu____16021 with
                                     | (uu____16073,lhs',wl3) ->
                                         let uu____16076 =
                                           copy_uvar u_lhs bs_lhs t_last_arg
                                             wl3
                                            in
                                         (match uu____16076 with
                                          | (uu____16093,lhs'_last_arg,wl4)
                                              -> (lhs', lhs'_last_arg, wl4)))
                                 in
                              (match uu____15970 with
                               | (lhs',lhs'_last_arg,wl2) ->
                                   ((let uu____16112 =
                                       FStar_All.pipe_left
                                         (FStar_TypeChecker_Env.debug env1)
                                         (FStar_Options.Other "Rel")
                                        in
                                     if uu____16112
                                     then
                                       let uu____16117 =
                                         FStar_Syntax_Print.term_to_string
                                           lhs'
                                          in
                                       let uu____16119 =
                                         FStar_Syntax_Print.term_to_string
                                           lhs'_last_arg
                                          in
                                       FStar_Util.print2
                                         "imitate_app 3:\n\tlhs'=%s\n\tlast_arg_lhs=%s\n"
                                         uu____16117 uu____16119
                                     else ());
                                    (let sol =
                                       let uu____16127 =
                                         let uu____16128 =
                                           let uu____16133 =
                                             let uu____16134 =
                                               let uu____16137 =
                                                 let uu____16142 =
                                                   let uu____16143 =
                                                     FStar_Syntax_Syntax.as_arg
                                                       lhs'_last_arg
                                                      in
                                                   [uu____16143]  in
                                                 FStar_Syntax_Syntax.mk_Tm_app
                                                   lhs' uu____16142
                                                  in
                                               uu____16137
                                                 FStar_Pervasives_Native.None
                                                 t_lhs.FStar_Syntax_Syntax.pos
                                                in
                                             FStar_Syntax_Util.abs bs_lhs
                                               uu____16134
                                               (FStar_Pervasives_Native.Some
                                                  (FStar_Syntax_Util.residual_tot
                                                     t_res_lhs))
                                              in
                                           (u_lhs, uu____16133)  in
                                         TERM uu____16128  in
                                       [uu____16127]  in
                                     let uu____16168 =
                                       let uu____16175 =
                                         mk_t_problem wl2 [] orig1 lhs'
                                           FStar_TypeChecker_Common.EQ rhs'
                                           FStar_Pervasives_Native.None
                                           "first-order lhs"
                                          in
                                       match uu____16175 with
                                       | (p1,wl3) ->
                                           let uu____16195 =
                                             mk_t_problem wl3 [] orig1
                                               lhs'_last_arg
                                               FStar_TypeChecker_Common.EQ
                                               (FStar_Pervasives_Native.fst
                                                  last_arg_rhs)
                                               FStar_Pervasives_Native.None
                                               "first-order rhs"
                                              in
                                           (match uu____16195 with
                                            | (p2,wl4) -> ([p1; p2], wl4))
                                        in
                                     match uu____16168 with
                                     | (sub_probs,wl3) ->
                                         let uu____16227 =
                                           let uu____16228 =
                                             solve_prob orig1
                                               FStar_Pervasives_Native.None
                                               sol wl3
                                              in
                                           attempt sub_probs uu____16228  in
                                         solve env1 uu____16227)))))))
               in
            let first_order orig1 env1 wl1 lhs1 rhs1 =
              let is_app rhs2 =
                let uu____16262 = FStar_Syntax_Util.head_and_args rhs2  in
                match uu____16262 with
                | (uu____16280,args) ->
                    (match args with | [] -> false | uu____16316 -> true)
                 in
              let is_arrow rhs2 =
                let uu____16335 =
                  let uu____16336 = FStar_Syntax_Subst.compress rhs2  in
                  uu____16336.FStar_Syntax_Syntax.n  in
                match uu____16335 with
                | FStar_Syntax_Syntax.Tm_arrow uu____16340 -> true
                | uu____16356 -> false  in
              let uu____16358 = quasi_pattern env1 lhs1  in
              match uu____16358 with
              | FStar_Pervasives_Native.None  ->
                  let msg =
                    FStar_Thunk.mk
                      (fun uu____16376  ->
                         let uu____16377 = prob_to_string env1 orig1  in
                         FStar_Util.format1
                           "first_order heuristic cannot solve %s; lhs not a quasi-pattern"
                           uu____16377)
                     in
                  giveup_or_defer env1 orig1 wl1 msg
              | FStar_Pervasives_Native.Some (bs_lhs,t_res_lhs) ->
                  let uu____16386 = is_app rhs1  in
                  if uu____16386
                  then imitate_app orig1 env1 wl1 lhs1 bs_lhs t_res_lhs rhs1
                  else
                    (let uu____16391 = is_arrow rhs1  in
                     if uu____16391
                     then
                       imitate_arrow orig1 env1 wl1 lhs1 bs_lhs t_res_lhs
                         FStar_TypeChecker_Common.EQ rhs1
                     else
                       (let msg =
                          FStar_Thunk.mk
                            (fun uu____16403  ->
                               let uu____16404 = prob_to_string env1 orig1
                                  in
                               FStar_Util.format1
                                 "first_order heuristic cannot solve %s; rhs not an app or arrow"
                                 uu____16404)
                           in
                        giveup_or_defer env1 orig1 wl1 msg))
               in
            match p_rel orig with
            | FStar_TypeChecker_Common.SUB  ->
                if wl.defer_ok
                then
                  let uu____16408 = FStar_Thunk.mkv "flex-rigid subtyping"
                     in
                  giveup_or_defer env orig wl uu____16408
                else solve_t_flex_rigid_eq env (make_prob_eq orig) wl lhs rhs
            | FStar_TypeChecker_Common.SUBINV  ->
                if wl.defer_ok
                then
                  let uu____16414 = FStar_Thunk.mkv "flex-rigid subtyping"
                     in
                  giveup_or_defer env orig wl uu____16414
                else solve_t_flex_rigid_eq env (make_prob_eq orig) wl lhs rhs
            | FStar_TypeChecker_Common.EQ  ->
                let uu____16419 = lhs  in
                (match uu____16419 with
                 | (_t1,ctx_uv,args_lhs) ->
                     let uu____16423 =
                       pat_vars env
                         ctx_uv.FStar_Syntax_Syntax.ctx_uvar_binders args_lhs
                        in
                     (match uu____16423 with
                      | FStar_Pervasives_Native.Some lhs_binders ->
                          let rhs1 = sn env rhs  in
                          let names_to_string1 fvs =
                            let uu____16441 =
                              let uu____16445 = FStar_Util.set_elements fvs
                                 in
                              FStar_List.map FStar_Syntax_Print.bv_to_string
                                uu____16445
                               in
                            FStar_All.pipe_right uu____16441
                              (FStar_String.concat ", ")
                             in
                          let fvs1 =
                            binders_as_bv_set
                              (FStar_List.append
                                 ctx_uv.FStar_Syntax_Syntax.ctx_uvar_binders
                                 lhs_binders)
                             in
                          let fvs2 = FStar_Syntax_Free.names rhs1  in
                          let uu____16466 = occurs_check ctx_uv rhs1  in
                          (match uu____16466 with
                           | (uvars1,occurs_ok,msg) ->
                               if Prims.op_Negation occurs_ok
                               then
                                 let uu____16495 =
                                   let uu____16496 =
                                     let uu____16498 = FStar_Option.get msg
                                        in
                                     Prims.op_Hat "occurs-check failed: "
                                       uu____16498
                                      in
                                   FStar_All.pipe_left FStar_Thunk.mkv
                                     uu____16496
                                    in
                                 giveup_or_defer env orig wl uu____16495
                               else
                                 (let uu____16506 =
                                    FStar_Util.set_is_subset_of fvs2 fvs1  in
                                  if uu____16506
                                  then
                                    let sol =
                                      mk_solution env lhs lhs_binders rhs1
                                       in
                                    let wl1 =
                                      restrict_all_uvars ctx_uv uvars1 wl  in
                                    let uu____16513 =
                                      solve_prob orig
                                        FStar_Pervasives_Native.None sol wl1
                                       in
                                    solve env uu____16513
                                  else
                                    if wl.defer_ok
                                    then
                                      (let msg1 =
                                         FStar_Thunk.mk
                                           (fun uu____16526  ->
                                              let uu____16527 =
                                                names_to_string1 fvs2  in
                                              let uu____16529 =
                                                names_to_string1 fvs1  in
                                              let uu____16531 =
                                                FStar_Syntax_Print.binders_to_string
                                                  ", "
                                                  (FStar_List.append
                                                     ctx_uv.FStar_Syntax_Syntax.ctx_uvar_binders
                                                     lhs_binders)
                                                 in
                                              FStar_Util.format3
                                                "free names in the RHS {%s} are out of scope for the LHS: {%s}, {%s}"
                                                uu____16527 uu____16529
                                                uu____16531)
                                          in
                                       giveup_or_defer env orig wl msg1)
                                    else first_order orig env wl lhs rhs1))
                      | uu____16543 ->
                          if wl.defer_ok
                          then
                            let uu____16547 = FStar_Thunk.mkv "Not a pattern"
                               in
                            giveup_or_defer env orig wl uu____16547
                          else
                            (let uu____16552 =
                               try_quasi_pattern orig env wl lhs rhs  in
                             match uu____16552 with
                             | (FStar_Util.Inr sol,wl1) ->
                                 let uu____16578 =
                                   solve_prob orig
                                     FStar_Pervasives_Native.None sol wl1
                                    in
                                 solve env uu____16578
                             | (FStar_Util.Inl msg,uu____16580) ->
                                 first_order orig env wl lhs rhs)))

and (solve_t_flex_flex :
  FStar_TypeChecker_Env.env ->
    FStar_TypeChecker_Common.prob -> worklist -> flex_t -> flex_t -> solution)
  =
  fun env  ->
    fun orig  ->
      fun wl  ->
        fun lhs  ->
          fun rhs  ->
            match p_rel orig with
            | FStar_TypeChecker_Common.SUB  ->
                if wl.defer_ok
                then
                  let uu____16598 = FStar_Thunk.mkv "flex-flex subtyping"  in
                  giveup_or_defer env orig wl uu____16598
                else solve_t_flex_flex env (make_prob_eq orig) wl lhs rhs
            | FStar_TypeChecker_Common.SUBINV  ->
                if wl.defer_ok
                then
                  let uu____16604 = FStar_Thunk.mkv "flex-flex subtyping"  in
                  giveup_or_defer env orig wl uu____16604
                else solve_t_flex_flex env (make_prob_eq orig) wl lhs rhs
            | FStar_TypeChecker_Common.EQ  ->
                if
                  wl.defer_ok &&
                    ((Prims.op_Negation (is_flex_pat lhs)) ||
                       (Prims.op_Negation (is_flex_pat rhs)))
                then
                  let uu____16626 = FStar_Thunk.mkv "flex-flex non-pattern"
                     in
                  giveup_or_defer env orig wl uu____16626
                else
                  (let uu____16631 =
                     let uu____16648 = quasi_pattern env lhs  in
                     let uu____16655 = quasi_pattern env rhs  in
                     (uu____16648, uu____16655)  in
                   match uu____16631 with
                   | (FStar_Pervasives_Native.Some
                      (binders_lhs,t_res_lhs),FStar_Pervasives_Native.Some
                      (binders_rhs,t_res_rhs)) ->
                       let uu____16698 = lhs  in
                       (match uu____16698 with
                        | ({ FStar_Syntax_Syntax.n = uu____16699;
                             FStar_Syntax_Syntax.pos = range;
                             FStar_Syntax_Syntax.vars = uu____16701;_},u_lhs,uu____16703)
                            ->
                            let uu____16706 = rhs  in
                            (match uu____16706 with
                             | (uu____16707,u_rhs,uu____16709) ->
                                 let uu____16710 =
                                   (FStar_Syntax_Unionfind.equiv
                                      u_lhs.FStar_Syntax_Syntax.ctx_uvar_head
                                      u_rhs.FStar_Syntax_Syntax.ctx_uvar_head)
                                     && (binders_eq binders_lhs binders_rhs)
                                    in
                                 if uu____16710
                                 then
                                   let uu____16717 =
                                     solve_prob orig
                                       FStar_Pervasives_Native.None [] wl
                                      in
                                   solve env uu____16717
                                 else
                                   (let uu____16720 =
                                      maximal_prefix
                                        u_lhs.FStar_Syntax_Syntax.ctx_uvar_binders
                                        u_rhs.FStar_Syntax_Syntax.ctx_uvar_binders
                                       in
                                    match uu____16720 with
                                    | (ctx_w,(ctx_l,ctx_r)) ->
                                        let gamma_w =
                                          gamma_until
                                            u_lhs.FStar_Syntax_Syntax.ctx_uvar_gamma
                                            ctx_w
                                           in
                                        let zs =
                                          intersect_binders gamma_w
                                            (FStar_List.append ctx_l
                                               binders_lhs)
                                            (FStar_List.append ctx_r
                                               binders_rhs)
                                           in
                                        let uu____16752 =
                                          let uu____16759 =
                                            let uu____16762 =
                                              FStar_Syntax_Syntax.mk_Total
                                                t_res_lhs
                                               in
                                            FStar_Syntax_Util.arrow zs
                                              uu____16762
                                             in
                                          new_uvar
                                            (Prims.op_Hat "flex-flex quasi:"
                                               (Prims.op_Hat "\tlhs="
                                                  (Prims.op_Hat
                                                     u_lhs.FStar_Syntax_Syntax.ctx_uvar_reason
                                                     (Prims.op_Hat "\trhs="
                                                        u_rhs.FStar_Syntax_Syntax.ctx_uvar_reason))))
                                            wl range gamma_w ctx_w
                                            uu____16759
                                            FStar_Syntax_Syntax.Strict
                                            FStar_Pervasives_Native.None
                                           in
                                        (match uu____16752 with
                                         | (uu____16774,w,wl1) ->
                                             let w_app =
                                               let uu____16780 =
                                                 let uu____16785 =
                                                   FStar_List.map
                                                     (fun uu____16796  ->
                                                        match uu____16796
                                                        with
                                                        | (z,uu____16804) ->
                                                            let uu____16809 =
                                                              FStar_Syntax_Syntax.bv_to_name
                                                                z
                                                               in
                                                            FStar_Syntax_Syntax.as_arg
                                                              uu____16809) zs
                                                    in
                                                 FStar_Syntax_Syntax.mk_Tm_app
                                                   w uu____16785
                                                  in
                                               uu____16780
                                                 FStar_Pervasives_Native.None
                                                 w.FStar_Syntax_Syntax.pos
                                                in
                                             ((let uu____16811 =
                                                 FStar_All.pipe_left
                                                   (FStar_TypeChecker_Env.debug
                                                      env)
                                                   (FStar_Options.Other "Rel")
                                                  in
                                               if uu____16811
                                               then
                                                 let uu____16816 =
                                                   let uu____16820 =
                                                     flex_t_to_string lhs  in
                                                   let uu____16822 =
                                                     let uu____16826 =
                                                       flex_t_to_string rhs
                                                        in
                                                     let uu____16828 =
                                                       let uu____16832 =
                                                         term_to_string w  in
                                                       let uu____16834 =
                                                         let uu____16838 =
                                                           FStar_Syntax_Print.binders_to_string
                                                             ", "
                                                             (FStar_List.append
                                                                ctx_l
                                                                binders_lhs)
                                                            in
                                                         let uu____16847 =
                                                           let uu____16851 =
                                                             FStar_Syntax_Print.binders_to_string
                                                               ", "
                                                               (FStar_List.append
                                                                  ctx_r
                                                                  binders_rhs)
                                                              in
                                                           let uu____16860 =
                                                             let uu____16864
                                                               =
                                                               FStar_Syntax_Print.binders_to_string
                                                                 ", " zs
                                                                in
                                                             [uu____16864]
                                                              in
                                                           uu____16851 ::
                                                             uu____16860
                                                            in
                                                         uu____16838 ::
                                                           uu____16847
                                                          in
                                                       uu____16832 ::
                                                         uu____16834
                                                        in
                                                     uu____16826 ::
                                                       uu____16828
                                                      in
                                                   uu____16820 :: uu____16822
                                                    in
                                                 FStar_Util.print
                                                   "flex-flex quasi:\n\tlhs=%s\n\trhs=%s\n\tsol=%s\n\tctx_l@binders_lhs=%s\n\tctx_r@binders_rhs=%s\n\tzs=%s\n"
                                                   uu____16816
                                               else ());
                                              (let sol =
                                                 let s1 =
                                                   let uu____16881 =
                                                     let uu____16886 =
                                                       FStar_Syntax_Util.abs
                                                         binders_lhs w_app
                                                         (FStar_Pervasives_Native.Some
                                                            (FStar_Syntax_Util.residual_tot
                                                               t_res_lhs))
                                                        in
                                                     (u_lhs, uu____16886)  in
                                                   TERM uu____16881  in
                                                 let uu____16887 =
                                                   FStar_Syntax_Unionfind.equiv
                                                     u_lhs.FStar_Syntax_Syntax.ctx_uvar_head
                                                     u_rhs.FStar_Syntax_Syntax.ctx_uvar_head
                                                    in
                                                 if uu____16887
                                                 then [s1]
                                                 else
                                                   (let s2 =
                                                      let uu____16895 =
                                                        let uu____16900 =
                                                          FStar_Syntax_Util.abs
                                                            binders_rhs w_app
                                                            (FStar_Pervasives_Native.Some
                                                               (FStar_Syntax_Util.residual_tot
                                                                  t_res_lhs))
                                                           in
                                                        (u_rhs, uu____16900)
                                                         in
                                                      TERM uu____16895  in
                                                    [s1; s2])
                                                  in
                                               let uu____16901 =
                                                 solve_prob orig
                                                   FStar_Pervasives_Native.None
                                                   sol wl1
                                                  in
                                               solve env uu____16901))))))
                   | uu____16902 ->
                       let uu____16919 =
                         FStar_Thunk.mkv "flex-flex: non-patterns"  in
                       giveup_or_defer env orig wl uu____16919)

and (solve_t' : FStar_TypeChecker_Env.env -> tprob -> worklist -> solution) =
  fun env  ->
    fun problem  ->
      fun wl  ->
        def_check_prob "solve_t'.1" (FStar_TypeChecker_Common.TProb problem);
        (let giveup_or_defer1 orig msg = giveup_or_defer env orig wl msg  in
         let rigid_heads_match env1 need_unif torig wl1 t1 t2 =
           let orig = FStar_TypeChecker_Common.TProb torig  in
           (let uu____16973 =
              FStar_All.pipe_left (FStar_TypeChecker_Env.debug env1)
                (FStar_Options.Other "Rel")
               in
            if uu____16973
            then
              let uu____16978 = FStar_Syntax_Print.term_to_string t1  in
              let uu____16980 = FStar_Syntax_Print.tag_of_term t1  in
              let uu____16982 = FStar_Syntax_Print.term_to_string t2  in
              let uu____16984 = FStar_Syntax_Print.tag_of_term t2  in
              FStar_Util.print5 "Heads %s: %s (%s) and %s (%s)\n"
                (if need_unif then "need unification" else "match")
                uu____16978 uu____16980 uu____16982 uu____16984
            else ());
           (let uu____16995 = FStar_Syntax_Util.head_and_args t1  in
            match uu____16995 with
            | (head1,args1) ->
                let uu____17038 = FStar_Syntax_Util.head_and_args t2  in
                (match uu____17038 with
                 | (head2,args2) ->
                     let solve_head_then wl2 k =
                       if need_unif
                       then k true wl2
                       else
                         (let uu____17108 =
                            solve_maybe_uinsts env1 orig head1 head2 wl2  in
                          match uu____17108 with
                          | USolved wl3 -> k true wl3
                          | UFailed msg -> giveup env1 msg orig
                          | UDeferred wl3 ->
                              let uu____17113 =
                                defer_lit "universe constraints" orig wl3  in
                              k false uu____17113)
                        in
                     let nargs = FStar_List.length args1  in
                     if nargs <> (FStar_List.length args2)
                     then
                       let uu____17134 =
                         FStar_Thunk.mk
                           (fun uu____17141  ->
                              let uu____17142 =
                                FStar_Syntax_Print.term_to_string head1  in
                              let uu____17144 = args_to_string args1  in
                              let uu____17148 =
                                FStar_Syntax_Print.term_to_string head2  in
                              let uu____17150 = args_to_string args2  in
                              FStar_Util.format4
                                "unequal number of arguments: %s[%s] and %s[%s]"
                                uu____17142 uu____17144 uu____17148
                                uu____17150)
                          in
                       giveup env1 uu____17134 orig
                     else
                       (let uu____17157 =
                          (nargs = Prims.int_zero) ||
                            (let uu____17162 =
                               FStar_Syntax_Util.eq_args args1 args2  in
                             uu____17162 = FStar_Syntax_Util.Equal)
                           in
                        if uu____17157
                        then
                          (if need_unif
                           then
                             solve_t env1
                               (let uu___2513_17166 = problem  in
                                {
                                  FStar_TypeChecker_Common.pid =
                                    (uu___2513_17166.FStar_TypeChecker_Common.pid);
                                  FStar_TypeChecker_Common.lhs = head1;
                                  FStar_TypeChecker_Common.relation =
                                    (uu___2513_17166.FStar_TypeChecker_Common.relation);
                                  FStar_TypeChecker_Common.rhs = head2;
                                  FStar_TypeChecker_Common.element =
                                    (uu___2513_17166.FStar_TypeChecker_Common.element);
                                  FStar_TypeChecker_Common.logical_guard =
                                    (uu___2513_17166.FStar_TypeChecker_Common.logical_guard);
                                  FStar_TypeChecker_Common.logical_guard_uvar
                                    =
                                    (uu___2513_17166.FStar_TypeChecker_Common.logical_guard_uvar);
                                  FStar_TypeChecker_Common.reason =
                                    (uu___2513_17166.FStar_TypeChecker_Common.reason);
                                  FStar_TypeChecker_Common.loc =
                                    (uu___2513_17166.FStar_TypeChecker_Common.loc);
                                  FStar_TypeChecker_Common.rank =
                                    (uu___2513_17166.FStar_TypeChecker_Common.rank)
                                }) wl1
                           else
                             solve_head_then wl1
                               (fun ok  ->
                                  fun wl2  ->
                                    if ok
                                    then
                                      let uu____17176 =
                                        solve_prob orig
                                          FStar_Pervasives_Native.None [] wl2
                                         in
                                      solve env1 uu____17176
                                    else solve env1 wl2))
                        else
                          (let uu____17181 = base_and_refinement env1 t1  in
                           match uu____17181 with
                           | (base1,refinement1) ->
                               let uu____17206 = base_and_refinement env1 t2
                                  in
                               (match uu____17206 with
                                | (base2,refinement2) ->
                                    (match (refinement1, refinement2) with
                                     | (FStar_Pervasives_Native.None
                                        ,FStar_Pervasives_Native.None ) ->
                                         let mk_sub_probs wl2 =
                                           let argp =
                                             if need_unif
                                             then
                                               FStar_List.zip
                                                 ((head1,
                                                    FStar_Pervasives_Native.None)
                                                 :: args1)
                                                 ((head2,
                                                    FStar_Pervasives_Native.None)
                                                 :: args2)
                                             else FStar_List.zip args1 args2
                                              in
                                           let uu____17371 =
                                             FStar_List.fold_right
                                               (fun uu____17411  ->
                                                  fun uu____17412  ->
                                                    match (uu____17411,
                                                            uu____17412)
                                                    with
                                                    | (((a1,uu____17464),
                                                        (a2,uu____17466)),
                                                       (probs,wl3)) ->
                                                        let uu____17515 =
                                                          mk_problem wl3 []
                                                            orig a1
                                                            FStar_TypeChecker_Common.EQ
                                                            a2
                                                            FStar_Pervasives_Native.None
                                                            "index"
                                                           in
                                                        (match uu____17515
                                                         with
                                                         | (prob',wl4) ->
                                                             (((FStar_TypeChecker_Common.TProb
                                                                  prob') ::
                                                               probs), wl4)))
                                               argp ([], wl2)
                                              in
                                           match uu____17371 with
                                           | (subprobs,wl3) ->
                                               ((let uu____17558 =
                                                   FStar_All.pipe_left
                                                     (FStar_TypeChecker_Env.debug
                                                        env1)
                                                     (FStar_Options.Other
                                                        "Rel")
                                                    in
                                                 if uu____17558
                                                 then
                                                   let uu____17563 =
                                                     FStar_Syntax_Print.list_to_string
                                                       (prob_to_string env1)
                                                       subprobs
                                                      in
                                                   FStar_Util.print1
                                                     "Adding subproblems for arguments: %s"
                                                     uu____17563
                                                 else ());
                                                (let uu____17569 =
                                                   FStar_Options.defensive ()
                                                    in
                                                 if uu____17569
                                                 then
                                                   FStar_List.iter
                                                     (def_check_prob
                                                        "solve_t' subprobs")
                                                     subprobs
                                                 else ());
                                                (subprobs, wl3))
                                            in
                                         let solve_sub_probs env2 wl2 =
                                           solve_head_then wl2
                                             (fun ok  ->
                                                fun wl3  ->
                                                  if Prims.op_Negation ok
                                                  then solve env2 wl3
                                                  else
                                                    (let uu____17596 =
                                                       mk_sub_probs wl3  in
                                                     match uu____17596 with
                                                     | (subprobs,wl4) ->
                                                         let formula =
                                                           let uu____17612 =
                                                             FStar_List.map
                                                               (fun p  ->
                                                                  p_guard p)
                                                               subprobs
                                                              in
                                                           FStar_Syntax_Util.mk_conj_l
                                                             uu____17612
                                                            in
                                                         let wl5 =
                                                           solve_prob orig
                                                             (FStar_Pervasives_Native.Some
                                                                formula) []
                                                             wl4
                                                            in
                                                         let uu____17620 =
                                                           attempt subprobs
                                                             wl5
                                                            in
                                                         solve env2
                                                           uu____17620))
                                            in
                                         let solve_sub_probs_no_smt env2 wl2
                                           =
                                           solve_head_then wl2
                                             (fun ok  ->
                                                fun wl3  ->
                                                  if Prims.op_Negation ok
                                                  then
                                                    failwith
                                                      "impossible (solve_sub_probs_no_smt)"
                                                  else ();
                                                  (let uu____17648 =
                                                     mk_sub_probs wl3  in
                                                   match uu____17648 with
                                                   | (subprobs,wl4) ->
                                                       let wl5 =
                                                         solve_prob orig
                                                           FStar_Pervasives_Native.None
                                                           [] wl4
                                                          in
                                                       let uu____17662 =
                                                         attempt subprobs wl5
                                                          in
                                                       solve env2 uu____17662))
                                            in
                                         let unfold_and_retry d env2 wl2
                                           uu____17687 =
                                           match uu____17687 with
                                           | (prob,reason) ->
                                               let uu____17694 =
                                                 let uu____17703 =
                                                   FStar_TypeChecker_Normalize.unfold_head_once
                                                     env2 t1
                                                    in
                                                 let uu____17706 =
                                                   FStar_TypeChecker_Normalize.unfold_head_once
                                                     env2 t2
                                                    in
                                                 (uu____17703, uu____17706)
                                                  in
                                               (match uu____17694 with
                                                | (FStar_Pervasives_Native.Some
                                                   t1',FStar_Pervasives_Native.Some
                                                   t2') ->
                                                    let uu____17719 =
                                                      FStar_Syntax_Util.head_and_args
                                                        t1'
                                                       in
                                                    (match uu____17719 with
                                                     | (head1',uu____17737)
                                                         ->
                                                         let uu____17762 =
                                                           FStar_Syntax_Util.head_and_args
                                                             t2'
                                                            in
                                                         (match uu____17762
                                                          with
                                                          | (head2',uu____17780)
                                                              ->
                                                              let uu____17805
                                                                =
                                                                let uu____17810
                                                                  =
                                                                  FStar_Syntax_Util.eq_tm
                                                                    head1'
                                                                    head1
                                                                   in
                                                                let uu____17811
                                                                  =
                                                                  FStar_Syntax_Util.eq_tm
                                                                    head2'
                                                                    head2
                                                                   in
                                                                (uu____17810,
                                                                  uu____17811)
                                                                 in
                                                              (match uu____17805
                                                               with
                                                               | (FStar_Syntax_Util.Equal
                                                                  ,FStar_Syntax_Util.Equal
                                                                  ) ->
                                                                   ((
                                                                    let uu____17813
                                                                    =
                                                                    FStar_All.pipe_left
                                                                    (FStar_TypeChecker_Env.debug
                                                                    env2)
                                                                    (FStar_Options.Other
                                                                    "Rel")
                                                                     in
                                                                    if
                                                                    uu____17813
                                                                    then
                                                                    let uu____17818
                                                                    =
                                                                    FStar_Syntax_Print.term_to_string
                                                                    t1  in
                                                                    let uu____17820
                                                                    =
                                                                    FStar_Syntax_Print.term_to_string
                                                                    t1'  in
                                                                    let uu____17822
                                                                    =
                                                                    FStar_Syntax_Print.term_to_string
                                                                    t2  in
                                                                    let uu____17824
                                                                    =
                                                                    FStar_Syntax_Print.term_to_string
                                                                    t2'  in
                                                                    FStar_Util.print4
                                                                    "Unfolding didn't make progress ... got %s ~> %s;\nand %s ~> %s\n"
                                                                    uu____17818
                                                                    uu____17820
                                                                    uu____17822
                                                                    uu____17824
                                                                    else ());
                                                                    solve_sub_probs
                                                                    env2 wl2)
                                                               | uu____17829
                                                                   ->
                                                                   let torig'
                                                                    =
                                                                    let uu___2598_17837
                                                                    = torig
                                                                     in
                                                                    {
                                                                    FStar_TypeChecker_Common.pid
                                                                    =
                                                                    (uu___2598_17837.FStar_TypeChecker_Common.pid);
                                                                    FStar_TypeChecker_Common.lhs
                                                                    = t1';
                                                                    FStar_TypeChecker_Common.relation
                                                                    =
                                                                    (uu___2598_17837.FStar_TypeChecker_Common.relation);
                                                                    FStar_TypeChecker_Common.rhs
                                                                    = t2';
                                                                    FStar_TypeChecker_Common.element
                                                                    =
                                                                    (uu___2598_17837.FStar_TypeChecker_Common.element);
                                                                    FStar_TypeChecker_Common.logical_guard
                                                                    =
                                                                    (uu___2598_17837.FStar_TypeChecker_Common.logical_guard);
                                                                    FStar_TypeChecker_Common.logical_guard_uvar
                                                                    =
                                                                    (uu___2598_17837.FStar_TypeChecker_Common.logical_guard_uvar);
                                                                    FStar_TypeChecker_Common.reason
                                                                    =
                                                                    (uu___2598_17837.FStar_TypeChecker_Common.reason);
                                                                    FStar_TypeChecker_Common.loc
                                                                    =
                                                                    (uu___2598_17837.FStar_TypeChecker_Common.loc);
                                                                    FStar_TypeChecker_Common.rank
                                                                    =
                                                                    (uu___2598_17837.FStar_TypeChecker_Common.rank)
                                                                    }  in
                                                                   ((
                                                                    let uu____17839
                                                                    =
                                                                    FStar_All.pipe_left
                                                                    (FStar_TypeChecker_Env.debug
                                                                    env2)
                                                                    (FStar_Options.Other
                                                                    "Rel")
                                                                     in
                                                                    if
                                                                    uu____17839
                                                                    then
                                                                    let uu____17844
                                                                    =
                                                                    prob_to_string
                                                                    env2
                                                                    (FStar_TypeChecker_Common.TProb
                                                                    torig')
                                                                     in
                                                                    FStar_Util.print1
                                                                    "Unfolded and now trying %s\n"
                                                                    uu____17844
                                                                    else ());
                                                                    solve_t
                                                                    env2
                                                                    torig'
                                                                    wl2))))
                                                | uu____17849 ->
                                                    solve_sub_probs env2 wl2)
                                            in
                                         let d =
                                           let uu____17861 =
                                             delta_depth_of_term env1 head1
                                              in
                                           match uu____17861 with
                                           | FStar_Pervasives_Native.None  ->
                                               FStar_Pervasives_Native.None
                                           | FStar_Pervasives_Native.Some d
                                               ->
                                               FStar_TypeChecker_Common.decr_delta_depth
                                                 d
                                            in
                                         let treat_as_injective =
                                           let uu____17869 =
                                             let uu____17870 =
                                               FStar_Syntax_Util.un_uinst
                                                 head1
                                                in
                                             uu____17870.FStar_Syntax_Syntax.n
                                              in
                                           match uu____17869 with
                                           | FStar_Syntax_Syntax.Tm_fvar fv
                                               ->
                                               FStar_TypeChecker_Env.fv_has_attr
                                                 env1 fv
                                                 FStar_Parser_Const.unifier_hint_injective_lid
                                           | uu____17875 -> false  in
                                         (match d with
                                          | FStar_Pervasives_Native.Some d1
                                              when
                                              wl1.smt_ok &&
                                                (Prims.op_Negation
                                                   treat_as_injective)
                                              ->
                                              try_solve_without_smt_or_else
                                                orig env1 wl1
                                                solve_sub_probs_no_smt
                                                (unfold_and_retry d1)
                                          | uu____17878 ->
                                              solve_sub_probs env1 wl1)
                                     | uu____17881 ->
                                         let lhs =
                                           force_refinement
                                             (base1, refinement1)
                                            in
                                         let rhs =
                                           force_refinement
                                             (base2, refinement2)
                                            in
                                         solve_t env1
                                           (let uu___2618_17917 = problem  in
                                            {
                                              FStar_TypeChecker_Common.pid =
                                                (uu___2618_17917.FStar_TypeChecker_Common.pid);
                                              FStar_TypeChecker_Common.lhs =
                                                lhs;
                                              FStar_TypeChecker_Common.relation
                                                =
                                                (uu___2618_17917.FStar_TypeChecker_Common.relation);
                                              FStar_TypeChecker_Common.rhs =
                                                rhs;
                                              FStar_TypeChecker_Common.element
                                                =
                                                (uu___2618_17917.FStar_TypeChecker_Common.element);
                                              FStar_TypeChecker_Common.logical_guard
                                                =
                                                (uu___2618_17917.FStar_TypeChecker_Common.logical_guard);
                                              FStar_TypeChecker_Common.logical_guard_uvar
                                                =
                                                (uu___2618_17917.FStar_TypeChecker_Common.logical_guard_uvar);
                                              FStar_TypeChecker_Common.reason
                                                =
                                                (uu___2618_17917.FStar_TypeChecker_Common.reason);
                                              FStar_TypeChecker_Common.loc =
                                                (uu___2618_17917.FStar_TypeChecker_Common.loc);
                                              FStar_TypeChecker_Common.rank =
                                                (uu___2618_17917.FStar_TypeChecker_Common.rank)
                                            }) wl1))))))
            in
         let try_match_heuristic env1 orig wl1 s1 s2 t1t2_opt =
           let try_solve_branch scrutinee p =
             let uu____17993 = destruct_flex_t scrutinee wl1  in
             match uu____17993 with
             | ((_t,uv,_args),wl2) ->
                 let uu____18004 =
                   FStar_TypeChecker_PatternUtils.pat_as_exp true env1 p  in
                 (match uu____18004 with
                  | (xs,pat_term,uu____18020,uu____18021) ->
                      let uu____18026 =
                        FStar_List.fold_left
                          (fun uu____18049  ->
                             fun x  ->
                               match uu____18049 with
                               | (subst1,wl3) ->
                                   let t_x =
                                     FStar_Syntax_Subst.subst subst1
                                       x.FStar_Syntax_Syntax.sort
                                      in
                                   let uu____18070 = copy_uvar uv [] t_x wl3
                                      in
                                   (match uu____18070 with
                                    | (uu____18089,u,wl4) ->
                                        let subst2 =
                                          (FStar_Syntax_Syntax.NT (x, u)) ::
                                          subst1  in
                                        (subst2, wl4))) ([], wl2) xs
                         in
                      (match uu____18026 with
                       | (subst1,wl3) ->
                           let pat_term1 =
                             FStar_Syntax_Subst.subst subst1 pat_term  in
                           let uu____18110 =
                             new_problem wl3 env1 scrutinee
                               FStar_TypeChecker_Common.EQ pat_term1
                               FStar_Pervasives_Native.None
                               scrutinee.FStar_Syntax_Syntax.pos
                               "match heuristic"
                              in
                           (match uu____18110 with
                            | (prob,wl4) ->
                                let wl' =
                                  let uu___2658_18127 = wl4  in
                                  {
                                    attempting =
                                      [FStar_TypeChecker_Common.TProb prob];
                                    wl_deferred = [];
                                    ctr = (uu___2658_18127.ctr);
                                    defer_ok = false;
                                    smt_ok = false;
                                    umax_heuristic_ok =
                                      (uu___2658_18127.umax_heuristic_ok);
                                    tcenv = (uu___2658_18127.tcenv);
                                    wl_implicits = []
                                  }  in
                                let tx =
                                  FStar_Syntax_Unionfind.new_transaction ()
                                   in
                                let uu____18138 = solve env1 wl'  in
                                (match uu____18138 with
                                 | Success (uu____18141,imps) ->
                                     let wl'1 =
                                       let uu___2666_18144 = wl'  in
                                       {
                                         attempting = [orig];
                                         wl_deferred =
                                           (uu___2666_18144.wl_deferred);
                                         ctr = (uu___2666_18144.ctr);
                                         defer_ok =
                                           (uu___2666_18144.defer_ok);
                                         smt_ok = (uu___2666_18144.smt_ok);
                                         umax_heuristic_ok =
                                           (uu___2666_18144.umax_heuristic_ok);
                                         tcenv = (uu___2666_18144.tcenv);
                                         wl_implicits =
                                           (uu___2666_18144.wl_implicits)
                                       }  in
                                     let uu____18145 = solve env1 wl'1  in
                                     (match uu____18145 with
                                      | Success (uu____18148,imps') ->
                                          (FStar_Syntax_Unionfind.commit tx;
                                           FStar_Pervasives_Native.Some
                                             ((let uu___2674_18152 = wl4  in
                                               {
                                                 attempting =
                                                   (uu___2674_18152.attempting);
                                                 wl_deferred =
                                                   (uu___2674_18152.wl_deferred);
                                                 ctr = (uu___2674_18152.ctr);
                                                 defer_ok =
                                                   (uu___2674_18152.defer_ok);
                                                 smt_ok =
                                                   (uu___2674_18152.smt_ok);
                                                 umax_heuristic_ok =
                                                   (uu___2674_18152.umax_heuristic_ok);
                                                 tcenv =
                                                   (uu___2674_18152.tcenv);
                                                 wl_implicits =
                                                   (FStar_List.append
                                                      wl4.wl_implicits
                                                      (FStar_List.append imps
                                                         imps'))
                                               })))
                                      | Failed uu____18153 ->
                                          (FStar_Syntax_Unionfind.rollback tx;
                                           FStar_Pervasives_Native.None))
                                 | uu____18159 ->
                                     (FStar_Syntax_Unionfind.rollback tx;
                                      FStar_Pervasives_Native.None)))))
              in
           match t1t2_opt with
           | FStar_Pervasives_Native.None  ->
               FStar_Util.Inr FStar_Pervasives_Native.None
           | FStar_Pervasives_Native.Some (t1,t2) ->
               ((let uu____18182 =
                   FStar_All.pipe_left (FStar_TypeChecker_Env.debug env1)
                     (FStar_Options.Other "Rel")
                    in
                 if uu____18182
                 then
                   let uu____18187 = FStar_Syntax_Print.term_to_string t1  in
                   let uu____18189 = FStar_Syntax_Print.term_to_string t2  in
                   FStar_Util.print2 "Trying match heuristic for %s vs. %s\n"
                     uu____18187 uu____18189
                 else ());
                (let uu____18194 =
                   let uu____18215 =
                     let uu____18224 = FStar_Syntax_Util.unmeta t1  in
                     (s1, uu____18224)  in
                   let uu____18231 =
                     let uu____18240 = FStar_Syntax_Util.unmeta t2  in
                     (s2, uu____18240)  in
                   (uu____18215, uu____18231)  in
                 match uu____18194 with
                 | ((uu____18270,{
                                   FStar_Syntax_Syntax.n =
                                     FStar_Syntax_Syntax.Tm_match
                                     (scrutinee,branches);
                                   FStar_Syntax_Syntax.pos = uu____18273;
                                   FStar_Syntax_Syntax.vars = uu____18274;_}),
                    (s,t)) ->
                     let uu____18345 =
                       let uu____18347 = is_flex scrutinee  in
                       Prims.op_Negation uu____18347  in
                     if uu____18345
                     then
                       ((let uu____18358 =
                           FStar_All.pipe_left
                             (FStar_TypeChecker_Env.debug env1)
                             (FStar_Options.Other "Rel")
                            in
                         if uu____18358
                         then
                           let uu____18363 =
                             FStar_Syntax_Print.term_to_string scrutinee  in
                           FStar_Util.print1
                             "match head %s is not a flex term\n" uu____18363
                         else ());
                        FStar_Util.Inr FStar_Pervasives_Native.None)
                     else
                       if wl1.defer_ok
                       then
                         ((let uu____18382 =
                             FStar_All.pipe_left
                               (FStar_TypeChecker_Env.debug env1)
                               (FStar_Options.Other "Rel")
                              in
                           if uu____18382
                           then FStar_Util.print_string "Deferring ... \n"
                           else ());
                          FStar_Util.Inl "defer")
                       else
                         ((let uu____18397 =
                             FStar_All.pipe_left
                               (FStar_TypeChecker_Env.debug env1)
                               (FStar_Options.Other "Rel")
                              in
                           if uu____18397
                           then
                             let uu____18402 =
                               FStar_Syntax_Print.term_to_string scrutinee
                                in
                             let uu____18404 =
                               FStar_Syntax_Print.term_to_string t  in
                             FStar_Util.print2
                               "Heuristic applicable with scrutinee %s and other side = %s\n"
                               uu____18402 uu____18404
                           else ());
                          (let pat_discriminates uu___28_18429 =
                             match uu___28_18429 with
                             | ({
                                  FStar_Syntax_Syntax.v =
                                    FStar_Syntax_Syntax.Pat_constant
                                    uu____18445;
                                  FStar_Syntax_Syntax.p = uu____18446;_},FStar_Pervasives_Native.None
                                ,uu____18447) -> true
                             | ({
                                  FStar_Syntax_Syntax.v =
                                    FStar_Syntax_Syntax.Pat_cons uu____18461;
                                  FStar_Syntax_Syntax.p = uu____18462;_},FStar_Pervasives_Native.None
                                ,uu____18463) -> true
                             | uu____18490 -> false  in
                           let head_matching_branch =
                             FStar_All.pipe_right branches
                               (FStar_Util.try_find
                                  (fun b  ->
                                     if pat_discriminates b
                                     then
                                       let uu____18593 =
                                         FStar_Syntax_Subst.open_branch b  in
                                       match uu____18593 with
                                       | (uu____18595,uu____18596,t') ->
                                           let uu____18614 =
                                             head_matches_delta env1 wl1 s t'
                                              in
                                           (match uu____18614 with
                                            | (FullMatch ,uu____18626) ->
                                                true
                                            | (HeadMatch
                                               uu____18640,uu____18641) ->
                                                true
                                            | uu____18656 -> false)
                                     else false))
                              in
                           match head_matching_branch with
                           | FStar_Pervasives_Native.None  ->
                               ((let uu____18693 =
                                   FStar_All.pipe_left
                                     (FStar_TypeChecker_Env.debug env1)
                                     (FStar_Options.Other "Rel")
                                    in
                                 if uu____18693
                                 then
                                   FStar_Util.print_string
                                     "No head_matching branch\n"
                                 else ());
                                (let try_branches =
                                   let uu____18704 =
                                     FStar_Util.prefix_until
                                       (fun b  ->
                                          Prims.op_Negation
                                            (pat_discriminates b)) branches
                                      in
                                   match uu____18704 with
                                   | FStar_Pervasives_Native.Some
                                       (branches1,uu____18792,uu____18793) ->
                                       branches1
                                   | uu____18938 -> branches  in
                                 let uu____18993 =
                                   FStar_Util.find_map try_branches
                                     (fun b  ->
                                        let uu____19002 =
                                          FStar_Syntax_Subst.open_branch b
                                           in
                                        match uu____19002 with
                                        | (p,uu____19006,uu____19007) ->
                                            try_solve_branch scrutinee p)
                                    in
                                 FStar_All.pipe_left
                                   (fun _19036  -> FStar_Util.Inr _19036)
                                   uu____18993))
                           | FStar_Pervasives_Native.Some b ->
                               let uu____19066 =
                                 FStar_Syntax_Subst.open_branch b  in
                               (match uu____19066 with
                                | (p,uu____19075,e) ->
                                    ((let uu____19094 =
                                        FStar_All.pipe_left
                                          (FStar_TypeChecker_Env.debug env1)
                                          (FStar_Options.Other "Rel")
                                         in
                                      if uu____19094
                                      then
                                        let uu____19099 =
                                          FStar_Syntax_Print.pat_to_string p
                                           in
                                        let uu____19101 =
                                          FStar_Syntax_Print.term_to_string e
                                           in
                                        FStar_Util.print2
                                          "Found head matching branch %s -> %s\n"
                                          uu____19099 uu____19101
                                      else ());
                                     (let uu____19106 =
                                        try_solve_branch scrutinee p  in
                                      FStar_All.pipe_left
                                        (fun _19121  -> FStar_Util.Inr _19121)
                                        uu____19106)))))
                 | ((s,t),(uu____19124,{
                                         FStar_Syntax_Syntax.n =
                                           FStar_Syntax_Syntax.Tm_match
                                           (scrutinee,branches);
                                         FStar_Syntax_Syntax.pos =
                                           uu____19127;
                                         FStar_Syntax_Syntax.vars =
                                           uu____19128;_}))
                     ->
                     let uu____19197 =
                       let uu____19199 = is_flex scrutinee  in
                       Prims.op_Negation uu____19199  in
                     if uu____19197
                     then
                       ((let uu____19210 =
                           FStar_All.pipe_left
                             (FStar_TypeChecker_Env.debug env1)
                             (FStar_Options.Other "Rel")
                            in
                         if uu____19210
                         then
                           let uu____19215 =
                             FStar_Syntax_Print.term_to_string scrutinee  in
                           FStar_Util.print1
                             "match head %s is not a flex term\n" uu____19215
                         else ());
                        FStar_Util.Inr FStar_Pervasives_Native.None)
                     else
                       if wl1.defer_ok
                       then
                         ((let uu____19234 =
                             FStar_All.pipe_left
                               (FStar_TypeChecker_Env.debug env1)
                               (FStar_Options.Other "Rel")
                              in
                           if uu____19234
                           then FStar_Util.print_string "Deferring ... \n"
                           else ());
                          FStar_Util.Inl "defer")
                       else
                         ((let uu____19249 =
                             FStar_All.pipe_left
                               (FStar_TypeChecker_Env.debug env1)
                               (FStar_Options.Other "Rel")
                              in
                           if uu____19249
                           then
                             let uu____19254 =
                               FStar_Syntax_Print.term_to_string scrutinee
                                in
                             let uu____19256 =
                               FStar_Syntax_Print.term_to_string t  in
                             FStar_Util.print2
                               "Heuristic applicable with scrutinee %s and other side = %s\n"
                               uu____19254 uu____19256
                           else ());
                          (let pat_discriminates uu___28_19281 =
                             match uu___28_19281 with
                             | ({
                                  FStar_Syntax_Syntax.v =
                                    FStar_Syntax_Syntax.Pat_constant
                                    uu____19297;
                                  FStar_Syntax_Syntax.p = uu____19298;_},FStar_Pervasives_Native.None
                                ,uu____19299) -> true
                             | ({
                                  FStar_Syntax_Syntax.v =
                                    FStar_Syntax_Syntax.Pat_cons uu____19313;
                                  FStar_Syntax_Syntax.p = uu____19314;_},FStar_Pervasives_Native.None
                                ,uu____19315) -> true
                             | uu____19342 -> false  in
                           let head_matching_branch =
                             FStar_All.pipe_right branches
                               (FStar_Util.try_find
                                  (fun b  ->
                                     if pat_discriminates b
                                     then
                                       let uu____19445 =
                                         FStar_Syntax_Subst.open_branch b  in
                                       match uu____19445 with
                                       | (uu____19447,uu____19448,t') ->
                                           let uu____19466 =
                                             head_matches_delta env1 wl1 s t'
                                              in
                                           (match uu____19466 with
                                            | (FullMatch ,uu____19478) ->
                                                true
                                            | (HeadMatch
                                               uu____19492,uu____19493) ->
                                                true
                                            | uu____19508 -> false)
                                     else false))
                              in
                           match head_matching_branch with
                           | FStar_Pervasives_Native.None  ->
                               ((let uu____19545 =
                                   FStar_All.pipe_left
                                     (FStar_TypeChecker_Env.debug env1)
                                     (FStar_Options.Other "Rel")
                                    in
                                 if uu____19545
                                 then
                                   FStar_Util.print_string
                                     "No head_matching branch\n"
                                 else ());
                                (let try_branches =
                                   let uu____19556 =
                                     FStar_Util.prefix_until
                                       (fun b  ->
                                          Prims.op_Negation
                                            (pat_discriminates b)) branches
                                      in
                                   match uu____19556 with
                                   | FStar_Pervasives_Native.Some
                                       (branches1,uu____19644,uu____19645) ->
                                       branches1
                                   | uu____19790 -> branches  in
                                 let uu____19845 =
                                   FStar_Util.find_map try_branches
                                     (fun b  ->
                                        let uu____19854 =
                                          FStar_Syntax_Subst.open_branch b
                                           in
                                        match uu____19854 with
                                        | (p,uu____19858,uu____19859) ->
                                            try_solve_branch scrutinee p)
                                    in
                                 FStar_All.pipe_left
                                   (fun _19888  -> FStar_Util.Inr _19888)
                                   uu____19845))
                           | FStar_Pervasives_Native.Some b ->
                               let uu____19918 =
                                 FStar_Syntax_Subst.open_branch b  in
                               (match uu____19918 with
                                | (p,uu____19927,e) ->
                                    ((let uu____19946 =
                                        FStar_All.pipe_left
                                          (FStar_TypeChecker_Env.debug env1)
                                          (FStar_Options.Other "Rel")
                                         in
                                      if uu____19946
                                      then
                                        let uu____19951 =
                                          FStar_Syntax_Print.pat_to_string p
                                           in
                                        let uu____19953 =
                                          FStar_Syntax_Print.term_to_string e
                                           in
                                        FStar_Util.print2
                                          "Found head matching branch %s -> %s\n"
                                          uu____19951 uu____19953
                                      else ());
                                     (let uu____19958 =
                                        try_solve_branch scrutinee p  in
                                      FStar_All.pipe_left
                                        (fun _19973  -> FStar_Util.Inr _19973)
                                        uu____19958)))))
                 | uu____19974 ->
                     ((let uu____19996 =
                         FStar_All.pipe_left
                           (FStar_TypeChecker_Env.debug env1)
                           (FStar_Options.Other "Rel")
                          in
                       if uu____19996
                       then
                         let uu____20001 = FStar_Syntax_Print.tag_of_term t1
                            in
                         let uu____20003 = FStar_Syntax_Print.tag_of_term t2
                            in
                         FStar_Util.print2
                           "Heuristic not applicable: tag lhs=%s, rhs=%s\n"
                           uu____20001 uu____20003
                       else ());
                      FStar_Util.Inr FStar_Pervasives_Native.None)))
            in
         let rigid_rigid_delta env1 torig wl1 head1 head2 t1 t2 =
           let orig = FStar_TypeChecker_Common.TProb torig  in
           (let uu____20049 =
              FStar_All.pipe_left (FStar_TypeChecker_Env.debug env1)
                (FStar_Options.Other "RelDelta")
               in
            if uu____20049
            then
              let uu____20054 = FStar_Syntax_Print.tag_of_term t1  in
              let uu____20056 = FStar_Syntax_Print.tag_of_term t2  in
              let uu____20058 = FStar_Syntax_Print.term_to_string t1  in
              let uu____20060 = FStar_Syntax_Print.term_to_string t2  in
              FStar_Util.print4 "rigid_rigid_delta of %s-%s (%s, %s)\n"
                uu____20054 uu____20056 uu____20058 uu____20060
            else ());
           (let uu____20065 = head_matches_delta env1 wl1 t1 t2  in
            match uu____20065 with
            | (m,o) ->
                (match (m, o) with
                 | (MisMatch uu____20096,uu____20097) ->
                     let rec may_relate head3 =
                       let uu____20125 =
                         let uu____20126 = FStar_Syntax_Subst.compress head3
                            in
                         uu____20126.FStar_Syntax_Syntax.n  in
                       match uu____20125 with
                       | FStar_Syntax_Syntax.Tm_name uu____20130 -> true
                       | FStar_Syntax_Syntax.Tm_match uu____20132 -> true
                       | FStar_Syntax_Syntax.Tm_fvar fv ->
                           let uu____20157 =
                             FStar_TypeChecker_Env.delta_depth_of_fv env1 fv
                              in
                           (match uu____20157 with
                            | FStar_Syntax_Syntax.Delta_equational_at_level
                                uu____20159 -> true
                            | FStar_Syntax_Syntax.Delta_abstract uu____20162
                                ->
                                problem.FStar_TypeChecker_Common.relation =
                                  FStar_TypeChecker_Common.EQ
                            | uu____20163 -> false)
                       | FStar_Syntax_Syntax.Tm_ascribed
                           (t,uu____20166,uu____20167) -> may_relate t
                       | FStar_Syntax_Syntax.Tm_uinst (t,uu____20209) ->
                           may_relate t
                       | FStar_Syntax_Syntax.Tm_meta (t,uu____20215) ->
                           may_relate t
                       | uu____20220 -> false  in
                     let uu____20222 =
                       try_match_heuristic env1 orig wl1 t1 t2 o  in
                     (match uu____20222 with
                      | FStar_Util.Inl _defer_ok ->
                          let uu____20235 =
                            FStar_Thunk.mkv "delaying match heuristic"  in
                          giveup_or_defer1 orig uu____20235
                      | FStar_Util.Inr (FStar_Pervasives_Native.Some wl2) ->
                          solve env1 wl2
                      | FStar_Util.Inr (FStar_Pervasives_Native.None ) ->
                          let uu____20245 =
                            ((may_relate head1) || (may_relate head2)) &&
                              wl1.smt_ok
                             in
                          if uu____20245
                          then
                            let uu____20248 =
                              guard_of_prob env1 wl1 problem t1 t2  in
                            (match uu____20248 with
                             | (guard,wl2) ->
                                 let uu____20255 =
                                   solve_prob orig
                                     (FStar_Pervasives_Native.Some guard) []
                                     wl2
                                    in
                                 solve env1 uu____20255)
                          else
                            (let uu____20258 =
                               FStar_Thunk.mk
                                 (fun uu____20265  ->
                                    let uu____20266 =
                                      FStar_Syntax_Print.term_to_string head1
                                       in
                                    let uu____20268 =
                                      let uu____20270 =
                                        let uu____20274 =
                                          delta_depth_of_term env1 head1  in
                                        FStar_Util.bind_opt uu____20274
                                          (fun x  ->
                                             let uu____20281 =
                                               FStar_Syntax_Print.delta_depth_to_string
                                                 x
                                                in
                                             FStar_Pervasives_Native.Some
                                               uu____20281)
                                         in
                                      FStar_Util.dflt "" uu____20270  in
                                    let uu____20286 =
                                      FStar_Syntax_Print.term_to_string head2
                                       in
                                    let uu____20288 =
                                      let uu____20290 =
                                        let uu____20294 =
                                          delta_depth_of_term env1 head2  in
                                        FStar_Util.bind_opt uu____20294
                                          (fun x  ->
                                             let uu____20301 =
                                               FStar_Syntax_Print.delta_depth_to_string
                                                 x
                                                in
                                             FStar_Pervasives_Native.Some
                                               uu____20301)
                                         in
                                      FStar_Util.dflt "" uu____20290  in
                                    FStar_Util.format4
                                      "head mismatch (%s (%s) vs %s (%s))"
                                      uu____20266 uu____20268 uu____20286
                                      uu____20288)
                                in
                             giveup env1 uu____20258 orig))
                 | (HeadMatch (true ),uu____20307) when
                     problem.FStar_TypeChecker_Common.relation <>
                       FStar_TypeChecker_Common.EQ
                     ->
                     if wl1.smt_ok
                     then
                       let uu____20322 = guard_of_prob env1 wl1 problem t1 t2
                          in
                       (match uu____20322 with
                        | (guard,wl2) ->
                            let uu____20329 =
                              solve_prob orig
                                (FStar_Pervasives_Native.Some guard) [] wl2
                               in
                            solve env1 uu____20329)
                     else
                       (let uu____20332 =
                          FStar_Thunk.mk
                            (fun uu____20337  ->
                               let uu____20338 =
                                 FStar_Syntax_Print.term_to_string t1  in
                               let uu____20340 =
                                 FStar_Syntax_Print.term_to_string t2  in
                               FStar_Util.format2
                                 "head mismatch for subtyping (%s vs %s)"
                                 uu____20338 uu____20340)
                           in
                        giveup env1 uu____20332 orig)
                 | (uu____20343,FStar_Pervasives_Native.Some (t11,t21)) ->
                     solve_t env1
                       (let uu___2849_20357 = problem  in
                        {
                          FStar_TypeChecker_Common.pid =
                            (uu___2849_20357.FStar_TypeChecker_Common.pid);
                          FStar_TypeChecker_Common.lhs = t11;
                          FStar_TypeChecker_Common.relation =
                            (uu___2849_20357.FStar_TypeChecker_Common.relation);
                          FStar_TypeChecker_Common.rhs = t21;
                          FStar_TypeChecker_Common.element =
                            (uu___2849_20357.FStar_TypeChecker_Common.element);
                          FStar_TypeChecker_Common.logical_guard =
                            (uu___2849_20357.FStar_TypeChecker_Common.logical_guard);
                          FStar_TypeChecker_Common.logical_guard_uvar =
                            (uu___2849_20357.FStar_TypeChecker_Common.logical_guard_uvar);
                          FStar_TypeChecker_Common.reason =
                            (uu___2849_20357.FStar_TypeChecker_Common.reason);
                          FStar_TypeChecker_Common.loc =
                            (uu___2849_20357.FStar_TypeChecker_Common.loc);
                          FStar_TypeChecker_Common.rank =
                            (uu___2849_20357.FStar_TypeChecker_Common.rank)
                        }) wl1
                 | (HeadMatch need_unif,FStar_Pervasives_Native.None ) ->
                     rigid_heads_match env1 need_unif torig wl1 t1 t2
                 | (FullMatch ,FStar_Pervasives_Native.None ) ->
                     rigid_heads_match env1 false torig wl1 t1 t2))
            in
         let orig = FStar_TypeChecker_Common.TProb problem  in
         def_check_prob "solve_t'.2" orig;
         (let uu____20384 =
            FStar_Util.physical_equality problem.FStar_TypeChecker_Common.lhs
              problem.FStar_TypeChecker_Common.rhs
             in
          if uu____20384
          then
            let uu____20387 =
              solve_prob orig FStar_Pervasives_Native.None [] wl  in
            solve env uu____20387
          else
            (let t1 = problem.FStar_TypeChecker_Common.lhs  in
             let t2 = problem.FStar_TypeChecker_Common.rhs  in
             (let uu____20393 =
                let uu____20396 = p_scope orig  in
                FStar_List.map FStar_Pervasives_Native.fst uu____20396  in
              FStar_TypeChecker_Env.def_check_closed_in (p_loc orig) "ref.t1"
                uu____20393 t1);
             (let uu____20415 =
                let uu____20418 = p_scope orig  in
                FStar_List.map FStar_Pervasives_Native.fst uu____20418  in
              FStar_TypeChecker_Env.def_check_closed_in (p_loc orig) "ref.t2"
                uu____20415 t2);
             (let uu____20437 =
                FStar_TypeChecker_Env.debug env (FStar_Options.Other "Rel")
                 in
              if uu____20437
              then
                let uu____20441 =
                  FStar_Util.string_of_int
                    problem.FStar_TypeChecker_Common.pid
                   in
                let uu____20443 =
                  let uu____20445 = FStar_Syntax_Print.tag_of_term t1  in
                  let uu____20447 =
                    let uu____20449 = FStar_Syntax_Print.term_to_string t1
                       in
                    Prims.op_Hat "::" uu____20449  in
                  Prims.op_Hat uu____20445 uu____20447  in
                let uu____20452 =
                  let uu____20454 = FStar_Syntax_Print.tag_of_term t2  in
                  let uu____20456 =
                    let uu____20458 = FStar_Syntax_Print.term_to_string t2
                       in
                    Prims.op_Hat "::" uu____20458  in
                  Prims.op_Hat uu____20454 uu____20456  in
                FStar_Util.print4 "Attempting %s (%s vs %s); rel = (%s)\n"
                  uu____20441 uu____20443 uu____20452
                  (rel_to_string problem.FStar_TypeChecker_Common.relation)
              else ());
             (let r = FStar_TypeChecker_Env.get_range env  in
              match ((t1.FStar_Syntax_Syntax.n), (t2.FStar_Syntax_Syntax.n))
              with
              | (FStar_Syntax_Syntax.Tm_delayed uu____20465,uu____20466) ->
                  failwith "Impossible: terms were not compressed"
              | (uu____20482,FStar_Syntax_Syntax.Tm_delayed uu____20483) ->
                  failwith "Impossible: terms were not compressed"
              | (FStar_Syntax_Syntax.Tm_ascribed uu____20499,uu____20500) ->
                  let uu____20527 =
                    let uu___2880_20528 = problem  in
                    let uu____20529 = FStar_Syntax_Util.unascribe t1  in
                    {
                      FStar_TypeChecker_Common.pid =
                        (uu___2880_20528.FStar_TypeChecker_Common.pid);
                      FStar_TypeChecker_Common.lhs = uu____20529;
                      FStar_TypeChecker_Common.relation =
                        (uu___2880_20528.FStar_TypeChecker_Common.relation);
                      FStar_TypeChecker_Common.rhs =
                        (uu___2880_20528.FStar_TypeChecker_Common.rhs);
                      FStar_TypeChecker_Common.element =
                        (uu___2880_20528.FStar_TypeChecker_Common.element);
                      FStar_TypeChecker_Common.logical_guard =
                        (uu___2880_20528.FStar_TypeChecker_Common.logical_guard);
                      FStar_TypeChecker_Common.logical_guard_uvar =
                        (uu___2880_20528.FStar_TypeChecker_Common.logical_guard_uvar);
                      FStar_TypeChecker_Common.reason =
                        (uu___2880_20528.FStar_TypeChecker_Common.reason);
                      FStar_TypeChecker_Common.loc =
                        (uu___2880_20528.FStar_TypeChecker_Common.loc);
                      FStar_TypeChecker_Common.rank =
                        (uu___2880_20528.FStar_TypeChecker_Common.rank)
                    }  in
                  solve_t' env uu____20527 wl
              | (FStar_Syntax_Syntax.Tm_meta uu____20530,uu____20531) ->
                  let uu____20538 =
                    let uu___2886_20539 = problem  in
                    let uu____20540 = FStar_Syntax_Util.unmeta t1  in
                    {
                      FStar_TypeChecker_Common.pid =
                        (uu___2886_20539.FStar_TypeChecker_Common.pid);
                      FStar_TypeChecker_Common.lhs = uu____20540;
                      FStar_TypeChecker_Common.relation =
                        (uu___2886_20539.FStar_TypeChecker_Common.relation);
                      FStar_TypeChecker_Common.rhs =
                        (uu___2886_20539.FStar_TypeChecker_Common.rhs);
                      FStar_TypeChecker_Common.element =
                        (uu___2886_20539.FStar_TypeChecker_Common.element);
                      FStar_TypeChecker_Common.logical_guard =
                        (uu___2886_20539.FStar_TypeChecker_Common.logical_guard);
                      FStar_TypeChecker_Common.logical_guard_uvar =
                        (uu___2886_20539.FStar_TypeChecker_Common.logical_guard_uvar);
                      FStar_TypeChecker_Common.reason =
                        (uu___2886_20539.FStar_TypeChecker_Common.reason);
                      FStar_TypeChecker_Common.loc =
                        (uu___2886_20539.FStar_TypeChecker_Common.loc);
                      FStar_TypeChecker_Common.rank =
                        (uu___2886_20539.FStar_TypeChecker_Common.rank)
                    }  in
                  solve_t' env uu____20538 wl
              | (uu____20541,FStar_Syntax_Syntax.Tm_ascribed uu____20542) ->
                  let uu____20569 =
                    let uu___2892_20570 = problem  in
                    let uu____20571 = FStar_Syntax_Util.unascribe t2  in
                    {
                      FStar_TypeChecker_Common.pid =
                        (uu___2892_20570.FStar_TypeChecker_Common.pid);
                      FStar_TypeChecker_Common.lhs =
                        (uu___2892_20570.FStar_TypeChecker_Common.lhs);
                      FStar_TypeChecker_Common.relation =
                        (uu___2892_20570.FStar_TypeChecker_Common.relation);
                      FStar_TypeChecker_Common.rhs = uu____20571;
                      FStar_TypeChecker_Common.element =
                        (uu___2892_20570.FStar_TypeChecker_Common.element);
                      FStar_TypeChecker_Common.logical_guard =
                        (uu___2892_20570.FStar_TypeChecker_Common.logical_guard);
                      FStar_TypeChecker_Common.logical_guard_uvar =
                        (uu___2892_20570.FStar_TypeChecker_Common.logical_guard_uvar);
                      FStar_TypeChecker_Common.reason =
                        (uu___2892_20570.FStar_TypeChecker_Common.reason);
                      FStar_TypeChecker_Common.loc =
                        (uu___2892_20570.FStar_TypeChecker_Common.loc);
                      FStar_TypeChecker_Common.rank =
                        (uu___2892_20570.FStar_TypeChecker_Common.rank)
                    }  in
                  solve_t' env uu____20569 wl
              | (uu____20572,FStar_Syntax_Syntax.Tm_meta uu____20573) ->
                  let uu____20580 =
                    let uu___2898_20581 = problem  in
                    let uu____20582 = FStar_Syntax_Util.unmeta t2  in
                    {
                      FStar_TypeChecker_Common.pid =
                        (uu___2898_20581.FStar_TypeChecker_Common.pid);
                      FStar_TypeChecker_Common.lhs =
                        (uu___2898_20581.FStar_TypeChecker_Common.lhs);
                      FStar_TypeChecker_Common.relation =
                        (uu___2898_20581.FStar_TypeChecker_Common.relation);
                      FStar_TypeChecker_Common.rhs = uu____20582;
                      FStar_TypeChecker_Common.element =
                        (uu___2898_20581.FStar_TypeChecker_Common.element);
                      FStar_TypeChecker_Common.logical_guard =
                        (uu___2898_20581.FStar_TypeChecker_Common.logical_guard);
                      FStar_TypeChecker_Common.logical_guard_uvar =
                        (uu___2898_20581.FStar_TypeChecker_Common.logical_guard_uvar);
                      FStar_TypeChecker_Common.reason =
                        (uu___2898_20581.FStar_TypeChecker_Common.reason);
                      FStar_TypeChecker_Common.loc =
                        (uu___2898_20581.FStar_TypeChecker_Common.loc);
                      FStar_TypeChecker_Common.rank =
                        (uu___2898_20581.FStar_TypeChecker_Common.rank)
                    }  in
                  solve_t' env uu____20580 wl
              | (FStar_Syntax_Syntax.Tm_quoted
                 (t11,uu____20584),FStar_Syntax_Syntax.Tm_quoted
                 (t21,uu____20586)) ->
                  let uu____20595 =
                    solve_prob orig FStar_Pervasives_Native.None [] wl  in
                  solve env uu____20595
              | (FStar_Syntax_Syntax.Tm_bvar uu____20596,uu____20597) ->
                  failwith
                    "Only locally nameless! We should never see a de Bruijn variable"
              | (uu____20599,FStar_Syntax_Syntax.Tm_bvar uu____20600) ->
                  failwith
                    "Only locally nameless! We should never see a de Bruijn variable"
              | (FStar_Syntax_Syntax.Tm_type u1,FStar_Syntax_Syntax.Tm_type
                 u2) -> solve_one_universe_eq env orig u1 u2 wl
              | (FStar_Syntax_Syntax.Tm_arrow
                 (bs1,c1),FStar_Syntax_Syntax.Tm_arrow (bs2,c2)) ->
                  let mk_c c uu___29_20670 =
                    match uu___29_20670 with
                    | [] -> c
                    | bs ->
                        let uu____20698 =
                          FStar_Syntax_Syntax.mk
                            (FStar_Syntax_Syntax.Tm_arrow (bs, c))
                            FStar_Pervasives_Native.None
                            c.FStar_Syntax_Syntax.pos
                           in
                        FStar_Syntax_Syntax.mk_Total uu____20698
                     in
                  let uu____20709 =
                    match_num_binders (bs1, (mk_c c1)) (bs2, (mk_c c2))  in
                  (match uu____20709 with
                   | ((bs11,c11),(bs21,c21)) ->
                       solve_binders env bs11 bs21 orig wl
                         (fun wl1  ->
                            fun scope  ->
                              fun env1  ->
                                fun subst1  ->
                                  let c12 =
                                    FStar_Syntax_Subst.subst_comp subst1 c11
                                     in
                                  let c22 =
                                    FStar_Syntax_Subst.subst_comp subst1 c21
                                     in
                                  let rel =
                                    let uu____20858 =
                                      FStar_Options.use_eq_at_higher_order ()
                                       in
                                    if uu____20858
                                    then FStar_TypeChecker_Common.EQ
                                    else
                                      problem.FStar_TypeChecker_Common.relation
                                     in
                                  mk_c_problem wl1 scope orig c12 rel c22
                                    FStar_Pervasives_Native.None
                                    "function co-domain"))
              | (FStar_Syntax_Syntax.Tm_abs
                 (bs1,tbody1,lopt1),FStar_Syntax_Syntax.Tm_abs
                 (bs2,tbody2,lopt2)) ->
                  let mk_t t l uu___30_20947 =
                    match uu___30_20947 with
                    | [] -> t
                    | bs ->
                        FStar_Syntax_Syntax.mk
                          (FStar_Syntax_Syntax.Tm_abs (bs, t, l))
                          FStar_Pervasives_Native.None
                          t.FStar_Syntax_Syntax.pos
                     in
                  let uu____20989 =
                    match_num_binders (bs1, (mk_t tbody1 lopt1))
                      (bs2, (mk_t tbody2 lopt2))
                     in
                  (match uu____20989 with
                   | ((bs11,tbody11),(bs21,tbody21)) ->
                       solve_binders env bs11 bs21 orig wl
                         (fun wl1  ->
                            fun scope  ->
                              fun env1  ->
                                fun subst1  ->
                                  let uu____21134 =
                                    FStar_Syntax_Subst.subst subst1 tbody11
                                     in
                                  let uu____21135 =
                                    FStar_Syntax_Subst.subst subst1 tbody21
                                     in
                                  mk_t_problem wl1 scope orig uu____21134
                                    problem.FStar_TypeChecker_Common.relation
                                    uu____21135 FStar_Pervasives_Native.None
                                    "lambda co-domain"))
              | (FStar_Syntax_Syntax.Tm_abs uu____21137,uu____21138) ->
                  let is_abs t =
                    match t.FStar_Syntax_Syntax.n with
                    | FStar_Syntax_Syntax.Tm_abs uu____21169 -> true
                    | uu____21189 -> false  in
                  let maybe_eta t =
                    if is_abs t
                    then FStar_Util.Inl t
                    else
                      (let t3 =
                         FStar_TypeChecker_Normalize.eta_expand wl.tcenv t
                          in
                       if is_abs t3
                       then FStar_Util.Inl t3
                       else FStar_Util.Inr t3)
                     in
                  let force_eta t =
                    if is_abs t
                    then t
                    else
                      (let uu____21249 =
                         env.FStar_TypeChecker_Env.type_of
                           (let uu___3000_21257 = env  in
                            {
                              FStar_TypeChecker_Env.solver =
                                (uu___3000_21257.FStar_TypeChecker_Env.solver);
                              FStar_TypeChecker_Env.range =
                                (uu___3000_21257.FStar_TypeChecker_Env.range);
                              FStar_TypeChecker_Env.curmodule =
                                (uu___3000_21257.FStar_TypeChecker_Env.curmodule);
                              FStar_TypeChecker_Env.gamma =
                                (uu___3000_21257.FStar_TypeChecker_Env.gamma);
                              FStar_TypeChecker_Env.gamma_sig =
                                (uu___3000_21257.FStar_TypeChecker_Env.gamma_sig);
                              FStar_TypeChecker_Env.gamma_cache =
                                (uu___3000_21257.FStar_TypeChecker_Env.gamma_cache);
                              FStar_TypeChecker_Env.modules =
                                (uu___3000_21257.FStar_TypeChecker_Env.modules);
                              FStar_TypeChecker_Env.expected_typ =
                                FStar_Pervasives_Native.None;
                              FStar_TypeChecker_Env.sigtab =
                                (uu___3000_21257.FStar_TypeChecker_Env.sigtab);
                              FStar_TypeChecker_Env.attrtab =
                                (uu___3000_21257.FStar_TypeChecker_Env.attrtab);
                              FStar_TypeChecker_Env.instantiate_imp =
                                (uu___3000_21257.FStar_TypeChecker_Env.instantiate_imp);
                              FStar_TypeChecker_Env.effects =
                                (uu___3000_21257.FStar_TypeChecker_Env.effects);
                              FStar_TypeChecker_Env.generalize =
                                (uu___3000_21257.FStar_TypeChecker_Env.generalize);
                              FStar_TypeChecker_Env.letrecs =
                                (uu___3000_21257.FStar_TypeChecker_Env.letrecs);
                              FStar_TypeChecker_Env.top_level =
                                (uu___3000_21257.FStar_TypeChecker_Env.top_level);
                              FStar_TypeChecker_Env.check_uvars =
                                (uu___3000_21257.FStar_TypeChecker_Env.check_uvars);
                              FStar_TypeChecker_Env.use_eq =
                                (uu___3000_21257.FStar_TypeChecker_Env.use_eq);
                              FStar_TypeChecker_Env.is_iface =
                                (uu___3000_21257.FStar_TypeChecker_Env.is_iface);
                              FStar_TypeChecker_Env.admit =
                                (uu___3000_21257.FStar_TypeChecker_Env.admit);
                              FStar_TypeChecker_Env.lax = true;
                              FStar_TypeChecker_Env.lax_universes =
                                (uu___3000_21257.FStar_TypeChecker_Env.lax_universes);
                              FStar_TypeChecker_Env.phase1 =
                                (uu___3000_21257.FStar_TypeChecker_Env.phase1);
                              FStar_TypeChecker_Env.failhard =
                                (uu___3000_21257.FStar_TypeChecker_Env.failhard);
                              FStar_TypeChecker_Env.nosynth =
                                (uu___3000_21257.FStar_TypeChecker_Env.nosynth);
                              FStar_TypeChecker_Env.uvar_subtyping =
                                (uu___3000_21257.FStar_TypeChecker_Env.uvar_subtyping);
                              FStar_TypeChecker_Env.tc_term =
                                (uu___3000_21257.FStar_TypeChecker_Env.tc_term);
                              FStar_TypeChecker_Env.type_of =
                                (uu___3000_21257.FStar_TypeChecker_Env.type_of);
                              FStar_TypeChecker_Env.universe_of =
                                (uu___3000_21257.FStar_TypeChecker_Env.universe_of);
                              FStar_TypeChecker_Env.check_type_of =
                                (uu___3000_21257.FStar_TypeChecker_Env.check_type_of);
                              FStar_TypeChecker_Env.use_bv_sorts = true;
                              FStar_TypeChecker_Env.qtbl_name_and_index =
                                (uu___3000_21257.FStar_TypeChecker_Env.qtbl_name_and_index);
                              FStar_TypeChecker_Env.normalized_eff_names =
                                (uu___3000_21257.FStar_TypeChecker_Env.normalized_eff_names);
                              FStar_TypeChecker_Env.fv_delta_depths =
                                (uu___3000_21257.FStar_TypeChecker_Env.fv_delta_depths);
                              FStar_TypeChecker_Env.proof_ns =
                                (uu___3000_21257.FStar_TypeChecker_Env.proof_ns);
                              FStar_TypeChecker_Env.synth_hook =
                                (uu___3000_21257.FStar_TypeChecker_Env.synth_hook);
                              FStar_TypeChecker_Env.splice =
                                (uu___3000_21257.FStar_TypeChecker_Env.splice);
                              FStar_TypeChecker_Env.mpreprocess =
                                (uu___3000_21257.FStar_TypeChecker_Env.mpreprocess);
                              FStar_TypeChecker_Env.postprocess =
                                (uu___3000_21257.FStar_TypeChecker_Env.postprocess);
                              FStar_TypeChecker_Env.is_native_tactic =
                                (uu___3000_21257.FStar_TypeChecker_Env.is_native_tactic);
                              FStar_TypeChecker_Env.identifier_info =
                                (uu___3000_21257.FStar_TypeChecker_Env.identifier_info);
                              FStar_TypeChecker_Env.tc_hooks =
                                (uu___3000_21257.FStar_TypeChecker_Env.tc_hooks);
                              FStar_TypeChecker_Env.dsenv =
                                (uu___3000_21257.FStar_TypeChecker_Env.dsenv);
                              FStar_TypeChecker_Env.nbe =
                                (uu___3000_21257.FStar_TypeChecker_Env.nbe);
                              FStar_TypeChecker_Env.strict_args_tab =
                                (uu___3000_21257.FStar_TypeChecker_Env.strict_args_tab);
                              FStar_TypeChecker_Env.erasable_types_tab =
                                (uu___3000_21257.FStar_TypeChecker_Env.erasable_types_tab)
                            }) t
                          in
                       match uu____21249 with
                       | (uu____21262,ty,uu____21264) ->
                           let ty1 =
                             let rec aux ty1 =
                               let ty2 =
                                 FStar_TypeChecker_Normalize.unfold_whnf env
                                   ty1
                                  in
                               let uu____21273 =
                                 let uu____21274 =
                                   FStar_Syntax_Subst.compress ty2  in
                                 uu____21274.FStar_Syntax_Syntax.n  in
                               match uu____21273 with
                               | FStar_Syntax_Syntax.Tm_refine uu____21277 ->
                                   let uu____21284 =
                                     FStar_Syntax_Util.unrefine ty2  in
                                   aux uu____21284
                               | uu____21285 -> ty2  in
                             aux ty  in
                           let r1 =
                             FStar_TypeChecker_Normalize.eta_expand_with_type
                               env t ty1
                              in
                           ((let uu____21288 =
                               FStar_All.pipe_left
                                 (FStar_TypeChecker_Env.debug wl.tcenv)
                                 (FStar_Options.Other "Rel")
                                in
                             if uu____21288
                             then
                               let uu____21293 =
                                 FStar_Syntax_Print.term_to_string t  in
                               let uu____21295 =
                                 let uu____21297 =
                                   FStar_TypeChecker_Normalize.unfold_whnf
                                     env ty1
                                    in
                                 FStar_Syntax_Print.term_to_string
                                   uu____21297
                                  in
                               let uu____21298 =
                                 FStar_Syntax_Print.term_to_string r1  in
                               FStar_Util.print3
                                 "force_eta of (%s) at type (%s) = %s\n"
                                 uu____21293 uu____21295 uu____21298
                             else ());
                            r1))
                     in
                  let uu____21303 =
                    let uu____21320 = maybe_eta t1  in
                    let uu____21327 = maybe_eta t2  in
                    (uu____21320, uu____21327)  in
                  (match uu____21303 with
                   | (FStar_Util.Inl t11,FStar_Util.Inl t21) ->
                       solve_t env
                         (let uu___3021_21369 = problem  in
                          {
                            FStar_TypeChecker_Common.pid =
                              (uu___3021_21369.FStar_TypeChecker_Common.pid);
                            FStar_TypeChecker_Common.lhs = t11;
                            FStar_TypeChecker_Common.relation =
                              (uu___3021_21369.FStar_TypeChecker_Common.relation);
                            FStar_TypeChecker_Common.rhs = t21;
                            FStar_TypeChecker_Common.element =
                              (uu___3021_21369.FStar_TypeChecker_Common.element);
                            FStar_TypeChecker_Common.logical_guard =
                              (uu___3021_21369.FStar_TypeChecker_Common.logical_guard);
                            FStar_TypeChecker_Common.logical_guard_uvar =
                              (uu___3021_21369.FStar_TypeChecker_Common.logical_guard_uvar);
                            FStar_TypeChecker_Common.reason =
                              (uu___3021_21369.FStar_TypeChecker_Common.reason);
                            FStar_TypeChecker_Common.loc =
                              (uu___3021_21369.FStar_TypeChecker_Common.loc);
                            FStar_TypeChecker_Common.rank =
                              (uu___3021_21369.FStar_TypeChecker_Common.rank)
                          }) wl
                   | (FStar_Util.Inl t_abs,FStar_Util.Inr not_abs) ->
                       let uu____21390 =
                         (is_flex not_abs) &&
                           ((p_rel orig) = FStar_TypeChecker_Common.EQ)
                          in
                       if uu____21390
                       then
                         let uu____21393 = destruct_flex_t not_abs wl  in
                         (match uu____21393 with
                          | (flex,wl1) ->
                              solve_t_flex_rigid_eq env orig wl1 flex t_abs)
                       else
                         (let t11 = force_eta t1  in
                          let t21 = force_eta t2  in
                          if (is_abs t11) && (is_abs t21)
                          then
                            solve_t env
                              (let uu___3038_21410 = problem  in
                               {
                                 FStar_TypeChecker_Common.pid =
                                   (uu___3038_21410.FStar_TypeChecker_Common.pid);
                                 FStar_TypeChecker_Common.lhs = t11;
                                 FStar_TypeChecker_Common.relation =
                                   (uu___3038_21410.FStar_TypeChecker_Common.relation);
                                 FStar_TypeChecker_Common.rhs = t21;
                                 FStar_TypeChecker_Common.element =
                                   (uu___3038_21410.FStar_TypeChecker_Common.element);
                                 FStar_TypeChecker_Common.logical_guard =
                                   (uu___3038_21410.FStar_TypeChecker_Common.logical_guard);
                                 FStar_TypeChecker_Common.logical_guard_uvar
                                   =
                                   (uu___3038_21410.FStar_TypeChecker_Common.logical_guard_uvar);
                                 FStar_TypeChecker_Common.reason =
                                   (uu___3038_21410.FStar_TypeChecker_Common.reason);
                                 FStar_TypeChecker_Common.loc =
                                   (uu___3038_21410.FStar_TypeChecker_Common.loc);
                                 FStar_TypeChecker_Common.rank =
                                   (uu___3038_21410.FStar_TypeChecker_Common.rank)
                               }) wl
                          else
                            (let uu____21413 =
                               FStar_Thunk.mkv
                                 "head tag mismatch: RHS is an abstraction"
                                in
                             giveup env uu____21413 orig))
                   | (FStar_Util.Inr not_abs,FStar_Util.Inl t_abs) ->
                       let uu____21436 =
                         (is_flex not_abs) &&
                           ((p_rel orig) = FStar_TypeChecker_Common.EQ)
                          in
                       if uu____21436
                       then
                         let uu____21439 = destruct_flex_t not_abs wl  in
                         (match uu____21439 with
                          | (flex,wl1) ->
                              solve_t_flex_rigid_eq env orig wl1 flex t_abs)
                       else
                         (let t11 = force_eta t1  in
                          let t21 = force_eta t2  in
                          if (is_abs t11) && (is_abs t21)
                          then
                            solve_t env
                              (let uu___3038_21456 = problem  in
                               {
                                 FStar_TypeChecker_Common.pid =
                                   (uu___3038_21456.FStar_TypeChecker_Common.pid);
                                 FStar_TypeChecker_Common.lhs = t11;
                                 FStar_TypeChecker_Common.relation =
                                   (uu___3038_21456.FStar_TypeChecker_Common.relation);
                                 FStar_TypeChecker_Common.rhs = t21;
                                 FStar_TypeChecker_Common.element =
                                   (uu___3038_21456.FStar_TypeChecker_Common.element);
                                 FStar_TypeChecker_Common.logical_guard =
                                   (uu___3038_21456.FStar_TypeChecker_Common.logical_guard);
                                 FStar_TypeChecker_Common.logical_guard_uvar
                                   =
                                   (uu___3038_21456.FStar_TypeChecker_Common.logical_guard_uvar);
                                 FStar_TypeChecker_Common.reason =
                                   (uu___3038_21456.FStar_TypeChecker_Common.reason);
                                 FStar_TypeChecker_Common.loc =
                                   (uu___3038_21456.FStar_TypeChecker_Common.loc);
                                 FStar_TypeChecker_Common.rank =
                                   (uu___3038_21456.FStar_TypeChecker_Common.rank)
                               }) wl
                          else
                            (let uu____21459 =
                               FStar_Thunk.mkv
                                 "head tag mismatch: RHS is an abstraction"
                                in
                             giveup env uu____21459 orig))
                   | uu____21462 ->
                       failwith
                         "Impossible: at least one side is an abstraction")
              | (uu____21480,FStar_Syntax_Syntax.Tm_abs uu____21481) ->
                  let is_abs t =
                    match t.FStar_Syntax_Syntax.n with
                    | FStar_Syntax_Syntax.Tm_abs uu____21512 -> true
                    | uu____21532 -> false  in
                  let maybe_eta t =
                    if is_abs t
                    then FStar_Util.Inl t
                    else
                      (let t3 =
                         FStar_TypeChecker_Normalize.eta_expand wl.tcenv t
                          in
                       if is_abs t3
                       then FStar_Util.Inl t3
                       else FStar_Util.Inr t3)
                     in
                  let force_eta t =
                    if is_abs t
                    then t
                    else
                      (let uu____21592 =
                         env.FStar_TypeChecker_Env.type_of
                           (let uu___3000_21600 = env  in
                            {
                              FStar_TypeChecker_Env.solver =
                                (uu___3000_21600.FStar_TypeChecker_Env.solver);
                              FStar_TypeChecker_Env.range =
                                (uu___3000_21600.FStar_TypeChecker_Env.range);
                              FStar_TypeChecker_Env.curmodule =
                                (uu___3000_21600.FStar_TypeChecker_Env.curmodule);
                              FStar_TypeChecker_Env.gamma =
                                (uu___3000_21600.FStar_TypeChecker_Env.gamma);
                              FStar_TypeChecker_Env.gamma_sig =
                                (uu___3000_21600.FStar_TypeChecker_Env.gamma_sig);
                              FStar_TypeChecker_Env.gamma_cache =
                                (uu___3000_21600.FStar_TypeChecker_Env.gamma_cache);
                              FStar_TypeChecker_Env.modules =
                                (uu___3000_21600.FStar_TypeChecker_Env.modules);
                              FStar_TypeChecker_Env.expected_typ =
                                FStar_Pervasives_Native.None;
                              FStar_TypeChecker_Env.sigtab =
                                (uu___3000_21600.FStar_TypeChecker_Env.sigtab);
                              FStar_TypeChecker_Env.attrtab =
                                (uu___3000_21600.FStar_TypeChecker_Env.attrtab);
                              FStar_TypeChecker_Env.instantiate_imp =
                                (uu___3000_21600.FStar_TypeChecker_Env.instantiate_imp);
                              FStar_TypeChecker_Env.effects =
                                (uu___3000_21600.FStar_TypeChecker_Env.effects);
                              FStar_TypeChecker_Env.generalize =
                                (uu___3000_21600.FStar_TypeChecker_Env.generalize);
                              FStar_TypeChecker_Env.letrecs =
                                (uu___3000_21600.FStar_TypeChecker_Env.letrecs);
                              FStar_TypeChecker_Env.top_level =
                                (uu___3000_21600.FStar_TypeChecker_Env.top_level);
                              FStar_TypeChecker_Env.check_uvars =
                                (uu___3000_21600.FStar_TypeChecker_Env.check_uvars);
                              FStar_TypeChecker_Env.use_eq =
                                (uu___3000_21600.FStar_TypeChecker_Env.use_eq);
                              FStar_TypeChecker_Env.is_iface =
                                (uu___3000_21600.FStar_TypeChecker_Env.is_iface);
                              FStar_TypeChecker_Env.admit =
                                (uu___3000_21600.FStar_TypeChecker_Env.admit);
                              FStar_TypeChecker_Env.lax = true;
                              FStar_TypeChecker_Env.lax_universes =
                                (uu___3000_21600.FStar_TypeChecker_Env.lax_universes);
                              FStar_TypeChecker_Env.phase1 =
                                (uu___3000_21600.FStar_TypeChecker_Env.phase1);
                              FStar_TypeChecker_Env.failhard =
                                (uu___3000_21600.FStar_TypeChecker_Env.failhard);
                              FStar_TypeChecker_Env.nosynth =
                                (uu___3000_21600.FStar_TypeChecker_Env.nosynth);
                              FStar_TypeChecker_Env.uvar_subtyping =
                                (uu___3000_21600.FStar_TypeChecker_Env.uvar_subtyping);
                              FStar_TypeChecker_Env.tc_term =
                                (uu___3000_21600.FStar_TypeChecker_Env.tc_term);
                              FStar_TypeChecker_Env.type_of =
                                (uu___3000_21600.FStar_TypeChecker_Env.type_of);
                              FStar_TypeChecker_Env.universe_of =
                                (uu___3000_21600.FStar_TypeChecker_Env.universe_of);
                              FStar_TypeChecker_Env.check_type_of =
                                (uu___3000_21600.FStar_TypeChecker_Env.check_type_of);
                              FStar_TypeChecker_Env.use_bv_sorts = true;
                              FStar_TypeChecker_Env.qtbl_name_and_index =
                                (uu___3000_21600.FStar_TypeChecker_Env.qtbl_name_and_index);
                              FStar_TypeChecker_Env.normalized_eff_names =
                                (uu___3000_21600.FStar_TypeChecker_Env.normalized_eff_names);
                              FStar_TypeChecker_Env.fv_delta_depths =
                                (uu___3000_21600.FStar_TypeChecker_Env.fv_delta_depths);
                              FStar_TypeChecker_Env.proof_ns =
                                (uu___3000_21600.FStar_TypeChecker_Env.proof_ns);
                              FStar_TypeChecker_Env.synth_hook =
                                (uu___3000_21600.FStar_TypeChecker_Env.synth_hook);
                              FStar_TypeChecker_Env.splice =
                                (uu___3000_21600.FStar_TypeChecker_Env.splice);
                              FStar_TypeChecker_Env.mpreprocess =
                                (uu___3000_21600.FStar_TypeChecker_Env.mpreprocess);
                              FStar_TypeChecker_Env.postprocess =
                                (uu___3000_21600.FStar_TypeChecker_Env.postprocess);
                              FStar_TypeChecker_Env.is_native_tactic =
                                (uu___3000_21600.FStar_TypeChecker_Env.is_native_tactic);
                              FStar_TypeChecker_Env.identifier_info =
                                (uu___3000_21600.FStar_TypeChecker_Env.identifier_info);
                              FStar_TypeChecker_Env.tc_hooks =
                                (uu___3000_21600.FStar_TypeChecker_Env.tc_hooks);
                              FStar_TypeChecker_Env.dsenv =
                                (uu___3000_21600.FStar_TypeChecker_Env.dsenv);
                              FStar_TypeChecker_Env.nbe =
                                (uu___3000_21600.FStar_TypeChecker_Env.nbe);
                              FStar_TypeChecker_Env.strict_args_tab =
                                (uu___3000_21600.FStar_TypeChecker_Env.strict_args_tab);
                              FStar_TypeChecker_Env.erasable_types_tab =
                                (uu___3000_21600.FStar_TypeChecker_Env.erasable_types_tab)
                            }) t
                          in
                       match uu____21592 with
                       | (uu____21605,ty,uu____21607) ->
                           let ty1 =
                             let rec aux ty1 =
                               let ty2 =
                                 FStar_TypeChecker_Normalize.unfold_whnf env
                                   ty1
                                  in
                               let uu____21616 =
                                 let uu____21617 =
                                   FStar_Syntax_Subst.compress ty2  in
                                 uu____21617.FStar_Syntax_Syntax.n  in
                               match uu____21616 with
                               | FStar_Syntax_Syntax.Tm_refine uu____21620 ->
                                   let uu____21627 =
                                     FStar_Syntax_Util.unrefine ty2  in
                                   aux uu____21627
                               | uu____21628 -> ty2  in
                             aux ty  in
                           let r1 =
                             FStar_TypeChecker_Normalize.eta_expand_with_type
                               env t ty1
                              in
                           ((let uu____21631 =
                               FStar_All.pipe_left
                                 (FStar_TypeChecker_Env.debug wl.tcenv)
                                 (FStar_Options.Other "Rel")
                                in
                             if uu____21631
                             then
                               let uu____21636 =
                                 FStar_Syntax_Print.term_to_string t  in
                               let uu____21638 =
                                 let uu____21640 =
                                   FStar_TypeChecker_Normalize.unfold_whnf
                                     env ty1
                                    in
                                 FStar_Syntax_Print.term_to_string
                                   uu____21640
                                  in
                               let uu____21641 =
                                 FStar_Syntax_Print.term_to_string r1  in
                               FStar_Util.print3
                                 "force_eta of (%s) at type (%s) = %s\n"
                                 uu____21636 uu____21638 uu____21641
                             else ());
                            r1))
                     in
                  let uu____21646 =
                    let uu____21663 = maybe_eta t1  in
                    let uu____21670 = maybe_eta t2  in
                    (uu____21663, uu____21670)  in
                  (match uu____21646 with
                   | (FStar_Util.Inl t11,FStar_Util.Inl t21) ->
                       solve_t env
                         (let uu___3021_21712 = problem  in
                          {
                            FStar_TypeChecker_Common.pid =
                              (uu___3021_21712.FStar_TypeChecker_Common.pid);
                            FStar_TypeChecker_Common.lhs = t11;
                            FStar_TypeChecker_Common.relation =
                              (uu___3021_21712.FStar_TypeChecker_Common.relation);
                            FStar_TypeChecker_Common.rhs = t21;
                            FStar_TypeChecker_Common.element =
                              (uu___3021_21712.FStar_TypeChecker_Common.element);
                            FStar_TypeChecker_Common.logical_guard =
                              (uu___3021_21712.FStar_TypeChecker_Common.logical_guard);
                            FStar_TypeChecker_Common.logical_guard_uvar =
                              (uu___3021_21712.FStar_TypeChecker_Common.logical_guard_uvar);
                            FStar_TypeChecker_Common.reason =
                              (uu___3021_21712.FStar_TypeChecker_Common.reason);
                            FStar_TypeChecker_Common.loc =
                              (uu___3021_21712.FStar_TypeChecker_Common.loc);
                            FStar_TypeChecker_Common.rank =
                              (uu___3021_21712.FStar_TypeChecker_Common.rank)
                          }) wl
                   | (FStar_Util.Inl t_abs,FStar_Util.Inr not_abs) ->
                       let uu____21733 =
                         (is_flex not_abs) &&
                           ((p_rel orig) = FStar_TypeChecker_Common.EQ)
                          in
                       if uu____21733
                       then
                         let uu____21736 = destruct_flex_t not_abs wl  in
                         (match uu____21736 with
                          | (flex,wl1) ->
                              solve_t_flex_rigid_eq env orig wl1 flex t_abs)
                       else
                         (let t11 = force_eta t1  in
                          let t21 = force_eta t2  in
                          if (is_abs t11) && (is_abs t21)
                          then
                            solve_t env
                              (let uu___3038_21753 = problem  in
                               {
                                 FStar_TypeChecker_Common.pid =
                                   (uu___3038_21753.FStar_TypeChecker_Common.pid);
                                 FStar_TypeChecker_Common.lhs = t11;
                                 FStar_TypeChecker_Common.relation =
                                   (uu___3038_21753.FStar_TypeChecker_Common.relation);
                                 FStar_TypeChecker_Common.rhs = t21;
                                 FStar_TypeChecker_Common.element =
                                   (uu___3038_21753.FStar_TypeChecker_Common.element);
                                 FStar_TypeChecker_Common.logical_guard =
                                   (uu___3038_21753.FStar_TypeChecker_Common.logical_guard);
                                 FStar_TypeChecker_Common.logical_guard_uvar
                                   =
                                   (uu___3038_21753.FStar_TypeChecker_Common.logical_guard_uvar);
                                 FStar_TypeChecker_Common.reason =
                                   (uu___3038_21753.FStar_TypeChecker_Common.reason);
                                 FStar_TypeChecker_Common.loc =
                                   (uu___3038_21753.FStar_TypeChecker_Common.loc);
                                 FStar_TypeChecker_Common.rank =
                                   (uu___3038_21753.FStar_TypeChecker_Common.rank)
                               }) wl
                          else
                            (let uu____21756 =
                               FStar_Thunk.mkv
                                 "head tag mismatch: RHS is an abstraction"
                                in
                             giveup env uu____21756 orig))
                   | (FStar_Util.Inr not_abs,FStar_Util.Inl t_abs) ->
                       let uu____21779 =
                         (is_flex not_abs) &&
                           ((p_rel orig) = FStar_TypeChecker_Common.EQ)
                          in
                       if uu____21779
                       then
                         let uu____21782 = destruct_flex_t not_abs wl  in
                         (match uu____21782 with
                          | (flex,wl1) ->
                              solve_t_flex_rigid_eq env orig wl1 flex t_abs)
                       else
                         (let t11 = force_eta t1  in
                          let t21 = force_eta t2  in
                          if (is_abs t11) && (is_abs t21)
                          then
                            solve_t env
                              (let uu___3038_21799 = problem  in
                               {
                                 FStar_TypeChecker_Common.pid =
                                   (uu___3038_21799.FStar_TypeChecker_Common.pid);
                                 FStar_TypeChecker_Common.lhs = t11;
                                 FStar_TypeChecker_Common.relation =
                                   (uu___3038_21799.FStar_TypeChecker_Common.relation);
                                 FStar_TypeChecker_Common.rhs = t21;
                                 FStar_TypeChecker_Common.element =
                                   (uu___3038_21799.FStar_TypeChecker_Common.element);
                                 FStar_TypeChecker_Common.logical_guard =
                                   (uu___3038_21799.FStar_TypeChecker_Common.logical_guard);
                                 FStar_TypeChecker_Common.logical_guard_uvar
                                   =
                                   (uu___3038_21799.FStar_TypeChecker_Common.logical_guard_uvar);
                                 FStar_TypeChecker_Common.reason =
                                   (uu___3038_21799.FStar_TypeChecker_Common.reason);
                                 FStar_TypeChecker_Common.loc =
                                   (uu___3038_21799.FStar_TypeChecker_Common.loc);
                                 FStar_TypeChecker_Common.rank =
                                   (uu___3038_21799.FStar_TypeChecker_Common.rank)
                               }) wl
                          else
                            (let uu____21802 =
                               FStar_Thunk.mkv
                                 "head tag mismatch: RHS is an abstraction"
                                in
                             giveup env uu____21802 orig))
                   | uu____21805 ->
                       failwith
                         "Impossible: at least one side is an abstraction")
              | (FStar_Syntax_Syntax.Tm_refine
                 (x1,phi1),FStar_Syntax_Syntax.Tm_refine (x2,phi2)) ->
                  let uu____21835 =
                    let uu____21840 =
                      head_matches_delta env wl x1.FStar_Syntax_Syntax.sort
                        x2.FStar_Syntax_Syntax.sort
                       in
                    match uu____21840 with
                    | (FullMatch ,FStar_Pervasives_Native.Some (t11,t21)) ->
                        ((let uu___3061_21868 = x1  in
                          {
                            FStar_Syntax_Syntax.ppname =
                              (uu___3061_21868.FStar_Syntax_Syntax.ppname);
                            FStar_Syntax_Syntax.index =
                              (uu___3061_21868.FStar_Syntax_Syntax.index);
                            FStar_Syntax_Syntax.sort = t11
                          }),
                          (let uu___3063_21870 = x2  in
                           {
                             FStar_Syntax_Syntax.ppname =
                               (uu___3063_21870.FStar_Syntax_Syntax.ppname);
                             FStar_Syntax_Syntax.index =
                               (uu___3063_21870.FStar_Syntax_Syntax.index);
                             FStar_Syntax_Syntax.sort = t21
                           }))
                    | (HeadMatch uu____21871,FStar_Pervasives_Native.Some
                       (t11,t21)) ->
                        ((let uu___3061_21886 = x1  in
                          {
                            FStar_Syntax_Syntax.ppname =
                              (uu___3061_21886.FStar_Syntax_Syntax.ppname);
                            FStar_Syntax_Syntax.index =
                              (uu___3061_21886.FStar_Syntax_Syntax.index);
                            FStar_Syntax_Syntax.sort = t11
                          }),
                          (let uu___3063_21888 = x2  in
                           {
                             FStar_Syntax_Syntax.ppname =
                               (uu___3063_21888.FStar_Syntax_Syntax.ppname);
                             FStar_Syntax_Syntax.index =
                               (uu___3063_21888.FStar_Syntax_Syntax.index);
                             FStar_Syntax_Syntax.sort = t21
                           }))
                    | uu____21889 -> (x1, x2)  in
                  (match uu____21835 with
                   | (x11,x21) ->
                       let t11 = FStar_Syntax_Util.refine x11 phi1  in
                       let t21 = FStar_Syntax_Util.refine x21 phi2  in
                       let uu____21908 = as_refinement false env t11  in
                       (match uu____21908 with
                        | (x12,phi11) ->
                            let uu____21916 = as_refinement false env t21  in
                            (match uu____21916 with
                             | (x22,phi21) ->
                                 ((let uu____21925 =
                                     FStar_TypeChecker_Env.debug env
                                       (FStar_Options.Other "Rel")
                                      in
                                   if uu____21925
                                   then
                                     ((let uu____21930 =
                                         FStar_Syntax_Print.bv_to_string x12
                                          in
                                       let uu____21932 =
                                         FStar_Syntax_Print.term_to_string
                                           x12.FStar_Syntax_Syntax.sort
                                          in
                                       let uu____21934 =
                                         FStar_Syntax_Print.term_to_string
                                           phi11
                                          in
                                       FStar_Util.print3
                                         "ref1 = (%s):(%s){%s}\n" uu____21930
                                         uu____21932 uu____21934);
                                      (let uu____21937 =
                                         FStar_Syntax_Print.bv_to_string x22
                                          in
                                       let uu____21939 =
                                         FStar_Syntax_Print.term_to_string
                                           x22.FStar_Syntax_Syntax.sort
                                          in
                                       let uu____21941 =
                                         FStar_Syntax_Print.term_to_string
                                           phi21
                                          in
                                       FStar_Util.print3
                                         "ref2 = (%s):(%s){%s}\n" uu____21937
                                         uu____21939 uu____21941))
                                   else ());
                                  (let uu____21946 =
                                     mk_t_problem wl [] orig
                                       x12.FStar_Syntax_Syntax.sort
                                       problem.FStar_TypeChecker_Common.relation
                                       x22.FStar_Syntax_Syntax.sort
                                       problem.FStar_TypeChecker_Common.element
                                       "refinement base type"
                                      in
                                   match uu____21946 with
                                   | (base_prob,wl1) ->
                                       let x13 =
                                         FStar_Syntax_Syntax.freshen_bv x12
                                          in
                                       let subst1 =
                                         [FStar_Syntax_Syntax.DB
                                            (Prims.int_zero, x13)]
                                          in
                                       let phi12 =
                                         FStar_Syntax_Subst.subst subst1
                                           phi11
                                          in
                                       let phi22 =
                                         FStar_Syntax_Subst.subst subst1
                                           phi21
                                          in
                                       let env1 =
                                         FStar_TypeChecker_Env.push_bv env
                                           x13
                                          in
                                       let mk_imp1 imp phi13 phi23 =
                                         let uu____22017 = imp phi13 phi23
                                            in
                                         FStar_All.pipe_right uu____22017
                                           (guard_on_element wl1 problem x13)
                                          in
                                       let fallback uu____22029 =
                                         let impl =
                                           if
                                             problem.FStar_TypeChecker_Common.relation
                                               = FStar_TypeChecker_Common.EQ
                                           then
                                             mk_imp1 FStar_Syntax_Util.mk_iff
                                               phi12 phi22
                                           else
                                             mk_imp1 FStar_Syntax_Util.mk_imp
                                               phi12 phi22
                                            in
                                         let guard =
                                           FStar_Syntax_Util.mk_conj
                                             (p_guard base_prob) impl
                                            in
                                         (let uu____22042 =
                                            let uu____22045 = p_scope orig
                                               in
                                            FStar_List.map
                                              FStar_Pervasives_Native.fst
                                              uu____22045
                                             in
                                          FStar_TypeChecker_Env.def_check_closed_in
                                            (p_loc orig) "ref.1" uu____22042
                                            (p_guard base_prob));
                                         (let uu____22064 =
                                            let uu____22067 = p_scope orig
                                               in
                                            FStar_List.map
                                              FStar_Pervasives_Native.fst
                                              uu____22067
                                             in
                                          FStar_TypeChecker_Env.def_check_closed_in
                                            (p_loc orig) "ref.2" uu____22064
                                            impl);
                                         (let wl2 =
                                            solve_prob orig
                                              (FStar_Pervasives_Native.Some
                                                 guard) [] wl1
                                             in
                                          let uu____22086 =
                                            attempt [base_prob] wl2  in
                                          solve env1 uu____22086)
                                          in
                                       let has_uvars =
                                         (let uu____22091 =
                                            let uu____22093 =
                                              FStar_Syntax_Free.uvars phi12
                                               in
                                            FStar_Util.set_is_empty
                                              uu____22093
                                             in
                                          Prims.op_Negation uu____22091) ||
                                           (let uu____22097 =
                                              let uu____22099 =
                                                FStar_Syntax_Free.uvars phi22
                                                 in
                                              FStar_Util.set_is_empty
                                                uu____22099
                                               in
                                            Prims.op_Negation uu____22097)
                                          in
                                       if
                                         (problem.FStar_TypeChecker_Common.relation
                                            = FStar_TypeChecker_Common.EQ)
                                           ||
                                           ((Prims.op_Negation
                                               env1.FStar_TypeChecker_Env.uvar_subtyping)
                                              && has_uvars)
                                       then
                                         let uu____22103 =
                                           let uu____22108 =
                                             let uu____22117 =
                                               FStar_Syntax_Syntax.mk_binder
                                                 x13
                                                in
                                             [uu____22117]  in
                                           mk_t_problem wl1 uu____22108 orig
                                             phi12
                                             FStar_TypeChecker_Common.EQ
                                             phi22
                                             FStar_Pervasives_Native.None
                                             "refinement formula"
                                            in
                                         (match uu____22103 with
                                          | (ref_prob,wl2) ->
                                              let uu____22139 =
                                                solve env1
                                                  (let uu___3105_22141 = wl2
                                                      in
                                                   {
                                                     attempting = [ref_prob];
                                                     wl_deferred = [];
                                                     ctr =
                                                       (uu___3105_22141.ctr);
                                                     defer_ok = false;
                                                     smt_ok =
                                                       (uu___3105_22141.smt_ok);
                                                     umax_heuristic_ok =
                                                       (uu___3105_22141.umax_heuristic_ok);
                                                     tcenv =
                                                       (uu___3105_22141.tcenv);
                                                     wl_implicits =
                                                       (uu___3105_22141.wl_implicits)
                                                   })
                                                 in
                                              (match uu____22139 with
                                               | Failed (prob,msg) ->
                                                   if
                                                     ((Prims.op_Negation
                                                         env1.FStar_TypeChecker_Env.uvar_subtyping)
                                                        && has_uvars)
                                                       ||
                                                       (Prims.op_Negation
                                                          wl2.smt_ok)
                                                   then giveup env1 msg prob
                                                   else fallback ()
                                               | Success uu____22155 ->
                                                   let guard =
                                                     let uu____22163 =
                                                       FStar_All.pipe_right
                                                         (p_guard ref_prob)
                                                         (guard_on_element
                                                            wl2 problem x13)
                                                        in
                                                     FStar_Syntax_Util.mk_conj
                                                       (p_guard base_prob)
                                                       uu____22163
                                                      in
                                                   let wl3 =
                                                     solve_prob orig
                                                       (FStar_Pervasives_Native.Some
                                                          guard) [] wl2
                                                      in
                                                   let wl4 =
                                                     let uu___3116_22172 =
                                                       wl3  in
                                                     {
                                                       attempting =
                                                         (uu___3116_22172.attempting);
                                                       wl_deferred =
                                                         (uu___3116_22172.wl_deferred);
                                                       ctr =
                                                         (wl3.ctr +
                                                            Prims.int_one);
                                                       defer_ok =
                                                         (uu___3116_22172.defer_ok);
                                                       smt_ok =
                                                         (uu___3116_22172.smt_ok);
                                                       umax_heuristic_ok =
                                                         (uu___3116_22172.umax_heuristic_ok);
                                                       tcenv =
                                                         (uu___3116_22172.tcenv);
                                                       wl_implicits =
                                                         (uu___3116_22172.wl_implicits)
                                                     }  in
                                                   let uu____22174 =
                                                     attempt [base_prob] wl4
                                                      in
                                                   solve env1 uu____22174))
                                       else fallback ())))))
              | (FStar_Syntax_Syntax.Tm_uvar
                 uu____22177,FStar_Syntax_Syntax.Tm_uvar uu____22178) ->
                  let uu____22203 = destruct_flex_t t1 wl  in
                  (match uu____22203 with
                   | (f1,wl1) ->
                       let uu____22210 = destruct_flex_t t2 wl1  in
                       (match uu____22210 with
                        | (f2,wl2) -> solve_t_flex_flex env orig wl2 f1 f2))
              | (FStar_Syntax_Syntax.Tm_app
                 ({
                    FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                      uu____22217;
                    FStar_Syntax_Syntax.pos = uu____22218;
                    FStar_Syntax_Syntax.vars = uu____22219;_},uu____22220),FStar_Syntax_Syntax.Tm_uvar
                 uu____22221) ->
                  let uu____22270 = destruct_flex_t t1 wl  in
                  (match uu____22270 with
                   | (f1,wl1) ->
                       let uu____22277 = destruct_flex_t t2 wl1  in
                       (match uu____22277 with
                        | (f2,wl2) -> solve_t_flex_flex env orig wl2 f1 f2))
              | (FStar_Syntax_Syntax.Tm_uvar
                 uu____22284,FStar_Syntax_Syntax.Tm_app
                 ({
                    FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                      uu____22285;
                    FStar_Syntax_Syntax.pos = uu____22286;
                    FStar_Syntax_Syntax.vars = uu____22287;_},uu____22288))
                  ->
                  let uu____22337 = destruct_flex_t t1 wl  in
                  (match uu____22337 with
                   | (f1,wl1) ->
                       let uu____22344 = destruct_flex_t t2 wl1  in
                       (match uu____22344 with
                        | (f2,wl2) -> solve_t_flex_flex env orig wl2 f1 f2))
              | (FStar_Syntax_Syntax.Tm_app
                 ({
                    FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                      uu____22351;
                    FStar_Syntax_Syntax.pos = uu____22352;
                    FStar_Syntax_Syntax.vars = uu____22353;_},uu____22354),FStar_Syntax_Syntax.Tm_app
                 ({
                    FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                      uu____22355;
                    FStar_Syntax_Syntax.pos = uu____22356;
                    FStar_Syntax_Syntax.vars = uu____22357;_},uu____22358))
                  ->
                  let uu____22431 = destruct_flex_t t1 wl  in
                  (match uu____22431 with
                   | (f1,wl1) ->
                       let uu____22438 = destruct_flex_t t2 wl1  in
                       (match uu____22438 with
                        | (f2,wl2) -> solve_t_flex_flex env orig wl2 f1 f2))
              | (FStar_Syntax_Syntax.Tm_uvar uu____22445,uu____22446) when
                  problem.FStar_TypeChecker_Common.relation =
                    FStar_TypeChecker_Common.EQ
                  ->
                  let uu____22459 = destruct_flex_t t1 wl  in
                  (match uu____22459 with
                   | (f1,wl1) -> solve_t_flex_rigid_eq env orig wl1 f1 t2)
              | (FStar_Syntax_Syntax.Tm_app
                 ({
                    FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                      uu____22466;
                    FStar_Syntax_Syntax.pos = uu____22467;
                    FStar_Syntax_Syntax.vars = uu____22468;_},uu____22469),uu____22470)
                  when
                  problem.FStar_TypeChecker_Common.relation =
                    FStar_TypeChecker_Common.EQ
                  ->
                  let uu____22507 = destruct_flex_t t1 wl  in
                  (match uu____22507 with
                   | (f1,wl1) -> solve_t_flex_rigid_eq env orig wl1 f1 t2)
              | (uu____22514,FStar_Syntax_Syntax.Tm_uvar uu____22515) when
                  problem.FStar_TypeChecker_Common.relation =
                    FStar_TypeChecker_Common.EQ
                  -> solve_t env (invert problem) wl
              | (uu____22528,FStar_Syntax_Syntax.Tm_app
                 ({
                    FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                      uu____22529;
                    FStar_Syntax_Syntax.pos = uu____22530;
                    FStar_Syntax_Syntax.vars = uu____22531;_},uu____22532))
                  when
                  problem.FStar_TypeChecker_Common.relation =
                    FStar_TypeChecker_Common.EQ
                  -> solve_t env (invert problem) wl
              | (FStar_Syntax_Syntax.Tm_uvar
                 uu____22569,FStar_Syntax_Syntax.Tm_arrow uu____22570) ->
                  solve_t' env
                    (let uu___3216_22598 = problem  in
                     {
                       FStar_TypeChecker_Common.pid =
                         (uu___3216_22598.FStar_TypeChecker_Common.pid);
                       FStar_TypeChecker_Common.lhs =
                         (uu___3216_22598.FStar_TypeChecker_Common.lhs);
                       FStar_TypeChecker_Common.relation =
                         FStar_TypeChecker_Common.EQ;
                       FStar_TypeChecker_Common.rhs =
                         (uu___3216_22598.FStar_TypeChecker_Common.rhs);
                       FStar_TypeChecker_Common.element =
                         (uu___3216_22598.FStar_TypeChecker_Common.element);
                       FStar_TypeChecker_Common.logical_guard =
                         (uu___3216_22598.FStar_TypeChecker_Common.logical_guard);
                       FStar_TypeChecker_Common.logical_guard_uvar =
                         (uu___3216_22598.FStar_TypeChecker_Common.logical_guard_uvar);
                       FStar_TypeChecker_Common.reason =
                         (uu___3216_22598.FStar_TypeChecker_Common.reason);
                       FStar_TypeChecker_Common.loc =
                         (uu___3216_22598.FStar_TypeChecker_Common.loc);
                       FStar_TypeChecker_Common.rank =
                         (uu___3216_22598.FStar_TypeChecker_Common.rank)
                     }) wl
              | (FStar_Syntax_Syntax.Tm_app
                 ({
                    FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                      uu____22599;
                    FStar_Syntax_Syntax.pos = uu____22600;
                    FStar_Syntax_Syntax.vars = uu____22601;_},uu____22602),FStar_Syntax_Syntax.Tm_arrow
                 uu____22603) ->
                  solve_t' env
                    (let uu___3216_22655 = problem  in
                     {
                       FStar_TypeChecker_Common.pid =
                         (uu___3216_22655.FStar_TypeChecker_Common.pid);
                       FStar_TypeChecker_Common.lhs =
                         (uu___3216_22655.FStar_TypeChecker_Common.lhs);
                       FStar_TypeChecker_Common.relation =
                         FStar_TypeChecker_Common.EQ;
                       FStar_TypeChecker_Common.rhs =
                         (uu___3216_22655.FStar_TypeChecker_Common.rhs);
                       FStar_TypeChecker_Common.element =
                         (uu___3216_22655.FStar_TypeChecker_Common.element);
                       FStar_TypeChecker_Common.logical_guard =
                         (uu___3216_22655.FStar_TypeChecker_Common.logical_guard);
                       FStar_TypeChecker_Common.logical_guard_uvar =
                         (uu___3216_22655.FStar_TypeChecker_Common.logical_guard_uvar);
                       FStar_TypeChecker_Common.reason =
                         (uu___3216_22655.FStar_TypeChecker_Common.reason);
                       FStar_TypeChecker_Common.loc =
                         (uu___3216_22655.FStar_TypeChecker_Common.loc);
                       FStar_TypeChecker_Common.rank =
                         (uu___3216_22655.FStar_TypeChecker_Common.rank)
                     }) wl
              | (uu____22656,FStar_Syntax_Syntax.Tm_uvar uu____22657) ->
                  let uu____22670 =
                    attempt [FStar_TypeChecker_Common.TProb problem] wl  in
                  solve env uu____22670
              | (uu____22671,FStar_Syntax_Syntax.Tm_app
                 ({
                    FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                      uu____22672;
                    FStar_Syntax_Syntax.pos = uu____22673;
                    FStar_Syntax_Syntax.vars = uu____22674;_},uu____22675))
                  ->
                  let uu____22712 =
                    attempt [FStar_TypeChecker_Common.TProb problem] wl  in
                  solve env uu____22712
              | (FStar_Syntax_Syntax.Tm_uvar uu____22713,uu____22714) ->
                  let uu____22727 =
                    attempt [FStar_TypeChecker_Common.TProb problem] wl  in
                  solve env uu____22727
              | (FStar_Syntax_Syntax.Tm_app
                 ({
                    FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                      uu____22728;
                    FStar_Syntax_Syntax.pos = uu____22729;
                    FStar_Syntax_Syntax.vars = uu____22730;_},uu____22731),uu____22732)
                  ->
                  let uu____22769 =
                    attempt [FStar_TypeChecker_Common.TProb problem] wl  in
                  solve env uu____22769
              | (FStar_Syntax_Syntax.Tm_refine uu____22770,uu____22771) ->
                  let t21 =
                    let uu____22779 = base_and_refinement env t2  in
                    FStar_All.pipe_left force_refinement uu____22779  in
                  solve_t env
                    (let uu___3251_22805 = problem  in
                     {
                       FStar_TypeChecker_Common.pid =
                         (uu___3251_22805.FStar_TypeChecker_Common.pid);
                       FStar_TypeChecker_Common.lhs =
                         (uu___3251_22805.FStar_TypeChecker_Common.lhs);
                       FStar_TypeChecker_Common.relation =
                         (uu___3251_22805.FStar_TypeChecker_Common.relation);
                       FStar_TypeChecker_Common.rhs = t21;
                       FStar_TypeChecker_Common.element =
                         (uu___3251_22805.FStar_TypeChecker_Common.element);
                       FStar_TypeChecker_Common.logical_guard =
                         (uu___3251_22805.FStar_TypeChecker_Common.logical_guard);
                       FStar_TypeChecker_Common.logical_guard_uvar =
                         (uu___3251_22805.FStar_TypeChecker_Common.logical_guard_uvar);
                       FStar_TypeChecker_Common.reason =
                         (uu___3251_22805.FStar_TypeChecker_Common.reason);
                       FStar_TypeChecker_Common.loc =
                         (uu___3251_22805.FStar_TypeChecker_Common.loc);
                       FStar_TypeChecker_Common.rank =
                         (uu___3251_22805.FStar_TypeChecker_Common.rank)
                     }) wl
              | (uu____22806,FStar_Syntax_Syntax.Tm_refine uu____22807) ->
                  let t11 =
                    let uu____22815 = base_and_refinement env t1  in
                    FStar_All.pipe_left force_refinement uu____22815  in
                  solve_t env
                    (let uu___3258_22841 = problem  in
                     {
                       FStar_TypeChecker_Common.pid =
                         (uu___3258_22841.FStar_TypeChecker_Common.pid);
                       FStar_TypeChecker_Common.lhs = t11;
                       FStar_TypeChecker_Common.relation =
                         (uu___3258_22841.FStar_TypeChecker_Common.relation);
                       FStar_TypeChecker_Common.rhs =
                         (uu___3258_22841.FStar_TypeChecker_Common.rhs);
                       FStar_TypeChecker_Common.element =
                         (uu___3258_22841.FStar_TypeChecker_Common.element);
                       FStar_TypeChecker_Common.logical_guard =
                         (uu___3258_22841.FStar_TypeChecker_Common.logical_guard);
                       FStar_TypeChecker_Common.logical_guard_uvar =
                         (uu___3258_22841.FStar_TypeChecker_Common.logical_guard_uvar);
                       FStar_TypeChecker_Common.reason =
                         (uu___3258_22841.FStar_TypeChecker_Common.reason);
                       FStar_TypeChecker_Common.loc =
                         (uu___3258_22841.FStar_TypeChecker_Common.loc);
                       FStar_TypeChecker_Common.rank =
                         (uu___3258_22841.FStar_TypeChecker_Common.rank)
                     }) wl
              | (FStar_Syntax_Syntax.Tm_match
                 (s1,brs1),FStar_Syntax_Syntax.Tm_match (s2,brs2)) ->
                  let by_smt uu____22923 =
                    let uu____22924 = guard_of_prob env wl problem t1 t2  in
                    match uu____22924 with
                    | (guard,wl1) ->
                        let uu____22931 =
                          solve_prob orig
                            (FStar_Pervasives_Native.Some guard) [] wl1
                           in
                        solve env uu____22931
                     in
                  let rec solve_branches wl1 brs11 brs21 =
                    match (brs11, brs21) with
                    | (br1::rs1,br2::rs2) ->
                        let uu____23150 = br1  in
                        (match uu____23150 with
                         | (p1,w1,uu____23179) ->
                             let uu____23196 = br2  in
                             (match uu____23196 with
                              | (p2,w2,uu____23219) ->
                                  let uu____23224 =
                                    let uu____23226 =
                                      FStar_Syntax_Syntax.eq_pat p1 p2  in
                                    Prims.op_Negation uu____23226  in
                                  if uu____23224
                                  then FStar_Pervasives_Native.None
                                  else
                                    (let uu____23253 =
                                       FStar_Syntax_Subst.open_branch' br1
                                        in
                                     match uu____23253 with
                                     | ((p11,w11,e1),s) ->
                                         let uu____23290 = br2  in
                                         (match uu____23290 with
                                          | (p21,w21,e2) ->
                                              let w22 =
                                                FStar_Util.map_opt w21
                                                  (FStar_Syntax_Subst.subst s)
                                                 in
                                              let e21 =
                                                FStar_Syntax_Subst.subst s e2
                                                 in
                                              let scope =
                                                let uu____23323 =
                                                  FStar_Syntax_Syntax.pat_bvs
                                                    p11
                                                   in
                                                FStar_All.pipe_left
                                                  (FStar_List.map
                                                     FStar_Syntax_Syntax.mk_binder)
                                                  uu____23323
                                                 in
                                              let uu____23328 =
                                                match (w11, w22) with
                                                | (FStar_Pervasives_Native.Some
                                                   uu____23359,FStar_Pervasives_Native.None
                                                   ) ->
                                                    FStar_Pervasives_Native.None
                                                | (FStar_Pervasives_Native.None
                                                   ,FStar_Pervasives_Native.Some
                                                   uu____23380) ->
                                                    FStar_Pervasives_Native.None
                                                | (FStar_Pervasives_Native.None
                                                   ,FStar_Pervasives_Native.None
                                                   ) ->
                                                    FStar_Pervasives_Native.Some
                                                      ([], wl1)
                                                | (FStar_Pervasives_Native.Some
                                                   w12,FStar_Pervasives_Native.Some
                                                   w23) ->
                                                    let uu____23439 =
                                                      mk_t_problem wl1 scope
                                                        orig w12
                                                        FStar_TypeChecker_Common.EQ
                                                        w23
                                                        FStar_Pervasives_Native.None
                                                        "when clause"
                                                       in
                                                    (match uu____23439 with
                                                     | (p,wl2) ->
                                                         FStar_Pervasives_Native.Some
                                                           ([(scope, p)],
                                                             wl2))
                                                 in
                                              FStar_Util.bind_opt uu____23328
                                                (fun uu____23511  ->
                                                   match uu____23511 with
                                                   | (wprobs,wl2) ->
                                                       let uu____23548 =
                                                         mk_t_problem wl2
                                                           scope orig e1
                                                           FStar_TypeChecker_Common.EQ
                                                           e21
                                                           FStar_Pervasives_Native.None
                                                           "branch body"
                                                          in
                                                       (match uu____23548
                                                        with
                                                        | (prob,wl3) ->
                                                            ((let uu____23569
                                                                =
                                                                FStar_All.pipe_left
                                                                  (FStar_TypeChecker_Env.debug
                                                                    wl3.tcenv)
                                                                  (FStar_Options.Other
                                                                    "Rel")
                                                                 in
                                                              if uu____23569
                                                              then
                                                                let uu____23574
                                                                  =
                                                                  prob_to_string
                                                                    env prob
                                                                   in
                                                                let uu____23576
                                                                  =
                                                                  FStar_Syntax_Print.binders_to_string
                                                                    ", "
                                                                    scope
                                                                   in
                                                                FStar_Util.print2
                                                                  "Created problem for branches %s with scope %s\n"
                                                                  uu____23574
                                                                  uu____23576
                                                              else ());
                                                             (let uu____23582
                                                                =
                                                                solve_branches
                                                                  wl3 rs1 rs2
                                                                 in
                                                              FStar_Util.bind_opt
                                                                uu____23582
                                                                (fun
                                                                   uu____23618
                                                                    ->
                                                                   match uu____23618
                                                                   with
                                                                   | 
                                                                   (r1,wl4)
                                                                    ->
                                                                    FStar_Pervasives_Native.Some
                                                                    (((scope,
                                                                    prob) ::
                                                                    (FStar_List.append
                                                                    wprobs r1)),
                                                                    wl4))))))))))
                    | ([],[]) -> FStar_Pervasives_Native.Some ([], wl1)
                    | uu____23747 -> FStar_Pervasives_Native.None  in
                  let uu____23788 = solve_branches wl brs1 brs2  in
                  (match uu____23788 with
                   | FStar_Pervasives_Native.None  ->
                       if wl.smt_ok
                       then by_smt ()
                       else
                         (let uu____23814 =
                            FStar_Thunk.mkv "Tm_match branches don't match"
                             in
                          giveup env uu____23814 orig)
                   | FStar_Pervasives_Native.Some (sub_probs,wl1) ->
                       let uu____23841 =
                         mk_t_problem wl1 [] orig s1
                           FStar_TypeChecker_Common.EQ s2
                           FStar_Pervasives_Native.None "match scrutinee"
                          in
                       (match uu____23841 with
                        | (sc_prob,wl2) ->
                            let sub_probs1 = ([], sc_prob) :: sub_probs  in
                            let formula =
                              let uu____23875 =
                                FStar_List.map
                                  (fun uu____23887  ->
                                     match uu____23887 with
                                     | (scope,p) ->
                                         FStar_TypeChecker_Env.close_forall
                                           wl2.tcenv scope (p_guard p))
                                  sub_probs1
                                 in
                              FStar_Syntax_Util.mk_conj_l uu____23875  in
                            let tx =
                              FStar_Syntax_Unionfind.new_transaction ()  in
                            let wl3 =
                              solve_prob orig
                                (FStar_Pervasives_Native.Some formula) [] wl2
                               in
                            let uu____23896 =
                              let uu____23897 =
                                let uu____23898 =
                                  FStar_List.map FStar_Pervasives_Native.snd
                                    sub_probs1
                                   in
                                attempt uu____23898
                                  (let uu___3357_23906 = wl3  in
                                   {
                                     attempting =
                                       (uu___3357_23906.attempting);
                                     wl_deferred =
                                       (uu___3357_23906.wl_deferred);
                                     ctr = (uu___3357_23906.ctr);
                                     defer_ok = (uu___3357_23906.defer_ok);
                                     smt_ok = false;
                                     umax_heuristic_ok =
                                       (uu___3357_23906.umax_heuristic_ok);
                                     tcenv = (uu___3357_23906.tcenv);
                                     wl_implicits =
                                       (uu___3357_23906.wl_implicits)
                                   })
                                 in
                              solve env uu____23897  in
                            (match uu____23896 with
                             | Success (ds,imp) ->
                                 (FStar_Syntax_Unionfind.commit tx;
                                  Success (ds, imp))
                             | Failed uu____23911 ->
                                 (FStar_Syntax_Unionfind.rollback tx;
                                  by_smt ()))))
              | (FStar_Syntax_Syntax.Tm_match uu____23917,uu____23918) ->
                  let head1 =
                    let uu____23942 = FStar_Syntax_Util.head_and_args t1  in
                    FStar_All.pipe_right uu____23942
                      FStar_Pervasives_Native.fst
                     in
                  let head2 =
                    let uu____23988 = FStar_Syntax_Util.head_and_args t2  in
                    FStar_All.pipe_right uu____23988
                      FStar_Pervasives_Native.fst
                     in
                  ((let uu____24034 =
                      FStar_TypeChecker_Env.debug env
                        (FStar_Options.Other "Rel")
                       in
                    if uu____24034
                    then
                      let uu____24038 =
                        FStar_Util.string_of_int
                          problem.FStar_TypeChecker_Common.pid
                         in
                      let uu____24040 =
                        FStar_Syntax_Print.term_to_string head1  in
                      let uu____24042 =
                        FStar_Syntax_Print.term_to_string head2  in
                      FStar_Util.print3
                        ">> (%s)\n>>> head1 = %s\n>>> head2 = %s\n"
                        uu____24038 uu____24040 uu____24042
                    else ());
                   (let no_free_uvars t =
                      (let uu____24056 = FStar_Syntax_Free.uvars t  in
                       FStar_Util.set_is_empty uu____24056) &&
                        (let uu____24060 = FStar_Syntax_Free.univs t  in
                         FStar_Util.set_is_empty uu____24060)
                       in
                    let equal t11 t21 =
                      let t12 =
                        FStar_TypeChecker_Normalize.normalize
                          [FStar_TypeChecker_Env.UnfoldUntil
                             FStar_Syntax_Syntax.delta_constant;
                          FStar_TypeChecker_Env.Primops;
                          FStar_TypeChecker_Env.Beta;
                          FStar_TypeChecker_Env.Eager_unfolding;
                          FStar_TypeChecker_Env.Iota] env t11
                         in
                      let t22 =
                        FStar_TypeChecker_Normalize.normalize
                          [FStar_TypeChecker_Env.UnfoldUntil
                             FStar_Syntax_Syntax.delta_constant;
                          FStar_TypeChecker_Env.Primops;
                          FStar_TypeChecker_Env.Beta;
                          FStar_TypeChecker_Env.Eager_unfolding;
                          FStar_TypeChecker_Env.Iota] env t21
                         in
                      let uu____24077 = FStar_Syntax_Util.eq_tm t12 t22  in
                      uu____24077 = FStar_Syntax_Util.Equal  in
                    let uu____24078 =
                      ((((FStar_TypeChecker_Env.is_interpreted env head1) ||
                           (FStar_TypeChecker_Env.is_interpreted env head2))
                          &&
                          (problem.FStar_TypeChecker_Common.relation =
                             FStar_TypeChecker_Common.EQ))
                         && (no_free_uvars t1))
                        && (no_free_uvars t2)
                       in
                    if uu____24078
                    then
                      (if Prims.op_Negation wl.smt_ok
                       then
                         let uu____24082 = equal t1 t2  in
                         (if uu____24082
                          then
                            let uu____24085 =
                              solve_prob orig FStar_Pervasives_Native.None []
                                wl
                               in
                            solve env uu____24085
                          else
                            rigid_rigid_delta env problem wl head1 head2 t1
                              t2)
                       else
                         (let uu____24090 =
                            let uu____24097 = equal t1 t2  in
                            if uu____24097
                            then (FStar_Pervasives_Native.None, wl)
                            else
                              (let uu____24110 = mk_eq2 wl env orig t1 t2  in
                               match uu____24110 with
                               | (g,wl1) ->
                                   ((FStar_Pervasives_Native.Some g), wl1))
                             in
                          match uu____24090 with
                          | (guard,wl1) ->
                              let uu____24131 = solve_prob orig guard [] wl1
                                 in
                              solve env uu____24131))
                    else rigid_rigid_delta env problem wl head1 head2 t1 t2))
              | (FStar_Syntax_Syntax.Tm_uinst uu____24134,uu____24135) ->
                  let head1 =
                    let uu____24143 = FStar_Syntax_Util.head_and_args t1  in
                    FStar_All.pipe_right uu____24143
                      FStar_Pervasives_Native.fst
                     in
                  let head2 =
                    let uu____24189 = FStar_Syntax_Util.head_and_args t2  in
                    FStar_All.pipe_right uu____24189
                      FStar_Pervasives_Native.fst
                     in
                  ((let uu____24235 =
                      FStar_TypeChecker_Env.debug env
                        (FStar_Options.Other "Rel")
                       in
                    if uu____24235
                    then
                      let uu____24239 =
                        FStar_Util.string_of_int
                          problem.FStar_TypeChecker_Common.pid
                         in
                      let uu____24241 =
                        FStar_Syntax_Print.term_to_string head1  in
                      let uu____24243 =
                        FStar_Syntax_Print.term_to_string head2  in
                      FStar_Util.print3
                        ">> (%s)\n>>> head1 = %s\n>>> head2 = %s\n"
                        uu____24239 uu____24241 uu____24243
                    else ());
                   (let no_free_uvars t =
                      (let uu____24257 = FStar_Syntax_Free.uvars t  in
                       FStar_Util.set_is_empty uu____24257) &&
                        (let uu____24261 = FStar_Syntax_Free.univs t  in
                         FStar_Util.set_is_empty uu____24261)
                       in
                    let equal t11 t21 =
                      let t12 =
                        FStar_TypeChecker_Normalize.normalize
                          [FStar_TypeChecker_Env.UnfoldUntil
                             FStar_Syntax_Syntax.delta_constant;
                          FStar_TypeChecker_Env.Primops;
                          FStar_TypeChecker_Env.Beta;
                          FStar_TypeChecker_Env.Eager_unfolding;
                          FStar_TypeChecker_Env.Iota] env t11
                         in
                      let t22 =
                        FStar_TypeChecker_Normalize.normalize
                          [FStar_TypeChecker_Env.UnfoldUntil
                             FStar_Syntax_Syntax.delta_constant;
                          FStar_TypeChecker_Env.Primops;
                          FStar_TypeChecker_Env.Beta;
                          FStar_TypeChecker_Env.Eager_unfolding;
                          FStar_TypeChecker_Env.Iota] env t21
                         in
                      let uu____24278 = FStar_Syntax_Util.eq_tm t12 t22  in
                      uu____24278 = FStar_Syntax_Util.Equal  in
                    let uu____24279 =
                      ((((FStar_TypeChecker_Env.is_interpreted env head1) ||
                           (FStar_TypeChecker_Env.is_interpreted env head2))
                          &&
                          (problem.FStar_TypeChecker_Common.relation =
                             FStar_TypeChecker_Common.EQ))
                         && (no_free_uvars t1))
                        && (no_free_uvars t2)
                       in
                    if uu____24279
                    then
                      (if Prims.op_Negation wl.smt_ok
                       then
                         let uu____24283 = equal t1 t2  in
                         (if uu____24283
                          then
                            let uu____24286 =
                              solve_prob orig FStar_Pervasives_Native.None []
                                wl
                               in
                            solve env uu____24286
                          else
                            rigid_rigid_delta env problem wl head1 head2 t1
                              t2)
                       else
                         (let uu____24291 =
                            let uu____24298 = equal t1 t2  in
                            if uu____24298
                            then (FStar_Pervasives_Native.None, wl)
                            else
                              (let uu____24311 = mk_eq2 wl env orig t1 t2  in
                               match uu____24311 with
                               | (g,wl1) ->
                                   ((FStar_Pervasives_Native.Some g), wl1))
                             in
                          match uu____24291 with
                          | (guard,wl1) ->
                              let uu____24332 = solve_prob orig guard [] wl1
                                 in
                              solve env uu____24332))
                    else rigid_rigid_delta env problem wl head1 head2 t1 t2))
              | (FStar_Syntax_Syntax.Tm_name uu____24335,uu____24336) ->
                  let head1 =
                    let uu____24338 = FStar_Syntax_Util.head_and_args t1  in
                    FStar_All.pipe_right uu____24338
                      FStar_Pervasives_Native.fst
                     in
                  let head2 =
                    let uu____24384 = FStar_Syntax_Util.head_and_args t2  in
                    FStar_All.pipe_right uu____24384
                      FStar_Pervasives_Native.fst
                     in
                  ((let uu____24430 =
                      FStar_TypeChecker_Env.debug env
                        (FStar_Options.Other "Rel")
                       in
                    if uu____24430
                    then
                      let uu____24434 =
                        FStar_Util.string_of_int
                          problem.FStar_TypeChecker_Common.pid
                         in
                      let uu____24436 =
                        FStar_Syntax_Print.term_to_string head1  in
                      let uu____24438 =
                        FStar_Syntax_Print.term_to_string head2  in
                      FStar_Util.print3
                        ">> (%s)\n>>> head1 = %s\n>>> head2 = %s\n"
                        uu____24434 uu____24436 uu____24438
                    else ());
                   (let no_free_uvars t =
                      (let uu____24452 = FStar_Syntax_Free.uvars t  in
                       FStar_Util.set_is_empty uu____24452) &&
                        (let uu____24456 = FStar_Syntax_Free.univs t  in
                         FStar_Util.set_is_empty uu____24456)
                       in
                    let equal t11 t21 =
                      let t12 =
                        FStar_TypeChecker_Normalize.normalize
                          [FStar_TypeChecker_Env.UnfoldUntil
                             FStar_Syntax_Syntax.delta_constant;
                          FStar_TypeChecker_Env.Primops;
                          FStar_TypeChecker_Env.Beta;
                          FStar_TypeChecker_Env.Eager_unfolding;
                          FStar_TypeChecker_Env.Iota] env t11
                         in
                      let t22 =
                        FStar_TypeChecker_Normalize.normalize
                          [FStar_TypeChecker_Env.UnfoldUntil
                             FStar_Syntax_Syntax.delta_constant;
                          FStar_TypeChecker_Env.Primops;
                          FStar_TypeChecker_Env.Beta;
                          FStar_TypeChecker_Env.Eager_unfolding;
                          FStar_TypeChecker_Env.Iota] env t21
                         in
                      let uu____24473 = FStar_Syntax_Util.eq_tm t12 t22  in
                      uu____24473 = FStar_Syntax_Util.Equal  in
                    let uu____24474 =
                      ((((FStar_TypeChecker_Env.is_interpreted env head1) ||
                           (FStar_TypeChecker_Env.is_interpreted env head2))
                          &&
                          (problem.FStar_TypeChecker_Common.relation =
                             FStar_TypeChecker_Common.EQ))
                         && (no_free_uvars t1))
                        && (no_free_uvars t2)
                       in
                    if uu____24474
                    then
                      (if Prims.op_Negation wl.smt_ok
                       then
                         let uu____24478 = equal t1 t2  in
                         (if uu____24478
                          then
                            let uu____24481 =
                              solve_prob orig FStar_Pervasives_Native.None []
                                wl
                               in
                            solve env uu____24481
                          else
                            rigid_rigid_delta env problem wl head1 head2 t1
                              t2)
                       else
                         (let uu____24486 =
                            let uu____24493 = equal t1 t2  in
                            if uu____24493
                            then (FStar_Pervasives_Native.None, wl)
                            else
                              (let uu____24506 = mk_eq2 wl env orig t1 t2  in
                               match uu____24506 with
                               | (g,wl1) ->
                                   ((FStar_Pervasives_Native.Some g), wl1))
                             in
                          match uu____24486 with
                          | (guard,wl1) ->
                              let uu____24527 = solve_prob orig guard [] wl1
                                 in
                              solve env uu____24527))
                    else rigid_rigid_delta env problem wl head1 head2 t1 t2))
              | (FStar_Syntax_Syntax.Tm_constant uu____24530,uu____24531) ->
                  let head1 =
                    let uu____24533 = FStar_Syntax_Util.head_and_args t1  in
                    FStar_All.pipe_right uu____24533
                      FStar_Pervasives_Native.fst
                     in
                  let head2 =
                    let uu____24579 = FStar_Syntax_Util.head_and_args t2  in
                    FStar_All.pipe_right uu____24579
                      FStar_Pervasives_Native.fst
                     in
                  ((let uu____24625 =
                      FStar_TypeChecker_Env.debug env
                        (FStar_Options.Other "Rel")
                       in
                    if uu____24625
                    then
                      let uu____24629 =
                        FStar_Util.string_of_int
                          problem.FStar_TypeChecker_Common.pid
                         in
                      let uu____24631 =
                        FStar_Syntax_Print.term_to_string head1  in
                      let uu____24633 =
                        FStar_Syntax_Print.term_to_string head2  in
                      FStar_Util.print3
                        ">> (%s)\n>>> head1 = %s\n>>> head2 = %s\n"
                        uu____24629 uu____24631 uu____24633
                    else ());
                   (let no_free_uvars t =
                      (let uu____24647 = FStar_Syntax_Free.uvars t  in
                       FStar_Util.set_is_empty uu____24647) &&
                        (let uu____24651 = FStar_Syntax_Free.univs t  in
                         FStar_Util.set_is_empty uu____24651)
                       in
                    let equal t11 t21 =
                      let t12 =
                        FStar_TypeChecker_Normalize.normalize
                          [FStar_TypeChecker_Env.UnfoldUntil
                             FStar_Syntax_Syntax.delta_constant;
                          FStar_TypeChecker_Env.Primops;
                          FStar_TypeChecker_Env.Beta;
                          FStar_TypeChecker_Env.Eager_unfolding;
                          FStar_TypeChecker_Env.Iota] env t11
                         in
                      let t22 =
                        FStar_TypeChecker_Normalize.normalize
                          [FStar_TypeChecker_Env.UnfoldUntil
                             FStar_Syntax_Syntax.delta_constant;
                          FStar_TypeChecker_Env.Primops;
                          FStar_TypeChecker_Env.Beta;
                          FStar_TypeChecker_Env.Eager_unfolding;
                          FStar_TypeChecker_Env.Iota] env t21
                         in
                      let uu____24668 = FStar_Syntax_Util.eq_tm t12 t22  in
                      uu____24668 = FStar_Syntax_Util.Equal  in
                    let uu____24669 =
                      ((((FStar_TypeChecker_Env.is_interpreted env head1) ||
                           (FStar_TypeChecker_Env.is_interpreted env head2))
                          &&
                          (problem.FStar_TypeChecker_Common.relation =
                             FStar_TypeChecker_Common.EQ))
                         && (no_free_uvars t1))
                        && (no_free_uvars t2)
                       in
                    if uu____24669
                    then
                      (if Prims.op_Negation wl.smt_ok
                       then
                         let uu____24673 = equal t1 t2  in
                         (if uu____24673
                          then
                            let uu____24676 =
                              solve_prob orig FStar_Pervasives_Native.None []
                                wl
                               in
                            solve env uu____24676
                          else
                            rigid_rigid_delta env problem wl head1 head2 t1
                              t2)
                       else
                         (let uu____24681 =
                            let uu____24688 = equal t1 t2  in
                            if uu____24688
                            then (FStar_Pervasives_Native.None, wl)
                            else
                              (let uu____24701 = mk_eq2 wl env orig t1 t2  in
                               match uu____24701 with
                               | (g,wl1) ->
                                   ((FStar_Pervasives_Native.Some g), wl1))
                             in
                          match uu____24681 with
                          | (guard,wl1) ->
                              let uu____24722 = solve_prob orig guard [] wl1
                                 in
                              solve env uu____24722))
                    else rigid_rigid_delta env problem wl head1 head2 t1 t2))
              | (FStar_Syntax_Syntax.Tm_fvar uu____24725,uu____24726) ->
                  let head1 =
                    let uu____24728 = FStar_Syntax_Util.head_and_args t1  in
                    FStar_All.pipe_right uu____24728
                      FStar_Pervasives_Native.fst
                     in
                  let head2 =
                    let uu____24768 = FStar_Syntax_Util.head_and_args t2  in
                    FStar_All.pipe_right uu____24768
                      FStar_Pervasives_Native.fst
                     in
                  ((let uu____24808 =
                      FStar_TypeChecker_Env.debug env
                        (FStar_Options.Other "Rel")
                       in
                    if uu____24808
                    then
                      let uu____24812 =
                        FStar_Util.string_of_int
                          problem.FStar_TypeChecker_Common.pid
                         in
                      let uu____24814 =
                        FStar_Syntax_Print.term_to_string head1  in
                      let uu____24816 =
                        FStar_Syntax_Print.term_to_string head2  in
                      FStar_Util.print3
                        ">> (%s)\n>>> head1 = %s\n>>> head2 = %s\n"
                        uu____24812 uu____24814 uu____24816
                    else ());
                   (let no_free_uvars t =
                      (let uu____24830 = FStar_Syntax_Free.uvars t  in
                       FStar_Util.set_is_empty uu____24830) &&
                        (let uu____24834 = FStar_Syntax_Free.univs t  in
                         FStar_Util.set_is_empty uu____24834)
                       in
                    let equal t11 t21 =
                      let t12 =
                        FStar_TypeChecker_Normalize.normalize
                          [FStar_TypeChecker_Env.UnfoldUntil
                             FStar_Syntax_Syntax.delta_constant;
                          FStar_TypeChecker_Env.Primops;
                          FStar_TypeChecker_Env.Beta;
                          FStar_TypeChecker_Env.Eager_unfolding;
                          FStar_TypeChecker_Env.Iota] env t11
                         in
                      let t22 =
                        FStar_TypeChecker_Normalize.normalize
                          [FStar_TypeChecker_Env.UnfoldUntil
                             FStar_Syntax_Syntax.delta_constant;
                          FStar_TypeChecker_Env.Primops;
                          FStar_TypeChecker_Env.Beta;
                          FStar_TypeChecker_Env.Eager_unfolding;
                          FStar_TypeChecker_Env.Iota] env t21
                         in
                      let uu____24851 = FStar_Syntax_Util.eq_tm t12 t22  in
                      uu____24851 = FStar_Syntax_Util.Equal  in
                    let uu____24852 =
                      ((((FStar_TypeChecker_Env.is_interpreted env head1) ||
                           (FStar_TypeChecker_Env.is_interpreted env head2))
                          &&
                          (problem.FStar_TypeChecker_Common.relation =
                             FStar_TypeChecker_Common.EQ))
                         && (no_free_uvars t1))
                        && (no_free_uvars t2)
                       in
                    if uu____24852
                    then
                      (if Prims.op_Negation wl.smt_ok
                       then
                         let uu____24856 = equal t1 t2  in
                         (if uu____24856
                          then
                            let uu____24859 =
                              solve_prob orig FStar_Pervasives_Native.None []
                                wl
                               in
                            solve env uu____24859
                          else
                            rigid_rigid_delta env problem wl head1 head2 t1
                              t2)
                       else
                         (let uu____24864 =
                            let uu____24871 = equal t1 t2  in
                            if uu____24871
                            then (FStar_Pervasives_Native.None, wl)
                            else
                              (let uu____24884 = mk_eq2 wl env orig t1 t2  in
                               match uu____24884 with
                               | (g,wl1) ->
                                   ((FStar_Pervasives_Native.Some g), wl1))
                             in
                          match uu____24864 with
                          | (guard,wl1) ->
                              let uu____24905 = solve_prob orig guard [] wl1
                                 in
                              solve env uu____24905))
                    else rigid_rigid_delta env problem wl head1 head2 t1 t2))
              | (FStar_Syntax_Syntax.Tm_app uu____24908,uu____24909) ->
                  let head1 =
                    let uu____24927 = FStar_Syntax_Util.head_and_args t1  in
                    FStar_All.pipe_right uu____24927
                      FStar_Pervasives_Native.fst
                     in
                  let head2 =
                    let uu____24967 = FStar_Syntax_Util.head_and_args t2  in
                    FStar_All.pipe_right uu____24967
                      FStar_Pervasives_Native.fst
                     in
                  ((let uu____25007 =
                      FStar_TypeChecker_Env.debug env
                        (FStar_Options.Other "Rel")
                       in
                    if uu____25007
                    then
                      let uu____25011 =
                        FStar_Util.string_of_int
                          problem.FStar_TypeChecker_Common.pid
                         in
                      let uu____25013 =
                        FStar_Syntax_Print.term_to_string head1  in
                      let uu____25015 =
                        FStar_Syntax_Print.term_to_string head2  in
                      FStar_Util.print3
                        ">> (%s)\n>>> head1 = %s\n>>> head2 = %s\n"
                        uu____25011 uu____25013 uu____25015
                    else ());
                   (let no_free_uvars t =
                      (let uu____25029 = FStar_Syntax_Free.uvars t  in
                       FStar_Util.set_is_empty uu____25029) &&
                        (let uu____25033 = FStar_Syntax_Free.univs t  in
                         FStar_Util.set_is_empty uu____25033)
                       in
                    let equal t11 t21 =
                      let t12 =
                        FStar_TypeChecker_Normalize.normalize
                          [FStar_TypeChecker_Env.UnfoldUntil
                             FStar_Syntax_Syntax.delta_constant;
                          FStar_TypeChecker_Env.Primops;
                          FStar_TypeChecker_Env.Beta;
                          FStar_TypeChecker_Env.Eager_unfolding;
                          FStar_TypeChecker_Env.Iota] env t11
                         in
                      let t22 =
                        FStar_TypeChecker_Normalize.normalize
                          [FStar_TypeChecker_Env.UnfoldUntil
                             FStar_Syntax_Syntax.delta_constant;
                          FStar_TypeChecker_Env.Primops;
                          FStar_TypeChecker_Env.Beta;
                          FStar_TypeChecker_Env.Eager_unfolding;
                          FStar_TypeChecker_Env.Iota] env t21
                         in
                      let uu____25050 = FStar_Syntax_Util.eq_tm t12 t22  in
                      uu____25050 = FStar_Syntax_Util.Equal  in
                    let uu____25051 =
                      ((((FStar_TypeChecker_Env.is_interpreted env head1) ||
                           (FStar_TypeChecker_Env.is_interpreted env head2))
                          &&
                          (problem.FStar_TypeChecker_Common.relation =
                             FStar_TypeChecker_Common.EQ))
                         && (no_free_uvars t1))
                        && (no_free_uvars t2)
                       in
                    if uu____25051
                    then
                      (if Prims.op_Negation wl.smt_ok
                       then
                         let uu____25055 = equal t1 t2  in
                         (if uu____25055
                          then
                            let uu____25058 =
                              solve_prob orig FStar_Pervasives_Native.None []
                                wl
                               in
                            solve env uu____25058
                          else
                            rigid_rigid_delta env problem wl head1 head2 t1
                              t2)
                       else
                         (let uu____25063 =
                            let uu____25070 = equal t1 t2  in
                            if uu____25070
                            then (FStar_Pervasives_Native.None, wl)
                            else
                              (let uu____25083 = mk_eq2 wl env orig t1 t2  in
                               match uu____25083 with
                               | (g,wl1) ->
                                   ((FStar_Pervasives_Native.Some g), wl1))
                             in
                          match uu____25063 with
                          | (guard,wl1) ->
                              let uu____25104 = solve_prob orig guard [] wl1
                                 in
                              solve env uu____25104))
                    else rigid_rigid_delta env problem wl head1 head2 t1 t2))
              | (uu____25107,FStar_Syntax_Syntax.Tm_match uu____25108) ->
                  let head1 =
                    let uu____25132 = FStar_Syntax_Util.head_and_args t1  in
                    FStar_All.pipe_right uu____25132
                      FStar_Pervasives_Native.fst
                     in
                  let head2 =
                    let uu____25172 = FStar_Syntax_Util.head_and_args t2  in
                    FStar_All.pipe_right uu____25172
                      FStar_Pervasives_Native.fst
                     in
                  ((let uu____25212 =
                      FStar_TypeChecker_Env.debug env
                        (FStar_Options.Other "Rel")
                       in
                    if uu____25212
                    then
                      let uu____25216 =
                        FStar_Util.string_of_int
                          problem.FStar_TypeChecker_Common.pid
                         in
                      let uu____25218 =
                        FStar_Syntax_Print.term_to_string head1  in
                      let uu____25220 =
                        FStar_Syntax_Print.term_to_string head2  in
                      FStar_Util.print3
                        ">> (%s)\n>>> head1 = %s\n>>> head2 = %s\n"
                        uu____25216 uu____25218 uu____25220
                    else ());
                   (let no_free_uvars t =
                      (let uu____25234 = FStar_Syntax_Free.uvars t  in
                       FStar_Util.set_is_empty uu____25234) &&
                        (let uu____25238 = FStar_Syntax_Free.univs t  in
                         FStar_Util.set_is_empty uu____25238)
                       in
                    let equal t11 t21 =
                      let t12 =
                        FStar_TypeChecker_Normalize.normalize
                          [FStar_TypeChecker_Env.UnfoldUntil
                             FStar_Syntax_Syntax.delta_constant;
                          FStar_TypeChecker_Env.Primops;
                          FStar_TypeChecker_Env.Beta;
                          FStar_TypeChecker_Env.Eager_unfolding;
                          FStar_TypeChecker_Env.Iota] env t11
                         in
                      let t22 =
                        FStar_TypeChecker_Normalize.normalize
                          [FStar_TypeChecker_Env.UnfoldUntil
                             FStar_Syntax_Syntax.delta_constant;
                          FStar_TypeChecker_Env.Primops;
                          FStar_TypeChecker_Env.Beta;
                          FStar_TypeChecker_Env.Eager_unfolding;
                          FStar_TypeChecker_Env.Iota] env t21
                         in
                      let uu____25255 = FStar_Syntax_Util.eq_tm t12 t22  in
                      uu____25255 = FStar_Syntax_Util.Equal  in
                    let uu____25256 =
                      ((((FStar_TypeChecker_Env.is_interpreted env head1) ||
                           (FStar_TypeChecker_Env.is_interpreted env head2))
                          &&
                          (problem.FStar_TypeChecker_Common.relation =
                             FStar_TypeChecker_Common.EQ))
                         && (no_free_uvars t1))
                        && (no_free_uvars t2)
                       in
                    if uu____25256
                    then
                      (if Prims.op_Negation wl.smt_ok
                       then
                         let uu____25260 = equal t1 t2  in
                         (if uu____25260
                          then
                            let uu____25263 =
                              solve_prob orig FStar_Pervasives_Native.None []
                                wl
                               in
                            solve env uu____25263
                          else
                            rigid_rigid_delta env problem wl head1 head2 t1
                              t2)
                       else
                         (let uu____25268 =
                            let uu____25275 = equal t1 t2  in
                            if uu____25275
                            then (FStar_Pervasives_Native.None, wl)
                            else
                              (let uu____25288 = mk_eq2 wl env orig t1 t2  in
                               match uu____25288 with
                               | (g,wl1) ->
                                   ((FStar_Pervasives_Native.Some g), wl1))
                             in
                          match uu____25268 with
                          | (guard,wl1) ->
                              let uu____25309 = solve_prob orig guard [] wl1
                                 in
                              solve env uu____25309))
                    else rigid_rigid_delta env problem wl head1 head2 t1 t2))
              | (uu____25312,FStar_Syntax_Syntax.Tm_uinst uu____25313) ->
                  let head1 =
                    let uu____25321 = FStar_Syntax_Util.head_and_args t1  in
                    FStar_All.pipe_right uu____25321
                      FStar_Pervasives_Native.fst
                     in
                  let head2 =
                    let uu____25361 = FStar_Syntax_Util.head_and_args t2  in
                    FStar_All.pipe_right uu____25361
                      FStar_Pervasives_Native.fst
                     in
                  ((let uu____25401 =
                      FStar_TypeChecker_Env.debug env
                        (FStar_Options.Other "Rel")
                       in
                    if uu____25401
                    then
                      let uu____25405 =
                        FStar_Util.string_of_int
                          problem.FStar_TypeChecker_Common.pid
                         in
                      let uu____25407 =
                        FStar_Syntax_Print.term_to_string head1  in
                      let uu____25409 =
                        FStar_Syntax_Print.term_to_string head2  in
                      FStar_Util.print3
                        ">> (%s)\n>>> head1 = %s\n>>> head2 = %s\n"
                        uu____25405 uu____25407 uu____25409
                    else ());
                   (let no_free_uvars t =
                      (let uu____25423 = FStar_Syntax_Free.uvars t  in
                       FStar_Util.set_is_empty uu____25423) &&
                        (let uu____25427 = FStar_Syntax_Free.univs t  in
                         FStar_Util.set_is_empty uu____25427)
                       in
                    let equal t11 t21 =
                      let t12 =
                        FStar_TypeChecker_Normalize.normalize
                          [FStar_TypeChecker_Env.UnfoldUntil
                             FStar_Syntax_Syntax.delta_constant;
                          FStar_TypeChecker_Env.Primops;
                          FStar_TypeChecker_Env.Beta;
                          FStar_TypeChecker_Env.Eager_unfolding;
                          FStar_TypeChecker_Env.Iota] env t11
                         in
                      let t22 =
                        FStar_TypeChecker_Normalize.normalize
                          [FStar_TypeChecker_Env.UnfoldUntil
                             FStar_Syntax_Syntax.delta_constant;
                          FStar_TypeChecker_Env.Primops;
                          FStar_TypeChecker_Env.Beta;
                          FStar_TypeChecker_Env.Eager_unfolding;
                          FStar_TypeChecker_Env.Iota] env t21
                         in
                      let uu____25444 = FStar_Syntax_Util.eq_tm t12 t22  in
                      uu____25444 = FStar_Syntax_Util.Equal  in
                    let uu____25445 =
                      ((((FStar_TypeChecker_Env.is_interpreted env head1) ||
                           (FStar_TypeChecker_Env.is_interpreted env head2))
                          &&
                          (problem.FStar_TypeChecker_Common.relation =
                             FStar_TypeChecker_Common.EQ))
                         && (no_free_uvars t1))
                        && (no_free_uvars t2)
                       in
                    if uu____25445
                    then
                      (if Prims.op_Negation wl.smt_ok
                       then
                         let uu____25449 = equal t1 t2  in
                         (if uu____25449
                          then
                            let uu____25452 =
                              solve_prob orig FStar_Pervasives_Native.None []
                                wl
                               in
                            solve env uu____25452
                          else
                            rigid_rigid_delta env problem wl head1 head2 t1
                              t2)
                       else
                         (let uu____25457 =
                            let uu____25464 = equal t1 t2  in
                            if uu____25464
                            then (FStar_Pervasives_Native.None, wl)
                            else
                              (let uu____25477 = mk_eq2 wl env orig t1 t2  in
                               match uu____25477 with
                               | (g,wl1) ->
                                   ((FStar_Pervasives_Native.Some g), wl1))
                             in
                          match uu____25457 with
                          | (guard,wl1) ->
                              let uu____25498 = solve_prob orig guard [] wl1
                                 in
                              solve env uu____25498))
                    else rigid_rigid_delta env problem wl head1 head2 t1 t2))
              | (uu____25501,FStar_Syntax_Syntax.Tm_name uu____25502) ->
                  let head1 =
                    let uu____25504 = FStar_Syntax_Util.head_and_args t1  in
                    FStar_All.pipe_right uu____25504
                      FStar_Pervasives_Native.fst
                     in
                  let head2 =
                    let uu____25544 = FStar_Syntax_Util.head_and_args t2  in
                    FStar_All.pipe_right uu____25544
                      FStar_Pervasives_Native.fst
                     in
                  ((let uu____25584 =
                      FStar_TypeChecker_Env.debug env
                        (FStar_Options.Other "Rel")
                       in
                    if uu____25584
                    then
                      let uu____25588 =
                        FStar_Util.string_of_int
                          problem.FStar_TypeChecker_Common.pid
                         in
                      let uu____25590 =
                        FStar_Syntax_Print.term_to_string head1  in
                      let uu____25592 =
                        FStar_Syntax_Print.term_to_string head2  in
                      FStar_Util.print3
                        ">> (%s)\n>>> head1 = %s\n>>> head2 = %s\n"
                        uu____25588 uu____25590 uu____25592
                    else ());
                   (let no_free_uvars t =
                      (let uu____25606 = FStar_Syntax_Free.uvars t  in
                       FStar_Util.set_is_empty uu____25606) &&
                        (let uu____25610 = FStar_Syntax_Free.univs t  in
                         FStar_Util.set_is_empty uu____25610)
                       in
                    let equal t11 t21 =
                      let t12 =
                        FStar_TypeChecker_Normalize.normalize
                          [FStar_TypeChecker_Env.UnfoldUntil
                             FStar_Syntax_Syntax.delta_constant;
                          FStar_TypeChecker_Env.Primops;
                          FStar_TypeChecker_Env.Beta;
                          FStar_TypeChecker_Env.Eager_unfolding;
                          FStar_TypeChecker_Env.Iota] env t11
                         in
                      let t22 =
                        FStar_TypeChecker_Normalize.normalize
                          [FStar_TypeChecker_Env.UnfoldUntil
                             FStar_Syntax_Syntax.delta_constant;
                          FStar_TypeChecker_Env.Primops;
                          FStar_TypeChecker_Env.Beta;
                          FStar_TypeChecker_Env.Eager_unfolding;
                          FStar_TypeChecker_Env.Iota] env t21
                         in
                      let uu____25627 = FStar_Syntax_Util.eq_tm t12 t22  in
                      uu____25627 = FStar_Syntax_Util.Equal  in
                    let uu____25628 =
                      ((((FStar_TypeChecker_Env.is_interpreted env head1) ||
                           (FStar_TypeChecker_Env.is_interpreted env head2))
                          &&
                          (problem.FStar_TypeChecker_Common.relation =
                             FStar_TypeChecker_Common.EQ))
                         && (no_free_uvars t1))
                        && (no_free_uvars t2)
                       in
                    if uu____25628
                    then
                      (if Prims.op_Negation wl.smt_ok
                       then
                         let uu____25632 = equal t1 t2  in
                         (if uu____25632
                          then
                            let uu____25635 =
                              solve_prob orig FStar_Pervasives_Native.None []
                                wl
                               in
                            solve env uu____25635
                          else
                            rigid_rigid_delta env problem wl head1 head2 t1
                              t2)
                       else
                         (let uu____25640 =
                            let uu____25647 = equal t1 t2  in
                            if uu____25647
                            then (FStar_Pervasives_Native.None, wl)
                            else
                              (let uu____25660 = mk_eq2 wl env orig t1 t2  in
                               match uu____25660 with
                               | (g,wl1) ->
                                   ((FStar_Pervasives_Native.Some g), wl1))
                             in
                          match uu____25640 with
                          | (guard,wl1) ->
                              let uu____25681 = solve_prob orig guard [] wl1
                                 in
                              solve env uu____25681))
                    else rigid_rigid_delta env problem wl head1 head2 t1 t2))
              | (uu____25684,FStar_Syntax_Syntax.Tm_constant uu____25685) ->
                  let head1 =
                    let uu____25687 = FStar_Syntax_Util.head_and_args t1  in
                    FStar_All.pipe_right uu____25687
                      FStar_Pervasives_Native.fst
                     in
                  let head2 =
                    let uu____25727 = FStar_Syntax_Util.head_and_args t2  in
                    FStar_All.pipe_right uu____25727
                      FStar_Pervasives_Native.fst
                     in
                  ((let uu____25767 =
                      FStar_TypeChecker_Env.debug env
                        (FStar_Options.Other "Rel")
                       in
                    if uu____25767
                    then
                      let uu____25771 =
                        FStar_Util.string_of_int
                          problem.FStar_TypeChecker_Common.pid
                         in
                      let uu____25773 =
                        FStar_Syntax_Print.term_to_string head1  in
                      let uu____25775 =
                        FStar_Syntax_Print.term_to_string head2  in
                      FStar_Util.print3
                        ">> (%s)\n>>> head1 = %s\n>>> head2 = %s\n"
                        uu____25771 uu____25773 uu____25775
                    else ());
                   (let no_free_uvars t =
                      (let uu____25789 = FStar_Syntax_Free.uvars t  in
                       FStar_Util.set_is_empty uu____25789) &&
                        (let uu____25793 = FStar_Syntax_Free.univs t  in
                         FStar_Util.set_is_empty uu____25793)
                       in
                    let equal t11 t21 =
                      let t12 =
                        FStar_TypeChecker_Normalize.normalize
                          [FStar_TypeChecker_Env.UnfoldUntil
                             FStar_Syntax_Syntax.delta_constant;
                          FStar_TypeChecker_Env.Primops;
                          FStar_TypeChecker_Env.Beta;
                          FStar_TypeChecker_Env.Eager_unfolding;
                          FStar_TypeChecker_Env.Iota] env t11
                         in
                      let t22 =
                        FStar_TypeChecker_Normalize.normalize
                          [FStar_TypeChecker_Env.UnfoldUntil
                             FStar_Syntax_Syntax.delta_constant;
                          FStar_TypeChecker_Env.Primops;
                          FStar_TypeChecker_Env.Beta;
                          FStar_TypeChecker_Env.Eager_unfolding;
                          FStar_TypeChecker_Env.Iota] env t21
                         in
                      let uu____25810 = FStar_Syntax_Util.eq_tm t12 t22  in
                      uu____25810 = FStar_Syntax_Util.Equal  in
                    let uu____25811 =
                      ((((FStar_TypeChecker_Env.is_interpreted env head1) ||
                           (FStar_TypeChecker_Env.is_interpreted env head2))
                          &&
                          (problem.FStar_TypeChecker_Common.relation =
                             FStar_TypeChecker_Common.EQ))
                         && (no_free_uvars t1))
                        && (no_free_uvars t2)
                       in
                    if uu____25811
                    then
                      (if Prims.op_Negation wl.smt_ok
                       then
                         let uu____25815 = equal t1 t2  in
                         (if uu____25815
                          then
                            let uu____25818 =
                              solve_prob orig FStar_Pervasives_Native.None []
                                wl
                               in
                            solve env uu____25818
                          else
                            rigid_rigid_delta env problem wl head1 head2 t1
                              t2)
                       else
                         (let uu____25823 =
                            let uu____25830 = equal t1 t2  in
                            if uu____25830
                            then (FStar_Pervasives_Native.None, wl)
                            else
                              (let uu____25843 = mk_eq2 wl env orig t1 t2  in
                               match uu____25843 with
                               | (g,wl1) ->
                                   ((FStar_Pervasives_Native.Some g), wl1))
                             in
                          match uu____25823 with
                          | (guard,wl1) ->
                              let uu____25864 = solve_prob orig guard [] wl1
                                 in
                              solve env uu____25864))
                    else rigid_rigid_delta env problem wl head1 head2 t1 t2))
              | (uu____25867,FStar_Syntax_Syntax.Tm_fvar uu____25868) ->
                  let head1 =
                    let uu____25870 = FStar_Syntax_Util.head_and_args t1  in
                    FStar_All.pipe_right uu____25870
                      FStar_Pervasives_Native.fst
                     in
                  let head2 =
                    let uu____25916 = FStar_Syntax_Util.head_and_args t2  in
                    FStar_All.pipe_right uu____25916
                      FStar_Pervasives_Native.fst
                     in
                  ((let uu____25962 =
                      FStar_TypeChecker_Env.debug env
                        (FStar_Options.Other "Rel")
                       in
                    if uu____25962
                    then
                      let uu____25966 =
                        FStar_Util.string_of_int
                          problem.FStar_TypeChecker_Common.pid
                         in
                      let uu____25968 =
                        FStar_Syntax_Print.term_to_string head1  in
                      let uu____25970 =
                        FStar_Syntax_Print.term_to_string head2  in
                      FStar_Util.print3
                        ">> (%s)\n>>> head1 = %s\n>>> head2 = %s\n"
                        uu____25966 uu____25968 uu____25970
                    else ());
                   (let no_free_uvars t =
                      (let uu____25984 = FStar_Syntax_Free.uvars t  in
                       FStar_Util.set_is_empty uu____25984) &&
                        (let uu____25988 = FStar_Syntax_Free.univs t  in
                         FStar_Util.set_is_empty uu____25988)
                       in
                    let equal t11 t21 =
                      let t12 =
                        FStar_TypeChecker_Normalize.normalize
                          [FStar_TypeChecker_Env.UnfoldUntil
                             FStar_Syntax_Syntax.delta_constant;
                          FStar_TypeChecker_Env.Primops;
                          FStar_TypeChecker_Env.Beta;
                          FStar_TypeChecker_Env.Eager_unfolding;
                          FStar_TypeChecker_Env.Iota] env t11
                         in
                      let t22 =
                        FStar_TypeChecker_Normalize.normalize
                          [FStar_TypeChecker_Env.UnfoldUntil
                             FStar_Syntax_Syntax.delta_constant;
                          FStar_TypeChecker_Env.Primops;
                          FStar_TypeChecker_Env.Beta;
                          FStar_TypeChecker_Env.Eager_unfolding;
                          FStar_TypeChecker_Env.Iota] env t21
                         in
                      let uu____26005 = FStar_Syntax_Util.eq_tm t12 t22  in
                      uu____26005 = FStar_Syntax_Util.Equal  in
                    let uu____26006 =
                      ((((FStar_TypeChecker_Env.is_interpreted env head1) ||
                           (FStar_TypeChecker_Env.is_interpreted env head2))
                          &&
                          (problem.FStar_TypeChecker_Common.relation =
                             FStar_TypeChecker_Common.EQ))
                         && (no_free_uvars t1))
                        && (no_free_uvars t2)
                       in
                    if uu____26006
                    then
                      (if Prims.op_Negation wl.smt_ok
                       then
                         let uu____26010 = equal t1 t2  in
                         (if uu____26010
                          then
                            let uu____26013 =
                              solve_prob orig FStar_Pervasives_Native.None []
                                wl
                               in
                            solve env uu____26013
                          else
                            rigid_rigid_delta env problem wl head1 head2 t1
                              t2)
                       else
                         (let uu____26018 =
                            let uu____26025 = equal t1 t2  in
                            if uu____26025
                            then (FStar_Pervasives_Native.None, wl)
                            else
                              (let uu____26038 = mk_eq2 wl env orig t1 t2  in
                               match uu____26038 with
                               | (g,wl1) ->
                                   ((FStar_Pervasives_Native.Some g), wl1))
                             in
                          match uu____26018 with
                          | (guard,wl1) ->
                              let uu____26059 = solve_prob orig guard [] wl1
                                 in
                              solve env uu____26059))
                    else rigid_rigid_delta env problem wl head1 head2 t1 t2))
              | (uu____26062,FStar_Syntax_Syntax.Tm_app uu____26063) ->
                  let head1 =
                    let uu____26081 = FStar_Syntax_Util.head_and_args t1  in
                    FStar_All.pipe_right uu____26081
                      FStar_Pervasives_Native.fst
                     in
                  let head2 =
                    let uu____26121 = FStar_Syntax_Util.head_and_args t2  in
                    FStar_All.pipe_right uu____26121
                      FStar_Pervasives_Native.fst
                     in
                  ((let uu____26161 =
                      FStar_TypeChecker_Env.debug env
                        (FStar_Options.Other "Rel")
                       in
                    if uu____26161
                    then
                      let uu____26165 =
                        FStar_Util.string_of_int
                          problem.FStar_TypeChecker_Common.pid
                         in
                      let uu____26167 =
                        FStar_Syntax_Print.term_to_string head1  in
                      let uu____26169 =
                        FStar_Syntax_Print.term_to_string head2  in
                      FStar_Util.print3
                        ">> (%s)\n>>> head1 = %s\n>>> head2 = %s\n"
                        uu____26165 uu____26167 uu____26169
                    else ());
                   (let no_free_uvars t =
                      (let uu____26183 = FStar_Syntax_Free.uvars t  in
                       FStar_Util.set_is_empty uu____26183) &&
                        (let uu____26187 = FStar_Syntax_Free.univs t  in
                         FStar_Util.set_is_empty uu____26187)
                       in
                    let equal t11 t21 =
                      let t12 =
                        FStar_TypeChecker_Normalize.normalize
                          [FStar_TypeChecker_Env.UnfoldUntil
                             FStar_Syntax_Syntax.delta_constant;
                          FStar_TypeChecker_Env.Primops;
                          FStar_TypeChecker_Env.Beta;
                          FStar_TypeChecker_Env.Eager_unfolding;
                          FStar_TypeChecker_Env.Iota] env t11
                         in
                      let t22 =
                        FStar_TypeChecker_Normalize.normalize
                          [FStar_TypeChecker_Env.UnfoldUntil
                             FStar_Syntax_Syntax.delta_constant;
                          FStar_TypeChecker_Env.Primops;
                          FStar_TypeChecker_Env.Beta;
                          FStar_TypeChecker_Env.Eager_unfolding;
                          FStar_TypeChecker_Env.Iota] env t21
                         in
                      let uu____26204 = FStar_Syntax_Util.eq_tm t12 t22  in
                      uu____26204 = FStar_Syntax_Util.Equal  in
                    let uu____26205 =
                      ((((FStar_TypeChecker_Env.is_interpreted env head1) ||
                           (FStar_TypeChecker_Env.is_interpreted env head2))
                          &&
                          (problem.FStar_TypeChecker_Common.relation =
                             FStar_TypeChecker_Common.EQ))
                         && (no_free_uvars t1))
                        && (no_free_uvars t2)
                       in
                    if uu____26205
                    then
                      (if Prims.op_Negation wl.smt_ok
                       then
                         let uu____26209 = equal t1 t2  in
                         (if uu____26209
                          then
                            let uu____26212 =
                              solve_prob orig FStar_Pervasives_Native.None []
                                wl
                               in
                            solve env uu____26212
                          else
                            rigid_rigid_delta env problem wl head1 head2 t1
                              t2)
                       else
                         (let uu____26217 =
                            let uu____26224 = equal t1 t2  in
                            if uu____26224
                            then (FStar_Pervasives_Native.None, wl)
                            else
                              (let uu____26237 = mk_eq2 wl env orig t1 t2  in
                               match uu____26237 with
                               | (g,wl1) ->
                                   ((FStar_Pervasives_Native.Some g), wl1))
                             in
                          match uu____26217 with
                          | (guard,wl1) ->
                              let uu____26258 = solve_prob orig guard [] wl1
                                 in
                              solve env uu____26258))
                    else rigid_rigid_delta env problem wl head1 head2 t1 t2))
              | (FStar_Syntax_Syntax.Tm_let
                 uu____26261,FStar_Syntax_Syntax.Tm_let uu____26262) ->
                  let uu____26289 = FStar_Syntax_Util.term_eq t1 t2  in
                  if uu____26289
                  then
                    let uu____26292 =
                      solve_prob orig FStar_Pervasives_Native.None [] wl  in
                    solve env uu____26292
                  else
                    (let uu____26295 = FStar_Thunk.mkv "Tm_let mismatch"  in
                     giveup env uu____26295 orig)
              | (FStar_Syntax_Syntax.Tm_let uu____26298,uu____26299) ->
                  let uu____26313 =
                    let uu____26319 =
                      let uu____26321 = FStar_Syntax_Print.tag_of_term t1  in
                      let uu____26323 = FStar_Syntax_Print.tag_of_term t2  in
                      let uu____26325 = FStar_Syntax_Print.term_to_string t1
                         in
                      let uu____26327 = FStar_Syntax_Print.term_to_string t2
                         in
                      FStar_Util.format4
                        "Internal error: unexpected flex-flex of %s and %s\n>>> (%s) -- (%s)"
                        uu____26321 uu____26323 uu____26325 uu____26327
                       in
                    (FStar_Errors.Fatal_UnificationNotWellFormed,
                      uu____26319)
                     in
                  FStar_Errors.raise_error uu____26313
                    t1.FStar_Syntax_Syntax.pos
              | (uu____26331,FStar_Syntax_Syntax.Tm_let uu____26332) ->
                  let uu____26346 =
                    let uu____26352 =
                      let uu____26354 = FStar_Syntax_Print.tag_of_term t1  in
                      let uu____26356 = FStar_Syntax_Print.tag_of_term t2  in
                      let uu____26358 = FStar_Syntax_Print.term_to_string t1
                         in
                      let uu____26360 = FStar_Syntax_Print.term_to_string t2
                         in
                      FStar_Util.format4
                        "Internal error: unexpected flex-flex of %s and %s\n>>> (%s) -- (%s)"
                        uu____26354 uu____26356 uu____26358 uu____26360
                       in
                    (FStar_Errors.Fatal_UnificationNotWellFormed,
                      uu____26352)
                     in
                  FStar_Errors.raise_error uu____26346
                    t1.FStar_Syntax_Syntax.pos
              | uu____26364 ->
                  let uu____26369 = FStar_Thunk.mkv "head tag mismatch"  in
                  giveup env uu____26369 orig))))

and (solve_c :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.comp FStar_TypeChecker_Common.problem ->
      worklist -> solution)
  =
  fun env  ->
    fun problem  ->
      fun wl  ->
        let c1 = problem.FStar_TypeChecker_Common.lhs  in
        let c2 = problem.FStar_TypeChecker_Common.rhs  in
        let orig = FStar_TypeChecker_Common.CProb problem  in
        let sub_prob wl1 t1 rel t2 reason =
          mk_t_problem wl1 [] orig t1 rel t2 FStar_Pervasives_Native.None
            reason
           in
        let solve_eq c1_comp c2_comp g_lift =
          (let uu____26435 =
             FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
               (FStar_Options.Other "EQ")
              in
           if uu____26435
           then
             let uu____26440 =
               let uu____26442 = FStar_Syntax_Syntax.mk_Comp c1_comp  in
               FStar_Syntax_Print.comp_to_string uu____26442  in
             let uu____26443 =
               let uu____26445 = FStar_Syntax_Syntax.mk_Comp c2_comp  in
               FStar_Syntax_Print.comp_to_string uu____26445  in
             FStar_Util.print2
               "solve_c is using an equality constraint (%s vs %s)\n"
               uu____26440 uu____26443
           else ());
          (let uu____26449 =
             let uu____26451 =
               FStar_Ident.lid_equals c1_comp.FStar_Syntax_Syntax.effect_name
                 c2_comp.FStar_Syntax_Syntax.effect_name
                in
             Prims.op_Negation uu____26451  in
           if uu____26449
           then
             let uu____26454 =
               FStar_Thunk.mk
                 (fun uu____26459  ->
                    let uu____26460 =
                      FStar_Syntax_Print.lid_to_string
                        c1_comp.FStar_Syntax_Syntax.effect_name
                       in
                    let uu____26462 =
                      FStar_Syntax_Print.lid_to_string
                        c2_comp.FStar_Syntax_Syntax.effect_name
                       in
                    FStar_Util.format2 "incompatible effects: %s <> %s"
                      uu____26460 uu____26462)
                in
             giveup env uu____26454 orig
           else
             if
               (FStar_List.length c1_comp.FStar_Syntax_Syntax.effect_args) <>
                 (FStar_List.length c2_comp.FStar_Syntax_Syntax.effect_args)
             then
               (let uu____26484 =
                  FStar_Thunk.mk
                    (fun uu____26489  ->
                       let uu____26490 =
                         FStar_Syntax_Print.args_to_string
                           c1_comp.FStar_Syntax_Syntax.effect_args
                          in
                       let uu____26492 =
                         FStar_Syntax_Print.args_to_string
                           c2_comp.FStar_Syntax_Syntax.effect_args
                          in
                       FStar_Util.format2
                         "incompatible effect arguments: %s <> %s"
                         uu____26490 uu____26492)
                   in
                giveup env uu____26484 orig)
             else
               (let uu____26497 =
                  sub_prob wl c1_comp.FStar_Syntax_Syntax.result_typ
                    FStar_TypeChecker_Common.EQ
                    c2_comp.FStar_Syntax_Syntax.result_typ "effect ret type"
                   in
                match uu____26497 with
                | (ret_sub_prob,wl1) ->
                    let uu____26505 =
                      FStar_List.fold_right2
                        (fun uu____26542  ->
                           fun uu____26543  ->
                             fun uu____26544  ->
                               match (uu____26542, uu____26543, uu____26544)
                               with
                               | ((a1,uu____26588),(a2,uu____26590),(arg_sub_probs,wl2))
                                   ->
                                   let uu____26623 =
                                     sub_prob wl2 a1
                                       FStar_TypeChecker_Common.EQ a2
                                       "effect arg"
                                      in
                                   (match uu____26623 with
                                    | (p,wl3) -> ((p :: arg_sub_probs), wl3)))
                        c1_comp.FStar_Syntax_Syntax.effect_args
                        c2_comp.FStar_Syntax_Syntax.effect_args ([], wl1)
                       in
                    (match uu____26505 with
                     | (arg_sub_probs,wl2) ->
                         let sub_probs =
                           let uu____26650 =
                             let uu____26653 =
                               FStar_All.pipe_right
                                 g_lift.FStar_TypeChecker_Common.deferred
                                 (FStar_List.map FStar_Pervasives_Native.snd)
                                in
                             FStar_List.append arg_sub_probs uu____26653  in
                           ret_sub_prob :: uu____26650  in
                         let guard =
                           let guard =
                             let uu____26675 =
                               FStar_List.map p_guard sub_probs  in
                             FStar_Syntax_Util.mk_conj_l uu____26675  in
                           match g_lift.FStar_TypeChecker_Common.guard_f with
                           | FStar_TypeChecker_Common.Trivial  -> guard
                           | FStar_TypeChecker_Common.NonTrivial f ->
                               FStar_Syntax_Util.mk_conj guard f
                            in
                         let wl3 =
                           let uu___3497_26684 = wl2  in
                           {
                             attempting = (uu___3497_26684.attempting);
                             wl_deferred = (uu___3497_26684.wl_deferred);
                             ctr = (uu___3497_26684.ctr);
                             defer_ok = (uu___3497_26684.defer_ok);
                             smt_ok = (uu___3497_26684.smt_ok);
                             umax_heuristic_ok =
                               (uu___3497_26684.umax_heuristic_ok);
                             tcenv = (uu___3497_26684.tcenv);
                             wl_implicits =
                               (FStar_List.append
                                  g_lift.FStar_TypeChecker_Common.implicits
                                  wl2.wl_implicits)
                           }  in
                         let wl4 =
                           solve_prob orig
                             (FStar_Pervasives_Native.Some guard) [] wl3
                            in
                         let uu____26686 = attempt sub_probs wl4  in
                         solve env uu____26686)))
           in
        let solve_layered_sub c11 edge c21 =
          (let uu____26704 =
             FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
               (FStar_Options.Other "LayeredEffects")
              in
           if uu____26704
           then
             let uu____26709 =
               let uu____26711 =
                 FStar_All.pipe_right c11 FStar_Syntax_Syntax.mk_Comp  in
               FStar_All.pipe_right uu____26711
                 FStar_Syntax_Print.comp_to_string
                in
             let uu____26713 =
               let uu____26715 =
                 FStar_All.pipe_right c21 FStar_Syntax_Syntax.mk_Comp  in
               FStar_All.pipe_right uu____26715
                 FStar_Syntax_Print.comp_to_string
                in
             FStar_Util.print2 "solve_layered_sub c1: %s and c2: %s\n"
               uu____26709 uu____26713
           else ());
          (let uu____26720 =
             let uu____26725 =
               let uu____26730 =
                 FStar_All.pipe_right c11 FStar_Syntax_Syntax.mk_Comp  in
               FStar_All.pipe_right uu____26730
                 ((edge.FStar_TypeChecker_Env.mlift).FStar_TypeChecker_Env.mlift_wp
                    env)
                in
             FStar_All.pipe_right uu____26725
               (fun uu____26747  ->
                  match uu____26747 with
                  | (c,g) ->
                      let uu____26758 = FStar_Syntax_Util.comp_to_comp_typ c
                         in
                      (uu____26758, g))
              in
           match uu____26720 with
           | (c12,g_lift) ->
               ((let uu____26762 =
                   FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                     (FStar_Options.Other "LayeredEffects")
                    in
                 if uu____26762
                 then
                   let uu____26767 =
                     let uu____26769 =
                       FStar_All.pipe_right c12 FStar_Syntax_Syntax.mk_Comp
                        in
                     FStar_All.pipe_right uu____26769
                       FStar_Syntax_Print.comp_to_string
                      in
                   let uu____26771 =
                     let uu____26773 =
                       FStar_All.pipe_right c21 FStar_Syntax_Syntax.mk_Comp
                        in
                     FStar_All.pipe_right uu____26773
                       FStar_Syntax_Print.comp_to_string
                      in
                   FStar_Util.print2
                     "solve_layered_sub after lift c1: %s and c2: %s\n"
                     uu____26767 uu____26771
                 else ());
                if
                  problem.FStar_TypeChecker_Common.relation =
                    FStar_TypeChecker_Common.EQ
                then solve_eq c12 c21 g_lift
                else
                  (let r = FStar_TypeChecker_Env.get_range env  in
                   let wl1 =
                     let uu___3517_26783 = wl  in
                     {
                       attempting = (uu___3517_26783.attempting);
                       wl_deferred = (uu___3517_26783.wl_deferred);
                       ctr = (uu___3517_26783.ctr);
                       defer_ok = (uu___3517_26783.defer_ok);
                       smt_ok = (uu___3517_26783.smt_ok);
                       umax_heuristic_ok =
                         (uu___3517_26783.umax_heuristic_ok);
                       tcenv = (uu___3517_26783.tcenv);
                       wl_implicits =
                         (FStar_List.append
                            g_lift.FStar_TypeChecker_Common.implicits
                            wl.wl_implicits)
                     }  in
                   let uu____26784 =
                     let is_uvar1 t =
                       let uu____26798 =
                         let uu____26799 = FStar_Syntax_Subst.compress t  in
                         uu____26799.FStar_Syntax_Syntax.n  in
                       match uu____26798 with
                       | FStar_Syntax_Syntax.Tm_uvar uu____26803 -> true
                       | FStar_Syntax_Syntax.Tm_uinst
                           ({
                              FStar_Syntax_Syntax.n =
                                FStar_Syntax_Syntax.Tm_uvar uu____26817;
                              FStar_Syntax_Syntax.pos = uu____26818;
                              FStar_Syntax_Syntax.vars = uu____26819;_},uu____26820)
                           -> true
                       | FStar_Syntax_Syntax.Tm_app
                           ({
                              FStar_Syntax_Syntax.n =
                                FStar_Syntax_Syntax.Tm_uvar uu____26838;
                              FStar_Syntax_Syntax.pos = uu____26839;
                              FStar_Syntax_Syntax.vars = uu____26840;_},uu____26841)
                           -> true
                       | uu____26879 -> false  in
                     FStar_List.fold_right2
                       (fun uu____26912  ->
                          fun uu____26913  ->
                            fun uu____26914  ->
                              match (uu____26912, uu____26913, uu____26914)
                              with
                              | ((a1,uu____26958),(a2,uu____26960),(is_sub_probs,wl2))
                                  ->
                                  let uu____26993 = is_uvar1 a1  in
                                  if uu____26993
                                  then
                                    let uu____27002 =
                                      sub_prob wl2 a1
                                        FStar_TypeChecker_Common.EQ a2
                                        "l.h.s. effect index uvar"
                                       in
                                    (match uu____27002 with
                                     | (p,wl3) -> ((p :: is_sub_probs), wl3))
                                  else (is_sub_probs, wl2))
                       c12.FStar_Syntax_Syntax.effect_args
                       c21.FStar_Syntax_Syntax.effect_args ([], wl1)
                      in
                   match uu____26784 with
                   | (is_sub_probs,wl2) ->
                       let uu____27030 =
                         sub_prob wl2 c12.FStar_Syntax_Syntax.result_typ
                           problem.FStar_TypeChecker_Common.relation
                           c21.FStar_Syntax_Syntax.result_typ "result type"
                          in
                       (match uu____27030 with
                        | (ret_sub_prob,wl3) ->
                            let uu____27038 =
                              let uu____27043 =
                                let uu____27044 =
                                  FStar_All.pipe_right
                                    c21.FStar_Syntax_Syntax.effect_name
                                    (FStar_TypeChecker_Env.get_effect_decl
                                       env)
                                   in
                                FStar_All.pipe_right uu____27044
                                  FStar_Syntax_Util.get_stronger_vc_combinator
                                 in
                              FStar_All.pipe_right uu____27043
                                (fun ts  ->
                                   FStar_TypeChecker_Env.inst_tscheme_with ts
                                     c21.FStar_Syntax_Syntax.comp_univs)
                               in
                            (match uu____27038 with
                             | (uu____27051,stronger_t) ->
                                 let stronger_t_shape_error s =
                                   let uu____27062 =
                                     FStar_Ident.string_of_lid
                                       c21.FStar_Syntax_Syntax.effect_name
                                      in
                                   let uu____27064 =
                                     FStar_Syntax_Print.term_to_string
                                       stronger_t
                                      in
                                   FStar_Util.format3
                                     "Unexpected shape of stronger for %s, reason: %s (t:%s)"
                                     uu____27062 s uu____27064
                                    in
                                 let uu____27067 =
                                   let uu____27096 =
                                     let uu____27097 =
                                       FStar_Syntax_Subst.compress stronger_t
                                        in
                                     uu____27097.FStar_Syntax_Syntax.n  in
                                   match uu____27096 with
                                   | FStar_Syntax_Syntax.Tm_arrow (bs,c) when
                                       (FStar_List.length bs) >=
                                         (Prims.of_int (2))
                                       ->
                                       let uu____27157 =
                                         FStar_Syntax_Subst.open_comp bs c
                                          in
                                       (match uu____27157 with
                                        | (a::bs1,c3) ->
                                            let uu____27213 =
                                              let uu____27232 =
                                                FStar_All.pipe_right bs1
                                                  (FStar_List.splitAt
                                                     ((FStar_List.length bs1)
                                                        - Prims.int_one))
                                                 in
                                              FStar_All.pipe_right
                                                uu____27232
                                                (fun uu____27336  ->
                                                   match uu____27336 with
                                                   | (l1,l2) ->
                                                       let uu____27409 =
                                                         FStar_List.hd l2  in
                                                       (l1, uu____27409))
                                               in
                                            (match uu____27213 with
                                             | (rest_bs,f_b) ->
                                                 (a, rest_bs, f_b, c3)))
                                   | uu____27514 ->
                                       let uu____27515 =
                                         let uu____27521 =
                                           stronger_t_shape_error
                                             "not an arrow or not enough binders"
                                            in
                                         (FStar_Errors.Fatal_UnexpectedExpressionType,
                                           uu____27521)
                                          in
                                       FStar_Errors.raise_error uu____27515 r
                                    in
                                 (match uu____27067 with
                                  | (a_b,rest_bs,f_b,stronger_c) ->
                                      let uu____27597 =
                                        let uu____27604 =
                                          let uu____27605 =
                                            let uu____27606 =
                                              let uu____27613 =
                                                FStar_All.pipe_right a_b
                                                  FStar_Pervasives_Native.fst
                                                 in
                                              (uu____27613,
                                                (c21.FStar_Syntax_Syntax.result_typ))
                                               in
                                            FStar_Syntax_Syntax.NT
                                              uu____27606
                                             in
                                          [uu____27605]  in
                                        FStar_TypeChecker_Env.uvars_for_binders
                                          env rest_bs uu____27604
                                          (fun b  ->
                                             let uu____27629 =
                                               FStar_Syntax_Print.binder_to_string
                                                 b
                                                in
                                             let uu____27631 =
                                               FStar_Ident.string_of_lid
                                                 c21.FStar_Syntax_Syntax.effect_name
                                                in
                                             let uu____27633 =
                                               FStar_Range.string_of_range r
                                                in
                                             FStar_Util.format3
                                               "implicit for binder %s in stronger of %s at %s"
                                               uu____27629 uu____27631
                                               uu____27633) r
                                         in
                                      (match uu____27597 with
                                       | (rest_bs_uvars,g_uvars) ->
                                           let wl4 =
                                             let uu___3591_27643 = wl3  in
                                             {
                                               attempting =
                                                 (uu___3591_27643.attempting);
                                               wl_deferred =
                                                 (uu___3591_27643.wl_deferred);
                                               ctr = (uu___3591_27643.ctr);
                                               defer_ok =
                                                 (uu___3591_27643.defer_ok);
                                               smt_ok =
                                                 (uu___3591_27643.smt_ok);
                                               umax_heuristic_ok =
                                                 (uu___3591_27643.umax_heuristic_ok);
                                               tcenv =
                                                 (uu___3591_27643.tcenv);
                                               wl_implicits =
                                                 (FStar_List.append
                                                    g_uvars.FStar_TypeChecker_Common.implicits
                                                    wl3.wl_implicits)
                                             }  in
                                           let substs =
                                             FStar_List.map2
                                               (fun b  ->
                                                  fun t  ->
                                                    let uu____27668 =
                                                      let uu____27675 =
                                                        FStar_All.pipe_right
                                                          b
                                                          FStar_Pervasives_Native.fst
                                                         in
                                                      (uu____27675, t)  in
                                                    FStar_Syntax_Syntax.NT
                                                      uu____27668) (a_b ::
                                               rest_bs)
                                               ((c21.FStar_Syntax_Syntax.result_typ)
                                               :: rest_bs_uvars)
                                              in
                                           let uu____27692 =
                                             let f_sort_is =
                                               let uu____27702 =
                                                 let uu____27703 =
                                                   let uu____27706 =
                                                     let uu____27707 =
                                                       FStar_All.pipe_right
                                                         f_b
                                                         FStar_Pervasives_Native.fst
                                                        in
                                                     uu____27707.FStar_Syntax_Syntax.sort
                                                      in
                                                   FStar_Syntax_Subst.compress
                                                     uu____27706
                                                    in
                                                 uu____27703.FStar_Syntax_Syntax.n
                                                  in
                                               match uu____27702 with
                                               | FStar_Syntax_Syntax.Tm_app
                                                   (uu____27718,uu____27719::is)
                                                   ->
                                                   let uu____27761 =
                                                     FStar_All.pipe_right is
                                                       (FStar_List.map
                                                          FStar_Pervasives_Native.fst)
                                                      in
                                                   FStar_All.pipe_right
                                                     uu____27761
                                                     (FStar_List.map
                                                        (FStar_Syntax_Subst.subst
                                                           substs))
                                               | uu____27794 ->
                                                   let uu____27795 =
                                                     let uu____27801 =
                                                       stronger_t_shape_error
                                                         "type of f is not a repr type"
                                                        in
                                                     (FStar_Errors.Fatal_UnexpectedExpressionType,
                                                       uu____27801)
                                                      in
                                                   FStar_Errors.raise_error
                                                     uu____27795 r
                                                in
                                             let uu____27807 =
                                               FStar_All.pipe_right
                                                 c12.FStar_Syntax_Syntax.effect_args
                                                 (FStar_List.map
                                                    FStar_Pervasives_Native.fst)
                                                in
                                             FStar_List.fold_left2
                                               (fun uu____27842  ->
                                                  fun f_sort_i  ->
                                                    fun c1_i  ->
                                                      match uu____27842 with
                                                      | (ps,wl5) ->
                                                          let uu____27863 =
                                                            sub_prob wl5
                                                              f_sort_i
                                                              FStar_TypeChecker_Common.EQ
                                                              c1_i
                                                              "indices of c1"
                                                             in
                                                          (match uu____27863
                                                           with
                                                           | (p,wl6) ->
                                                               ((FStar_List.append
                                                                   ps 
                                                                   [p]), wl6)))
                                               ([], wl4) f_sort_is
                                               uu____27807
                                              in
                                           (match uu____27692 with
                                            | (f_sub_probs,wl5) ->
                                                let stronger_ct =
                                                  let uu____27888 =
                                                    FStar_All.pipe_right
                                                      stronger_c
                                                      (FStar_Syntax_Subst.subst_comp
                                                         substs)
                                                     in
                                                  FStar_All.pipe_right
                                                    uu____27888
                                                    FStar_Syntax_Util.comp_to_comp_typ
                                                   in
                                                let uu____27889 =
                                                  let g_sort_is =
                                                    let uu____27899 =
                                                      let uu____27900 =
                                                        FStar_Syntax_Subst.compress
                                                          stronger_ct.FStar_Syntax_Syntax.result_typ
                                                         in
                                                      uu____27900.FStar_Syntax_Syntax.n
                                                       in
                                                    match uu____27899 with
                                                    | FStar_Syntax_Syntax.Tm_app
                                                        (uu____27905,uu____27906::is)
                                                        ->
                                                        FStar_All.pipe_right
                                                          is
                                                          (FStar_List.map
                                                             FStar_Pervasives_Native.fst)
                                                    | uu____27974 ->
                                                        let uu____27975 =
                                                          let uu____27981 =
                                                            stronger_t_shape_error
                                                              "return type is not a repr type"
                                                             in
                                                          (FStar_Errors.Fatal_UnexpectedExpressionType,
                                                            uu____27981)
                                                           in
                                                        FStar_Errors.raise_error
                                                          uu____27975 r
                                                     in
                                                  let uu____27987 =
                                                    FStar_All.pipe_right
                                                      c21.FStar_Syntax_Syntax.effect_args
                                                      (FStar_List.map
                                                         FStar_Pervasives_Native.fst)
                                                     in
                                                  FStar_List.fold_left2
                                                    (fun uu____28022  ->
                                                       fun g_sort_i  ->
                                                         fun c2_i  ->
                                                           match uu____28022
                                                           with
                                                           | (ps,wl6) ->
                                                               let uu____28043
                                                                 =
                                                                 sub_prob wl6
                                                                   g_sort_i
                                                                   FStar_TypeChecker_Common.EQ
                                                                   c2_i
                                                                   "indices of c2"
                                                                  in
                                                               (match uu____28043
                                                                with
                                                                | (p,wl7) ->
                                                                    ((FStar_List.append
                                                                    ps [p]),
                                                                    wl7)))
                                                    ([], wl5) g_sort_is
                                                    uu____27987
                                                   in
                                                (match uu____27889 with
                                                 | (g_sub_probs,wl6) ->
                                                     let fml =
                                                       let uu____28070 =
                                                         let uu____28075 =
                                                           FStar_List.hd
                                                             stronger_ct.FStar_Syntax_Syntax.comp_univs
                                                            in
                                                         let uu____28076 =
                                                           let uu____28077 =
                                                             FStar_List.hd
                                                               stronger_ct.FStar_Syntax_Syntax.effect_args
                                                              in
                                                           FStar_Pervasives_Native.fst
                                                             uu____28077
                                                            in
                                                         (uu____28075,
                                                           uu____28076)
                                                          in
                                                       match uu____28070 with
                                                       | (u,wp) ->
                                                           let trivial_post =
                                                             let ts =
                                                               let uu____28104
                                                                 =
                                                                 FStar_TypeChecker_Env.lookup_definition
                                                                   [FStar_TypeChecker_Env.NoDelta]
                                                                   env
                                                                   FStar_Parser_Const.trivial_pure_post_lid
                                                                  in
                                                               FStar_All.pipe_right
                                                                 uu____28104
                                                                 FStar_Util.must
                                                                in
                                                             let uu____28121
                                                               =
                                                               FStar_TypeChecker_Env.inst_tscheme_with
                                                                 ts [u]
                                                                in
                                                             match uu____28121
                                                             with
                                                             | (uu____28126,t)
                                                                 ->
                                                                 let uu____28128
                                                                   =
                                                                   let uu____28133
                                                                    =
                                                                    let uu____28134
                                                                    =
                                                                    FStar_All.pipe_right
                                                                    stronger_ct.FStar_Syntax_Syntax.result_typ
                                                                    FStar_Syntax_Syntax.as_arg
                                                                     in
                                                                    [uu____28134]
                                                                     in
                                                                   FStar_Syntax_Syntax.mk_Tm_app
                                                                    t
                                                                    uu____28133
                                                                    in
                                                                 uu____28128
                                                                   FStar_Pervasives_Native.None
                                                                   FStar_Range.dummyRange
                                                              in
                                                           let uu____28167 =
                                                             let uu____28172
                                                               =
                                                               let uu____28173
                                                                 =
                                                                 FStar_All.pipe_right
                                                                   trivial_post
                                                                   FStar_Syntax_Syntax.as_arg
                                                                  in
                                                               [uu____28173]
                                                                in
                                                             FStar_Syntax_Syntax.mk_Tm_app
                                                               wp uu____28172
                                                              in
                                                           uu____28167
                                                             FStar_Pervasives_Native.None
                                                             FStar_Range.dummyRange
                                                        in
                                                     let sub_probs =
                                                       let uu____28209 =
                                                         let uu____28212 =
                                                           let uu____28215 =
                                                             let uu____28218
                                                               =
                                                               FStar_All.pipe_right
                                                                 g_lift.FStar_TypeChecker_Common.deferred
                                                                 (FStar_List.map
                                                                    FStar_Pervasives_Native.snd)
                                                                in
                                                             FStar_List.append
                                                               g_sub_probs
                                                               uu____28218
                                                              in
                                                           FStar_List.append
                                                             f_sub_probs
                                                             uu____28215
                                                            in
                                                         FStar_List.append
                                                           is_sub_probs
                                                           uu____28212
                                                          in
                                                       ret_sub_prob ::
                                                         uu____28209
                                                        in
                                                     let guard =
                                                       let guard =
                                                         let uu____28242 =
                                                           FStar_List.map
                                                             p_guard
                                                             sub_probs
                                                            in
                                                         FStar_Syntax_Util.mk_conj_l
                                                           uu____28242
                                                          in
                                                       match g_lift.FStar_TypeChecker_Common.guard_f
                                                       with
                                                       | FStar_TypeChecker_Common.Trivial
                                                            -> guard
                                                       | FStar_TypeChecker_Common.NonTrivial
                                                           f ->
                                                           FStar_Syntax_Util.mk_conj
                                                             guard f
                                                        in
                                                     let wl7 =
                                                       let uu____28253 =
                                                         let uu____28256 =
                                                           FStar_Syntax_Util.mk_conj
                                                             guard fml
                                                            in
                                                         FStar_All.pipe_left
                                                           (fun _28259  ->
                                                              FStar_Pervasives_Native.Some
                                                                _28259)
                                                           uu____28256
                                                          in
                                                       solve_prob orig
                                                         uu____28253 [] wl6
                                                        in
                                                     let uu____28260 =
                                                       attempt sub_probs wl7
                                                        in
                                                     solve env uu____28260)))))))))
           in
        let solve_sub c11 edge c21 =
          let r = FStar_TypeChecker_Env.get_range env  in
          let lift_c1 uu____28283 =
            let univs1 =
              match c11.FStar_Syntax_Syntax.comp_univs with
              | [] ->
                  let uu____28285 =
                    env.FStar_TypeChecker_Env.universe_of env
                      c11.FStar_Syntax_Syntax.result_typ
                     in
                  [uu____28285]
              | x -> x  in
            let c12 =
              let uu___3662_28288 = c11  in
              {
                FStar_Syntax_Syntax.comp_univs = univs1;
                FStar_Syntax_Syntax.effect_name =
                  (uu___3662_28288.FStar_Syntax_Syntax.effect_name);
                FStar_Syntax_Syntax.result_typ =
                  (uu___3662_28288.FStar_Syntax_Syntax.result_typ);
                FStar_Syntax_Syntax.effect_args =
                  (uu___3662_28288.FStar_Syntax_Syntax.effect_args);
                FStar_Syntax_Syntax.flags =
                  (uu___3662_28288.FStar_Syntax_Syntax.flags)
              }  in
            let uu____28289 =
              let uu____28294 =
                FStar_All.pipe_right
                  (let uu___3665_28296 = c12  in
                   {
                     FStar_Syntax_Syntax.comp_univs = univs1;
                     FStar_Syntax_Syntax.effect_name =
                       (uu___3665_28296.FStar_Syntax_Syntax.effect_name);
                     FStar_Syntax_Syntax.result_typ =
                       (uu___3665_28296.FStar_Syntax_Syntax.result_typ);
                     FStar_Syntax_Syntax.effect_args =
                       (uu___3665_28296.FStar_Syntax_Syntax.effect_args);
                     FStar_Syntax_Syntax.flags =
                       (uu___3665_28296.FStar_Syntax_Syntax.flags)
                   }) FStar_Syntax_Syntax.mk_Comp
                 in
              FStar_All.pipe_right uu____28294
                ((edge.FStar_TypeChecker_Env.mlift).FStar_TypeChecker_Env.mlift_wp
                   env)
               in
            FStar_All.pipe_right uu____28289
              (fun uu____28310  ->
                 match uu____28310 with
                 | (c,g) ->
                     let uu____28317 =
                       let uu____28319 = FStar_TypeChecker_Env.is_trivial g
                          in
                       Prims.op_Negation uu____28319  in
                     if uu____28317
                     then
                       let uu____28322 =
                         let uu____28328 =
                           let uu____28330 =
                             FStar_Ident.string_of_lid
                               c12.FStar_Syntax_Syntax.effect_name
                              in
                           let uu____28332 =
                             FStar_Ident.string_of_lid
                               c21.FStar_Syntax_Syntax.effect_name
                              in
                           FStar_Util.format2
                             "Lift between wp-effects (%s~>%s) should not have returned a non-trivial guard"
                             uu____28330 uu____28332
                            in
                         (FStar_Errors.Fatal_UnexpectedEffect, uu____28328)
                          in
                       FStar_Errors.raise_error uu____28322 r
                     else FStar_Syntax_Util.comp_to_comp_typ c)
             in
          let uu____28338 =
            FStar_TypeChecker_Env.is_layered_effect env
              c21.FStar_Syntax_Syntax.effect_name
             in
          if uu____28338
          then solve_layered_sub c11 edge c21
          else
            if
              problem.FStar_TypeChecker_Common.relation =
                FStar_TypeChecker_Common.EQ
            then
              (let uu____28344 = lift_c1 ()  in
               solve_eq uu____28344 c21 FStar_TypeChecker_Env.trivial_guard)
            else
              (let is_null_wp_2 =
                 FStar_All.pipe_right c21.FStar_Syntax_Syntax.flags
                   (FStar_Util.for_some
                      (fun uu___31_28353  ->
                         match uu___31_28353 with
                         | FStar_Syntax_Syntax.TOTAL  -> true
                         | FStar_Syntax_Syntax.MLEFFECT  -> true
                         | FStar_Syntax_Syntax.SOMETRIVIAL  -> true
                         | uu____28358 -> false))
                  in
               let uu____28360 =
                 match ((c11.FStar_Syntax_Syntax.effect_args),
                         (c21.FStar_Syntax_Syntax.effect_args))
                 with
                 | ((wp1,uu____28390)::uu____28391,(wp2,uu____28393)::uu____28394)
                     -> (wp1, wp2)
                 | uu____28467 ->
                     let uu____28492 =
                       let uu____28498 =
                         let uu____28500 =
                           FStar_Syntax_Print.lid_to_string
                             c11.FStar_Syntax_Syntax.effect_name
                            in
                         let uu____28502 =
                           FStar_Syntax_Print.lid_to_string
                             c21.FStar_Syntax_Syntax.effect_name
                            in
                         FStar_Util.format2
                           "Got effects %s and %s, expected normalized effects"
                           uu____28500 uu____28502
                          in
                       (FStar_Errors.Fatal_ExpectNormalizedEffect,
                         uu____28498)
                        in
                     FStar_Errors.raise_error uu____28492
                       env.FStar_TypeChecker_Env.range
                  in
               match uu____28360 with
               | (wpc1,wpc2) ->
                   let uu____28512 = FStar_Util.physical_equality wpc1 wpc2
                      in
                   if uu____28512
                   then
                     let uu____28515 =
                       problem_using_guard orig
                         c11.FStar_Syntax_Syntax.result_typ
                         problem.FStar_TypeChecker_Common.relation
                         c21.FStar_Syntax_Syntax.result_typ
                         FStar_Pervasives_Native.None "result type"
                        in
                     solve_t env uu____28515 wl
                   else
                     (let uu____28519 =
                        let uu____28526 =
                          FStar_TypeChecker_Env.effect_decl_opt env
                            c21.FStar_Syntax_Syntax.effect_name
                           in
                        FStar_Util.must uu____28526  in
                      match uu____28519 with
                      | (c2_decl,qualifiers) ->
                          let uu____28547 =
                            FStar_All.pipe_right qualifiers
                              (FStar_List.contains
                                 FStar_Syntax_Syntax.Reifiable)
                             in
                          if uu____28547
                          then
                            let c1_repr =
                              let uu____28554 =
                                let uu____28555 =
                                  let uu____28556 = lift_c1 ()  in
                                  FStar_Syntax_Syntax.mk_Comp uu____28556  in
                                let uu____28557 =
                                  env.FStar_TypeChecker_Env.universe_of env
                                    c11.FStar_Syntax_Syntax.result_typ
                                   in
                                FStar_TypeChecker_Env.reify_comp env
                                  uu____28555 uu____28557
                                 in
                              FStar_TypeChecker_Normalize.normalize
                                [FStar_TypeChecker_Env.UnfoldUntil
                                   FStar_Syntax_Syntax.delta_constant;
                                FStar_TypeChecker_Env.Weak;
                                FStar_TypeChecker_Env.HNF] env uu____28554
                               in
                            let c2_repr =
                              let uu____28559 =
                                let uu____28560 =
                                  FStar_Syntax_Syntax.mk_Comp c21  in
                                let uu____28561 =
                                  env.FStar_TypeChecker_Env.universe_of env
                                    c21.FStar_Syntax_Syntax.result_typ
                                   in
                                FStar_TypeChecker_Env.reify_comp env
                                  uu____28560 uu____28561
                                 in
                              FStar_TypeChecker_Normalize.normalize
                                [FStar_TypeChecker_Env.UnfoldUntil
                                   FStar_Syntax_Syntax.delta_constant;
                                FStar_TypeChecker_Env.Weak;
                                FStar_TypeChecker_Env.HNF] env uu____28559
                               in
                            let uu____28562 =
                              let uu____28567 =
                                let uu____28569 =
                                  FStar_Syntax_Print.term_to_string c1_repr
                                   in
                                let uu____28571 =
                                  FStar_Syntax_Print.term_to_string c2_repr
                                   in
                                FStar_Util.format2
                                  "sub effect repr: %s <: %s" uu____28569
                                  uu____28571
                                 in
                              sub_prob wl c1_repr
                                problem.FStar_TypeChecker_Common.relation
                                c2_repr uu____28567
                               in
                            (match uu____28562 with
                             | (prob,wl1) ->
                                 let wl2 =
                                   solve_prob orig
                                     (FStar_Pervasives_Native.Some
                                        (p_guard prob)) [] wl1
                                    in
                                 let uu____28577 = attempt [prob] wl2  in
                                 solve env uu____28577)
                          else
                            (let g =
                               if env.FStar_TypeChecker_Env.lax
                               then FStar_Syntax_Util.t_true
                               else
                                 (let wpc1_2 =
                                    let uu____28597 = lift_c1 ()  in
                                    FStar_All.pipe_right uu____28597
                                      (fun ct  ->
                                         FStar_List.hd
                                           ct.FStar_Syntax_Syntax.effect_args)
                                     in
                                  if is_null_wp_2
                                  then
                                    ((let uu____28620 =
                                        FStar_All.pipe_left
                                          (FStar_TypeChecker_Env.debug env)
                                          (FStar_Options.Other "Rel")
                                         in
                                      if uu____28620
                                      then
                                        FStar_Util.print_string
                                          "Using trivial wp ... \n"
                                      else ());
                                     (let c1_univ =
                                        env.FStar_TypeChecker_Env.universe_of
                                          env
                                          c11.FStar_Syntax_Syntax.result_typ
                                         in
                                      let trivial =
                                        let uu____28630 =
                                          FStar_All.pipe_right c2_decl
                                            FStar_Syntax_Util.get_wp_trivial_combinator
                                           in
                                        match uu____28630 with
                                        | FStar_Pervasives_Native.None  ->
                                            failwith
                                              "Rel doesn't yet handle undefined trivial combinator in an effect"
                                        | FStar_Pervasives_Native.Some t -> t
                                         in
                                      let uu____28637 =
                                        let uu____28644 =
                                          let uu____28645 =
                                            let uu____28662 =
                                              FStar_TypeChecker_Env.inst_effect_fun_with
                                                [c1_univ] env c2_decl trivial
                                               in
                                            let uu____28665 =
                                              let uu____28676 =
                                                FStar_Syntax_Syntax.as_arg
                                                  c11.FStar_Syntax_Syntax.result_typ
                                                 in
                                              [uu____28676; wpc1_2]  in
                                            (uu____28662, uu____28665)  in
                                          FStar_Syntax_Syntax.Tm_app
                                            uu____28645
                                           in
                                        FStar_Syntax_Syntax.mk uu____28644
                                         in
                                      uu____28637
                                        FStar_Pervasives_Native.None r))
                                  else
                                    (let c2_univ =
                                       env.FStar_TypeChecker_Env.universe_of
                                         env
                                         c21.FStar_Syntax_Syntax.result_typ
                                        in
                                     let stronger =
                                       FStar_All.pipe_right c2_decl
                                         FStar_Syntax_Util.get_stronger_vc_combinator
                                        in
                                     let uu____28725 =
                                       let uu____28732 =
                                         let uu____28733 =
                                           let uu____28750 =
                                             FStar_TypeChecker_Env.inst_effect_fun_with
                                               [c2_univ] env c2_decl stronger
                                              in
                                           let uu____28753 =
                                             let uu____28764 =
                                               FStar_Syntax_Syntax.as_arg
                                                 c21.FStar_Syntax_Syntax.result_typ
                                                in
                                             let uu____28773 =
                                               let uu____28784 =
                                                 FStar_Syntax_Syntax.as_arg
                                                   wpc2
                                                  in
                                               [uu____28784; wpc1_2]  in
                                             uu____28764 :: uu____28773  in
                                           (uu____28750, uu____28753)  in
                                         FStar_Syntax_Syntax.Tm_app
                                           uu____28733
                                          in
                                       FStar_Syntax_Syntax.mk uu____28732  in
                                     uu____28725 FStar_Pervasives_Native.None
                                       r))
                                in
                             (let uu____28838 =
                                FStar_All.pipe_left
                                  (FStar_TypeChecker_Env.debug env)
                                  (FStar_Options.Other "Rel")
                                 in
                              if uu____28838
                              then
                                let uu____28843 =
                                  let uu____28845 =
                                    FStar_TypeChecker_Normalize.normalize
                                      [FStar_TypeChecker_Env.Iota;
                                      FStar_TypeChecker_Env.Eager_unfolding;
                                      FStar_TypeChecker_Env.Primops;
                                      FStar_TypeChecker_Env.Simplify] env g
                                     in
                                  FStar_Syntax_Print.term_to_string
                                    uu____28845
                                   in
                                FStar_Util.print1
                                  "WP guard (simplifed) is (%s)\n"
                                  uu____28843
                              else ());
                             (let uu____28849 =
                                sub_prob wl
                                  c11.FStar_Syntax_Syntax.result_typ
                                  problem.FStar_TypeChecker_Common.relation
                                  c21.FStar_Syntax_Syntax.result_typ
                                  "result type"
                                 in
                              match uu____28849 with
                              | (base_prob,wl1) ->
                                  let wl2 =
                                    let uu____28858 =
                                      let uu____28861 =
                                        FStar_Syntax_Util.mk_conj
                                          (p_guard base_prob) g
                                         in
                                      FStar_All.pipe_left
                                        (fun _28864  ->
                                           FStar_Pervasives_Native.Some
                                             _28864) uu____28861
                                       in
                                    solve_prob orig uu____28858 [] wl1  in
                                  let uu____28865 = attempt [base_prob] wl2
                                     in
                                  solve env uu____28865))))
           in
        let uu____28866 = FStar_Util.physical_equality c1 c2  in
        if uu____28866
        then
          let uu____28869 =
            solve_prob orig FStar_Pervasives_Native.None [] wl  in
          solve env uu____28869
        else
          ((let uu____28873 =
              FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                (FStar_Options.Other "Rel")
               in
            if uu____28873
            then
              let uu____28878 = FStar_Syntax_Print.comp_to_string c1  in
              let uu____28880 = FStar_Syntax_Print.comp_to_string c2  in
              FStar_Util.print3 "solve_c %s %s %s\n" uu____28878
                (rel_to_string problem.FStar_TypeChecker_Common.relation)
                uu____28880
            else ());
           (let uu____28885 =
              let uu____28894 =
                FStar_TypeChecker_Normalize.ghost_to_pure env c1  in
              let uu____28897 =
                FStar_TypeChecker_Normalize.ghost_to_pure env c2  in
              (uu____28894, uu____28897)  in
            match uu____28885 with
            | (c11,c21) ->
                (match ((c11.FStar_Syntax_Syntax.n),
                         (c21.FStar_Syntax_Syntax.n))
                 with
                 | (FStar_Syntax_Syntax.GTotal
                    (t1,uu____28915),FStar_Syntax_Syntax.Total
                    (t2,uu____28917)) when
                     FStar_TypeChecker_Env.non_informative env t2 ->
                     let uu____28934 =
                       problem_using_guard orig t1
                         problem.FStar_TypeChecker_Common.relation t2
                         FStar_Pervasives_Native.None "result type"
                        in
                     solve_t env uu____28934 wl
                 | (FStar_Syntax_Syntax.GTotal
                    uu____28936,FStar_Syntax_Syntax.Total uu____28937) ->
                     let uu____28954 =
                       FStar_Thunk.mkv
                         "incompatible monad ordering: GTot </: Tot"
                        in
                     giveup env uu____28954 orig
                 | (FStar_Syntax_Syntax.Total
                    (t1,uu____28958),FStar_Syntax_Syntax.Total
                    (t2,uu____28960)) ->
                     let uu____28977 =
                       problem_using_guard orig t1
                         problem.FStar_TypeChecker_Common.relation t2
                         FStar_Pervasives_Native.None "result type"
                        in
                     solve_t env uu____28977 wl
                 | (FStar_Syntax_Syntax.GTotal
                    (t1,uu____28980),FStar_Syntax_Syntax.GTotal
                    (t2,uu____28982)) ->
                     let uu____28999 =
                       problem_using_guard orig t1
                         problem.FStar_TypeChecker_Common.relation t2
                         FStar_Pervasives_Native.None "result type"
                        in
                     solve_t env uu____28999 wl
                 | (FStar_Syntax_Syntax.Total
                    (t1,uu____29002),FStar_Syntax_Syntax.GTotal
                    (t2,uu____29004)) when
                     problem.FStar_TypeChecker_Common.relation =
                       FStar_TypeChecker_Common.SUB
                     ->
                     let uu____29021 =
                       problem_using_guard orig t1
                         problem.FStar_TypeChecker_Common.relation t2
                         FStar_Pervasives_Native.None "result type"
                        in
                     solve_t env uu____29021 wl
                 | (FStar_Syntax_Syntax.Total
                    (t1,uu____29024),FStar_Syntax_Syntax.GTotal
                    (t2,uu____29026)) ->
                     let uu____29043 = FStar_Thunk.mkv "GTot =/= Tot"  in
                     giveup env uu____29043 orig
                 | (FStar_Syntax_Syntax.GTotal
                    uu____29046,FStar_Syntax_Syntax.Comp uu____29047) ->
                     let uu____29056 =
                       let uu___3789_29059 = problem  in
                       let uu____29062 =
                         let uu____29063 =
                           FStar_TypeChecker_Env.comp_to_comp_typ env c11  in
                         FStar_All.pipe_left FStar_Syntax_Syntax.mk_Comp
                           uu____29063
                          in
                       {
                         FStar_TypeChecker_Common.pid =
                           (uu___3789_29059.FStar_TypeChecker_Common.pid);
                         FStar_TypeChecker_Common.lhs = uu____29062;
                         FStar_TypeChecker_Common.relation =
                           (uu___3789_29059.FStar_TypeChecker_Common.relation);
                         FStar_TypeChecker_Common.rhs =
                           (uu___3789_29059.FStar_TypeChecker_Common.rhs);
                         FStar_TypeChecker_Common.element =
                           (uu___3789_29059.FStar_TypeChecker_Common.element);
                         FStar_TypeChecker_Common.logical_guard =
                           (uu___3789_29059.FStar_TypeChecker_Common.logical_guard);
                         FStar_TypeChecker_Common.logical_guard_uvar =
                           (uu___3789_29059.FStar_TypeChecker_Common.logical_guard_uvar);
                         FStar_TypeChecker_Common.reason =
                           (uu___3789_29059.FStar_TypeChecker_Common.reason);
                         FStar_TypeChecker_Common.loc =
                           (uu___3789_29059.FStar_TypeChecker_Common.loc);
                         FStar_TypeChecker_Common.rank =
                           (uu___3789_29059.FStar_TypeChecker_Common.rank)
                       }  in
                     solve_c env uu____29056 wl
                 | (FStar_Syntax_Syntax.Total
                    uu____29064,FStar_Syntax_Syntax.Comp uu____29065) ->
                     let uu____29074 =
                       let uu___3789_29077 = problem  in
                       let uu____29080 =
                         let uu____29081 =
                           FStar_TypeChecker_Env.comp_to_comp_typ env c11  in
                         FStar_All.pipe_left FStar_Syntax_Syntax.mk_Comp
                           uu____29081
                          in
                       {
                         FStar_TypeChecker_Common.pid =
                           (uu___3789_29077.FStar_TypeChecker_Common.pid);
                         FStar_TypeChecker_Common.lhs = uu____29080;
                         FStar_TypeChecker_Common.relation =
                           (uu___3789_29077.FStar_TypeChecker_Common.relation);
                         FStar_TypeChecker_Common.rhs =
                           (uu___3789_29077.FStar_TypeChecker_Common.rhs);
                         FStar_TypeChecker_Common.element =
                           (uu___3789_29077.FStar_TypeChecker_Common.element);
                         FStar_TypeChecker_Common.logical_guard =
                           (uu___3789_29077.FStar_TypeChecker_Common.logical_guard);
                         FStar_TypeChecker_Common.logical_guard_uvar =
                           (uu___3789_29077.FStar_TypeChecker_Common.logical_guard_uvar);
                         FStar_TypeChecker_Common.reason =
                           (uu___3789_29077.FStar_TypeChecker_Common.reason);
                         FStar_TypeChecker_Common.loc =
                           (uu___3789_29077.FStar_TypeChecker_Common.loc);
                         FStar_TypeChecker_Common.rank =
                           (uu___3789_29077.FStar_TypeChecker_Common.rank)
                       }  in
                     solve_c env uu____29074 wl
                 | (FStar_Syntax_Syntax.Comp
                    uu____29082,FStar_Syntax_Syntax.GTotal uu____29083) ->
                     let uu____29092 =
                       let uu___3801_29095 = problem  in
                       let uu____29098 =
                         let uu____29099 =
                           FStar_TypeChecker_Env.comp_to_comp_typ env c21  in
                         FStar_All.pipe_left FStar_Syntax_Syntax.mk_Comp
                           uu____29099
                          in
                       {
                         FStar_TypeChecker_Common.pid =
                           (uu___3801_29095.FStar_TypeChecker_Common.pid);
                         FStar_TypeChecker_Common.lhs =
                           (uu___3801_29095.FStar_TypeChecker_Common.lhs);
                         FStar_TypeChecker_Common.relation =
                           (uu___3801_29095.FStar_TypeChecker_Common.relation);
                         FStar_TypeChecker_Common.rhs = uu____29098;
                         FStar_TypeChecker_Common.element =
                           (uu___3801_29095.FStar_TypeChecker_Common.element);
                         FStar_TypeChecker_Common.logical_guard =
                           (uu___3801_29095.FStar_TypeChecker_Common.logical_guard);
                         FStar_TypeChecker_Common.logical_guard_uvar =
                           (uu___3801_29095.FStar_TypeChecker_Common.logical_guard_uvar);
                         FStar_TypeChecker_Common.reason =
                           (uu___3801_29095.FStar_TypeChecker_Common.reason);
                         FStar_TypeChecker_Common.loc =
                           (uu___3801_29095.FStar_TypeChecker_Common.loc);
                         FStar_TypeChecker_Common.rank =
                           (uu___3801_29095.FStar_TypeChecker_Common.rank)
                       }  in
                     solve_c env uu____29092 wl
                 | (FStar_Syntax_Syntax.Comp
                    uu____29100,FStar_Syntax_Syntax.Total uu____29101) ->
                     let uu____29110 =
                       let uu___3801_29113 = problem  in
                       let uu____29116 =
                         let uu____29117 =
                           FStar_TypeChecker_Env.comp_to_comp_typ env c21  in
                         FStar_All.pipe_left FStar_Syntax_Syntax.mk_Comp
                           uu____29117
                          in
                       {
                         FStar_TypeChecker_Common.pid =
                           (uu___3801_29113.FStar_TypeChecker_Common.pid);
                         FStar_TypeChecker_Common.lhs =
                           (uu___3801_29113.FStar_TypeChecker_Common.lhs);
                         FStar_TypeChecker_Common.relation =
                           (uu___3801_29113.FStar_TypeChecker_Common.relation);
                         FStar_TypeChecker_Common.rhs = uu____29116;
                         FStar_TypeChecker_Common.element =
                           (uu___3801_29113.FStar_TypeChecker_Common.element);
                         FStar_TypeChecker_Common.logical_guard =
                           (uu___3801_29113.FStar_TypeChecker_Common.logical_guard);
                         FStar_TypeChecker_Common.logical_guard_uvar =
                           (uu___3801_29113.FStar_TypeChecker_Common.logical_guard_uvar);
                         FStar_TypeChecker_Common.reason =
                           (uu___3801_29113.FStar_TypeChecker_Common.reason);
                         FStar_TypeChecker_Common.loc =
                           (uu___3801_29113.FStar_TypeChecker_Common.loc);
                         FStar_TypeChecker_Common.rank =
                           (uu___3801_29113.FStar_TypeChecker_Common.rank)
                       }  in
                     solve_c env uu____29110 wl
                 | (FStar_Syntax_Syntax.Comp
                    uu____29118,FStar_Syntax_Syntax.Comp uu____29119) ->
                     let uu____29120 =
                       (((FStar_Syntax_Util.is_ml_comp c11) &&
                           (FStar_Syntax_Util.is_ml_comp c21))
                          ||
                          ((FStar_Syntax_Util.is_total_comp c11) &&
                             (FStar_Syntax_Util.is_total_comp c21)))
                         ||
                         (((FStar_Syntax_Util.is_total_comp c11) &&
                             (FStar_Syntax_Util.is_ml_comp c21))
                            &&
                            (problem.FStar_TypeChecker_Common.relation =
                               FStar_TypeChecker_Common.SUB))
                        in
                     if uu____29120
                     then
                       let uu____29123 =
                         problem_using_guard orig
                           (FStar_Syntax_Util.comp_result c11)
                           problem.FStar_TypeChecker_Common.relation
                           (FStar_Syntax_Util.comp_result c21)
                           FStar_Pervasives_Native.None "result type"
                          in
                       solve_t env uu____29123 wl
                     else
                       (let c1_comp =
                          FStar_TypeChecker_Env.comp_to_comp_typ env c11  in
                        let c2_comp =
                          FStar_TypeChecker_Env.comp_to_comp_typ env c21  in
                        if
                          problem.FStar_TypeChecker_Common.relation =
                            FStar_TypeChecker_Common.EQ
                        then
                          let uu____29130 =
                            let uu____29135 =
                              FStar_Ident.lid_equals
                                c1_comp.FStar_Syntax_Syntax.effect_name
                                c2_comp.FStar_Syntax_Syntax.effect_name
                               in
                            if uu____29135
                            then (c1_comp, c2_comp)
                            else
                              (let uu____29144 =
                                 FStar_TypeChecker_Env.unfold_effect_abbrev
                                   env c11
                                  in
                               let uu____29145 =
                                 FStar_TypeChecker_Env.unfold_effect_abbrev
                                   env c21
                                  in
                               (uu____29144, uu____29145))
                             in
                          match uu____29130 with
                          | (c1_comp1,c2_comp1) ->
                              solve_eq c1_comp1 c2_comp1
                                FStar_TypeChecker_Env.trivial_guard
                        else
                          (let c12 =
                             FStar_TypeChecker_Env.unfold_effect_abbrev env
                               c11
                              in
                           let c22 =
                             FStar_TypeChecker_Env.unfold_effect_abbrev env
                               c21
                              in
                           (let uu____29153 =
                              FStar_All.pipe_left
                                (FStar_TypeChecker_Env.debug env)
                                (FStar_Options.Other "Rel")
                               in
                            if uu____29153
                            then
                              FStar_Util.print2 "solve_c for %s and %s\n"
                                (c12.FStar_Syntax_Syntax.effect_name).FStar_Ident.str
                                (c22.FStar_Syntax_Syntax.effect_name).FStar_Ident.str
                            else ());
                           (let uu____29161 =
                              FStar_TypeChecker_Env.monad_leq env
                                c12.FStar_Syntax_Syntax.effect_name
                                c22.FStar_Syntax_Syntax.effect_name
                               in
                            match uu____29161 with
                            | FStar_Pervasives_Native.None  ->
                                let uu____29164 =
                                  FStar_Thunk.mk
                                    (fun uu____29169  ->
                                       let uu____29170 =
                                         FStar_Syntax_Print.lid_to_string
                                           c12.FStar_Syntax_Syntax.effect_name
                                          in
                                       let uu____29172 =
                                         FStar_Syntax_Print.lid_to_string
                                           c22.FStar_Syntax_Syntax.effect_name
                                          in
                                       FStar_Util.format2
                                         "incompatible monad ordering: %s </: %s"
                                         uu____29170 uu____29172)
                                   in
                                giveup env uu____29164 orig
                            | FStar_Pervasives_Native.Some edge ->
                                solve_sub c12 edge c22))))))

let (print_pending_implicits :
  FStar_TypeChecker_Common.guard_t -> Prims.string) =
  fun g  ->
    let uu____29183 =
      FStar_All.pipe_right g.FStar_TypeChecker_Common.implicits
        (FStar_List.map
           (fun i  ->
              FStar_Syntax_Print.term_to_string
                i.FStar_TypeChecker_Common.imp_tm))
       in
    FStar_All.pipe_right uu____29183 (FStar_String.concat ", ")
  
let (ineqs_to_string :
  (FStar_Syntax_Syntax.universe Prims.list * (FStar_Syntax_Syntax.universe *
    FStar_Syntax_Syntax.universe) Prims.list) -> Prims.string)
  =
  fun ineqs  ->
    let vars =
      let uu____29233 =
        FStar_All.pipe_right (FStar_Pervasives_Native.fst ineqs)
          (FStar_List.map FStar_Syntax_Print.univ_to_string)
         in
      FStar_All.pipe_right uu____29233 (FStar_String.concat ", ")  in
    let ineqs1 =
      let uu____29258 =
        FStar_All.pipe_right (FStar_Pervasives_Native.snd ineqs)
          (FStar_List.map
             (fun uu____29289  ->
                match uu____29289 with
                | (u1,u2) ->
                    let uu____29297 = FStar_Syntax_Print.univ_to_string u1
                       in
                    let uu____29299 = FStar_Syntax_Print.univ_to_string u2
                       in
                    FStar_Util.format2 "%s < %s" uu____29297 uu____29299))
         in
      FStar_All.pipe_right uu____29258 (FStar_String.concat ", ")  in
    FStar_Util.format2 "Solving for {%s}; inequalities are {%s}" vars ineqs1
  
let (guard_to_string :
  FStar_TypeChecker_Env.env ->
    FStar_TypeChecker_Common.guard_t -> Prims.string)
  =
  fun env  ->
    fun g  ->
      match ((g.FStar_TypeChecker_Common.guard_f),
              (g.FStar_TypeChecker_Common.deferred),
              (g.FStar_TypeChecker_Common.univ_ineqs))
      with
      | (FStar_TypeChecker_Common.Trivial ,[],(uu____29336,[])) when
          let uu____29363 = FStar_Options.print_implicits ()  in
          Prims.op_Negation uu____29363 -> "{}"
      | uu____29366 ->
          let form =
            match g.FStar_TypeChecker_Common.guard_f with
            | FStar_TypeChecker_Common.Trivial  -> "trivial"
            | FStar_TypeChecker_Common.NonTrivial f ->
                let uu____29393 =
                  ((FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                      (FStar_Options.Other "Rel"))
                     ||
                     (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                        FStar_Options.Extreme))
                    || (FStar_Options.print_implicits ())
                   in
                if uu____29393
                then FStar_TypeChecker_Normalize.term_to_string env f
                else "non-trivial"
             in
          let carry =
            let uu____29405 =
              FStar_List.map
                (fun uu____29418  ->
                   match uu____29418 with
                   | (uu____29425,x) -> prob_to_string env x)
                g.FStar_TypeChecker_Common.deferred
               in
            FStar_All.pipe_right uu____29405 (FStar_String.concat ",\n")  in
          let imps = print_pending_implicits g  in
          let uu____29436 =
            ineqs_to_string g.FStar_TypeChecker_Common.univ_ineqs  in
          FStar_Util.format4
            "\n\t{guard_f=%s;\n\t deferred={\n%s};\n\t univ_ineqs={%s};\n\t implicits={%s}}\n"
            form carry uu____29436 imps
  
let (new_t_problem :
  worklist ->
    FStar_TypeChecker_Env.env ->
      FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
        FStar_TypeChecker_Common.rel ->
          FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
            FStar_Syntax_Syntax.bv FStar_Pervasives_Native.option ->
              FStar_Range.range -> (FStar_TypeChecker_Common.prob * worklist))
  =
  fun wl  ->
    fun env  ->
      fun lhs  ->
        fun rel  ->
          fun rhs  ->
            fun elt  ->
              fun loc  ->
                let reason =
                  let uu____29493 =
                    (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                       (FStar_Options.Other "ExplainRel"))
                      ||
                      (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                         (FStar_Options.Other "Rel"))
                     in
                  if uu____29493
                  then
                    let uu____29501 =
                      FStar_TypeChecker_Normalize.term_to_string env lhs  in
                    let uu____29503 =
                      FStar_TypeChecker_Normalize.term_to_string env rhs  in
                    FStar_Util.format3 "Top-level:\n%s\n\t%s\n%s" uu____29501
                      (rel_to_string rel) uu____29503
                  else "TOP"  in
                let uu____29509 =
                  new_problem wl env lhs rel rhs elt loc reason  in
                match uu____29509 with
                | (p,wl1) ->
                    (def_check_prob (Prims.op_Hat "new_t_problem." reason)
                       (FStar_TypeChecker_Common.TProb p);
                     ((FStar_TypeChecker_Common.TProb p), wl1))
  
let (new_t_prob :
  worklist ->
    FStar_TypeChecker_Env.env ->
      FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
        FStar_TypeChecker_Common.rel ->
          FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
            (FStar_TypeChecker_Common.prob * FStar_Syntax_Syntax.bv *
              worklist))
  =
  fun wl  ->
    fun env  ->
      fun t1  ->
        fun rel  ->
          fun t2  ->
            let x =
              let uu____29569 =
                let uu____29572 = FStar_TypeChecker_Env.get_range env  in
                FStar_All.pipe_left
                  (fun _29575  -> FStar_Pervasives_Native.Some _29575)
                  uu____29572
                 in
              FStar_Syntax_Syntax.new_bv uu____29569 t1  in
            let uu____29576 =
              let uu____29581 = FStar_TypeChecker_Env.get_range env  in
              new_t_problem wl env t1 rel t2 (FStar_Pervasives_Native.Some x)
                uu____29581
               in
            match uu____29576 with | (p,wl1) -> (p, x, wl1)
  
let (solve_and_commit :
  FStar_TypeChecker_Env.env ->
    worklist ->
      ((FStar_TypeChecker_Common.prob * lstring) ->
         (FStar_TypeChecker_Common.deferred *
           FStar_TypeChecker_Common.implicits) FStar_Pervasives_Native.option)
        ->
        (FStar_TypeChecker_Common.deferred *
          FStar_TypeChecker_Common.implicits) FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun probs  ->
      fun err  ->
        let tx = FStar_Syntax_Unionfind.new_transaction ()  in
        (let uu____29639 =
           FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
             (FStar_Options.Other "RelBench")
            in
         if uu____29639
         then
           let uu____29644 =
             FStar_Common.string_of_list
               (fun p  -> FStar_Util.string_of_int (p_pid p))
               probs.attempting
              in
           FStar_Util.print1 "solving problems %s {\n" uu____29644
         else ());
        (let uu____29651 =
           FStar_Util.record_time (fun uu____29658  -> solve env probs)  in
         match uu____29651 with
         | (sol,ms) ->
             ((let uu____29670 =
                 FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                   (FStar_Options.Other "RelBench")
                  in
               if uu____29670
               then
                 let uu____29675 = FStar_Util.string_of_int ms  in
                 FStar_Util.print1 "} solved in %s ms\n" uu____29675
               else ());
              (match sol with
               | Success (deferred,implicits) ->
                   let uu____29688 =
                     FStar_Util.record_time
                       (fun uu____29695  -> FStar_Syntax_Unionfind.commit tx)
                      in
                   (match uu____29688 with
                    | ((),ms1) ->
                        ((let uu____29706 =
                            FStar_All.pipe_left
                              (FStar_TypeChecker_Env.debug env)
                              (FStar_Options.Other "RelBench")
                             in
                          if uu____29706
                          then
                            let uu____29711 = FStar_Util.string_of_int ms1
                               in
                            FStar_Util.print1 "committed in %s ms\n"
                              uu____29711
                          else ());
                         FStar_Pervasives_Native.Some (deferred, implicits)))
               | Failed (d,s) ->
                   ((let uu____29723 =
                       (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                          (FStar_Options.Other "ExplainRel"))
                         ||
                         (FStar_All.pipe_left
                            (FStar_TypeChecker_Env.debug env)
                            (FStar_Options.Other "Rel"))
                        in
                     if uu____29723
                     then
                       let uu____29730 = explain env d s  in
                       FStar_All.pipe_left FStar_Util.print_string
                         uu____29730
                     else ());
                    (let result = err (d, s)  in
                     FStar_Syntax_Unionfind.rollback tx; result)))))
  
let (simplify_guard :
  FStar_TypeChecker_Env.env ->
    FStar_TypeChecker_Common.guard_t -> FStar_TypeChecker_Common.guard_t)
  =
  fun env  ->
    fun g  ->
      match g.FStar_TypeChecker_Common.guard_f with
      | FStar_TypeChecker_Common.Trivial  -> g
      | FStar_TypeChecker_Common.NonTrivial f ->
          ((let uu____29756 =
              FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                (FStar_Options.Other "Simplification")
               in
            if uu____29756
            then
              let uu____29761 = FStar_Syntax_Print.term_to_string f  in
              FStar_Util.print1 "Simplifying guard %s\n" uu____29761
            else ());
           (let f1 =
              FStar_TypeChecker_Normalize.normalize
                [FStar_TypeChecker_Env.Beta;
                FStar_TypeChecker_Env.Eager_unfolding;
                FStar_TypeChecker_Env.Simplify;
                FStar_TypeChecker_Env.Primops;
                FStar_TypeChecker_Env.NoFullNorm] env f
               in
            (let uu____29768 =
               FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                 (FStar_Options.Other "Simplification")
                in
             if uu____29768
             then
               let uu____29773 = FStar_Syntax_Print.term_to_string f1  in
               FStar_Util.print1 "Simplified guard to %s\n" uu____29773
             else ());
            (let f2 =
               let uu____29779 =
                 let uu____29780 = FStar_Syntax_Util.unmeta f1  in
                 uu____29780.FStar_Syntax_Syntax.n  in
               match uu____29779 with
               | FStar_Syntax_Syntax.Tm_fvar fv when
                   FStar_Syntax_Syntax.fv_eq_lid fv
                     FStar_Parser_Const.true_lid
                   -> FStar_TypeChecker_Common.Trivial
               | uu____29784 -> FStar_TypeChecker_Common.NonTrivial f1  in
             let uu___3918_29785 = g  in
             {
               FStar_TypeChecker_Common.guard_f = f2;
               FStar_TypeChecker_Common.deferred =
                 (uu___3918_29785.FStar_TypeChecker_Common.deferred);
               FStar_TypeChecker_Common.univ_ineqs =
                 (uu___3918_29785.FStar_TypeChecker_Common.univ_ineqs);
               FStar_TypeChecker_Common.implicits =
                 (uu___3918_29785.FStar_TypeChecker_Common.implicits)
             })))
  
let (with_guard :
  FStar_TypeChecker_Env.env ->
    FStar_TypeChecker_Common.prob ->
      (FStar_TypeChecker_Common.deferred *
        FStar_TypeChecker_Common.implicits) FStar_Pervasives_Native.option ->
        FStar_TypeChecker_Common.guard_t FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun prob  ->
      fun dopt  ->
        match dopt with
        | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
        | FStar_Pervasives_Native.Some (deferred,implicits) ->
            let uu____29828 =
              let uu____29829 =
                let uu____29830 =
                  FStar_All.pipe_right (p_guard prob)
                    (fun _29831  ->
                       FStar_TypeChecker_Common.NonTrivial _29831)
                   in
                {
                  FStar_TypeChecker_Common.guard_f = uu____29830;
                  FStar_TypeChecker_Common.deferred = deferred;
                  FStar_TypeChecker_Common.univ_ineqs = ([], []);
                  FStar_TypeChecker_Common.implicits = implicits
                }  in
              simplify_guard env uu____29829  in
            FStar_All.pipe_left
              (fun _29838  -> FStar_Pervasives_Native.Some _29838)
              uu____29828
  
let with_guard_no_simp :
  'Auu____29848 .
    'Auu____29848 ->
      FStar_TypeChecker_Common.prob ->
        FStar_TypeChecker_Common.deferred FStar_Pervasives_Native.option ->
          FStar_TypeChecker_Common.guard_t FStar_Pervasives_Native.option
  =
  fun env  ->
    fun prob  ->
      fun dopt  ->
        match dopt with
        | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
        | FStar_Pervasives_Native.Some d ->
            let uu____29871 =
              let uu____29872 =
                FStar_All.pipe_right (p_guard prob)
                  (fun _29873  -> FStar_TypeChecker_Common.NonTrivial _29873)
                 in
              {
                FStar_TypeChecker_Common.guard_f = uu____29872;
                FStar_TypeChecker_Common.deferred = d;
                FStar_TypeChecker_Common.univ_ineqs = ([], []);
                FStar_TypeChecker_Common.implicits = []
              }  in
            FStar_Pervasives_Native.Some uu____29871
  
let (try_teq :
  Prims.bool ->
    FStar_TypeChecker_Env.env ->
      FStar_Syntax_Syntax.typ ->
        FStar_Syntax_Syntax.typ ->
          FStar_TypeChecker_Common.guard_t FStar_Pervasives_Native.option)
  =
  fun smt_ok  ->
    fun env  ->
      fun t1  ->
        fun t2  ->
          (let uu____29906 =
             FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
               (FStar_Options.Other "Rel")
              in
           if uu____29906
           then
             let uu____29911 = FStar_Syntax_Print.term_to_string t1  in
             let uu____29913 = FStar_Syntax_Print.term_to_string t2  in
             FStar_Util.print2 "try_teq of %s and %s {\n" uu____29911
               uu____29913
           else ());
          (let uu____29918 =
             let uu____29923 = FStar_TypeChecker_Env.get_range env  in
             new_t_problem (empty_worklist env) env t1
               FStar_TypeChecker_Common.EQ t2 FStar_Pervasives_Native.None
               uu____29923
              in
           match uu____29918 with
           | (prob,wl) ->
               let g =
                 let uu____29931 =
                   solve_and_commit env (singleton wl prob smt_ok)
                     (fun uu____29939  -> FStar_Pervasives_Native.None)
                    in
                 FStar_All.pipe_left (with_guard env prob) uu____29931  in
               ((let uu____29957 =
                   FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                     (FStar_Options.Other "Rel")
                    in
                 if uu____29957
                 then
                   let uu____29962 =
                     FStar_Common.string_of_option (guard_to_string env) g
                      in
                   FStar_Util.print1 "} res = %s\n" uu____29962
                 else ());
                g))
  
let (teq :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.typ ->
      FStar_Syntax_Syntax.typ -> FStar_TypeChecker_Common.guard_t)
  =
  fun env  ->
    fun t1  ->
      fun t2  ->
        let uu____29983 = try_teq true env t1 t2  in
        match uu____29983 with
        | FStar_Pervasives_Native.None  ->
            ((let uu____29988 = FStar_TypeChecker_Env.get_range env  in
              let uu____29989 =
                FStar_TypeChecker_Err.basic_type_error env
                  FStar_Pervasives_Native.None t2 t1
                 in
              FStar_Errors.log_issue uu____29988 uu____29989);
             FStar_TypeChecker_Common.trivial_guard)
        | FStar_Pervasives_Native.Some g ->
            ((let uu____29997 =
                FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                  (FStar_Options.Other "Rel")
                 in
              if uu____29997
              then
                let uu____30002 = FStar_Syntax_Print.term_to_string t1  in
                let uu____30004 = FStar_Syntax_Print.term_to_string t2  in
                let uu____30006 = guard_to_string env g  in
                FStar_Util.print3
                  "teq of %s and %s succeeded with guard %s\n" uu____30002
                  uu____30004 uu____30006
              else ());
             g)
  
let (subtype_fail :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term ->
      FStar_Syntax_Syntax.typ -> FStar_Syntax_Syntax.typ -> unit)
  =
  fun env  ->
    fun e  ->
      fun t1  ->
        fun t2  ->
          let uu____30032 = FStar_TypeChecker_Env.get_range env  in
          let uu____30033 =
            FStar_TypeChecker_Err.basic_type_error env
              (FStar_Pervasives_Native.Some e) t2 t1
             in
          FStar_Errors.log_issue uu____30032 uu____30033
  
let (sub_comp :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.comp ->
      FStar_Syntax_Syntax.comp ->
        FStar_TypeChecker_Common.guard_t FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun c1  ->
      fun c2  ->
        let rel =
          if env.FStar_TypeChecker_Env.use_eq
          then FStar_TypeChecker_Common.EQ
          else FStar_TypeChecker_Common.SUB  in
        (let uu____30062 =
           FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
             (FStar_Options.Other "Rel")
            in
         if uu____30062
         then
           let uu____30067 = FStar_Syntax_Print.comp_to_string c1  in
           let uu____30069 = FStar_Syntax_Print.comp_to_string c2  in
           FStar_Util.print3 "sub_comp of %s --and-- %s --with-- %s\n"
             uu____30067 uu____30069
             (if rel = FStar_TypeChecker_Common.EQ then "EQ" else "SUB")
         else ());
        (let uu____30080 =
           let uu____30087 = FStar_TypeChecker_Env.get_range env  in
           new_problem (empty_worklist env) env c1 rel c2
             FStar_Pervasives_Native.None uu____30087 "sub_comp"
            in
         match uu____30080 with
         | (prob,wl) ->
             let prob1 = FStar_TypeChecker_Common.CProb prob  in
             (def_check_prob "sub_comp" prob1;
              (let uu____30100 =
                 FStar_Util.record_time
                   (fun uu____30112  ->
                      let uu____30113 =
                        solve_and_commit env (singleton wl prob1 true)
                          (fun uu____30122  -> FStar_Pervasives_Native.None)
                         in
                      FStar_All.pipe_left (with_guard env prob1) uu____30113)
                  in
               match uu____30100 with
               | (r,ms) ->
                   ((let uu____30150 =
                       FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                         (FStar_Options.Other "RelBench")
                        in
                     if uu____30150
                     then
                       let uu____30155 = FStar_Syntax_Print.comp_to_string c1
                          in
                       let uu____30157 = FStar_Syntax_Print.comp_to_string c2
                          in
                       let uu____30159 = FStar_Util.string_of_int ms  in
                       FStar_Util.print4
                         "sub_comp of %s --and-- %s --with-- %s --- solved in %s ms\n"
                         uu____30155 uu____30157
                         (if rel = FStar_TypeChecker_Common.EQ
                          then "EQ"
                          else "SUB") uu____30159
                     else ());
                    r))))
  
let (solve_universe_inequalities' :
  FStar_Syntax_Unionfind.tx ->
    FStar_TypeChecker_Env.env ->
      (FStar_Syntax_Syntax.universe Prims.list *
        (FStar_Syntax_Syntax.universe * FStar_Syntax_Syntax.universe)
        Prims.list) -> unit)
  =
  fun tx  ->
    fun env  ->
      fun uu____30197  ->
        match uu____30197 with
        | (variables,ineqs) ->
            let fail1 u1 u2 =
              FStar_Syntax_Unionfind.rollback tx;
              (let uu____30240 =
                 let uu____30246 =
                   let uu____30248 = FStar_Syntax_Print.univ_to_string u1  in
                   let uu____30250 = FStar_Syntax_Print.univ_to_string u2  in
                   FStar_Util.format2 "Universe %s and %s are incompatible"
                     uu____30248 uu____30250
                    in
                 (FStar_Errors.Fatal_IncompatibleUniverse, uu____30246)  in
               let uu____30254 = FStar_TypeChecker_Env.get_range env  in
               FStar_Errors.raise_error uu____30240 uu____30254)
               in
            let equiv1 v1 v' =
              let uu____30267 =
                let uu____30272 = FStar_Syntax_Subst.compress_univ v1  in
                let uu____30273 = FStar_Syntax_Subst.compress_univ v'  in
                (uu____30272, uu____30273)  in
              match uu____30267 with
              | (FStar_Syntax_Syntax.U_unif v0,FStar_Syntax_Syntax.U_unif
                 v0') -> FStar_Syntax_Unionfind.univ_equiv v0 v0'
              | uu____30293 -> false  in
            let sols =
              FStar_All.pipe_right variables
                (FStar_List.collect
                   (fun v1  ->
                      let uu____30324 = FStar_Syntax_Subst.compress_univ v1
                         in
                      match uu____30324 with
                      | FStar_Syntax_Syntax.U_unif uu____30331 ->
                          let lower_bounds_of_v =
                            FStar_All.pipe_right ineqs
                              (FStar_List.collect
                                 (fun uu____30360  ->
                                    match uu____30360 with
                                    | (u,v') ->
                                        let uu____30369 = equiv1 v1 v'  in
                                        if uu____30369
                                        then
                                          let uu____30374 =
                                            FStar_All.pipe_right variables
                                              (FStar_Util.for_some (equiv1 u))
                                             in
                                          (if uu____30374 then [] else [u])
                                        else []))
                             in
                          let lb =
                            FStar_TypeChecker_Normalize.normalize_universe
                              env
                              (FStar_Syntax_Syntax.U_max lower_bounds_of_v)
                             in
                          [(lb, v1)]
                      | uu____30395 -> []))
               in
            let uu____30400 =
              let wl =
                let uu___4011_30404 = empty_worklist env  in
                {
                  attempting = (uu___4011_30404.attempting);
                  wl_deferred = (uu___4011_30404.wl_deferred);
                  ctr = (uu___4011_30404.ctr);
                  defer_ok = false;
                  smt_ok = (uu___4011_30404.smt_ok);
                  umax_heuristic_ok = (uu___4011_30404.umax_heuristic_ok);
                  tcenv = (uu___4011_30404.tcenv);
                  wl_implicits = (uu___4011_30404.wl_implicits)
                }  in
              FStar_All.pipe_right sols
                (FStar_List.map
                   (fun uu____30423  ->
                      match uu____30423 with
                      | (lb,v1) ->
                          let uu____30430 =
                            solve_universe_eq (~- Prims.int_one) wl lb v1  in
                          (match uu____30430 with
                           | USolved wl1 -> ()
                           | uu____30433 -> fail1 lb v1)))
               in
            let rec check_ineq uu____30444 =
              match uu____30444 with
              | (u,v1) ->
                  let u1 =
                    FStar_TypeChecker_Normalize.normalize_universe env u  in
                  let v2 =
                    FStar_TypeChecker_Normalize.normalize_universe env v1  in
                  (match (u1, v2) with
                   | (FStar_Syntax_Syntax.U_zero ,uu____30456) -> true
                   | (FStar_Syntax_Syntax.U_succ
                      u0,FStar_Syntax_Syntax.U_succ v0) ->
                       check_ineq (u0, v0)
                   | (FStar_Syntax_Syntax.U_name
                      u0,FStar_Syntax_Syntax.U_name v0) ->
                       FStar_Ident.ident_equals u0 v0
                   | (FStar_Syntax_Syntax.U_unif
                      u0,FStar_Syntax_Syntax.U_unif v0) ->
                       FStar_Syntax_Unionfind.univ_equiv u0 v0
                   | (FStar_Syntax_Syntax.U_name
                      uu____30480,FStar_Syntax_Syntax.U_succ v0) ->
                       check_ineq (u1, v0)
                   | (FStar_Syntax_Syntax.U_unif
                      uu____30482,FStar_Syntax_Syntax.U_succ v0) ->
                       check_ineq (u1, v0)
                   | (FStar_Syntax_Syntax.U_max us,uu____30493) ->
                       FStar_All.pipe_right us
                         (FStar_Util.for_all (fun u2  -> check_ineq (u2, v2)))
                   | (uu____30501,FStar_Syntax_Syntax.U_max vs) ->
                       FStar_All.pipe_right vs
                         (FStar_Util.for_some
                            (fun v3  -> check_ineq (u1, v3)))
                   | uu____30510 -> false)
               in
            let uu____30516 =
              FStar_All.pipe_right ineqs
                (FStar_Util.for_all
                   (fun uu____30533  ->
                      match uu____30533 with
                      | (u,v1) ->
                          let uu____30541 = check_ineq (u, v1)  in
                          if uu____30541
                          then true
                          else
                            ((let uu____30549 =
                                FStar_All.pipe_left
                                  (FStar_TypeChecker_Env.debug env)
                                  (FStar_Options.Other "GenUniverses")
                                 in
                              if uu____30549
                              then
                                let uu____30554 =
                                  FStar_Syntax_Print.univ_to_string u  in
                                let uu____30556 =
                                  FStar_Syntax_Print.univ_to_string v1  in
                                FStar_Util.print2 "%s </= %s" uu____30554
                                  uu____30556
                              else ());
                             false)))
               in
            if uu____30516
            then ()
            else
              ((let uu____30566 =
                  FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                    (FStar_Options.Other "GenUniverses")
                   in
                if uu____30566
                then
                  ((let uu____30572 = ineqs_to_string (variables, ineqs)  in
                    FStar_Util.print1
                      "Partially solved inequality constraints are: %s\n"
                      uu____30572);
                   FStar_Syntax_Unionfind.rollback tx;
                   (let uu____30584 = ineqs_to_string (variables, ineqs)  in
                    FStar_Util.print1
                      "Original solved inequality constraints are: %s\n"
                      uu____30584))
                else ());
               (let uu____30597 = FStar_TypeChecker_Env.get_range env  in
                FStar_Errors.raise_error
                  (FStar_Errors.Fatal_FailToSolveUniverseInEquality,
                    "Failed to solve universe inequalities for inductives")
                  uu____30597))
  
let (solve_universe_inequalities :
  FStar_TypeChecker_Env.env ->
    (FStar_Syntax_Syntax.universe Prims.list * (FStar_Syntax_Syntax.universe
      * FStar_Syntax_Syntax.universe) Prims.list) -> unit)
  =
  fun env  ->
    fun ineqs  ->
      let tx = FStar_Syntax_Unionfind.new_transaction ()  in
      solve_universe_inequalities' tx env ineqs;
      FStar_Syntax_Unionfind.commit tx
  
let (try_solve_deferred_constraints :
  Prims.bool ->
    FStar_TypeChecker_Env.env ->
      FStar_TypeChecker_Common.guard_t -> FStar_TypeChecker_Common.guard_t)
  =
  fun defer_ok  ->
    fun env  ->
      fun g  ->
        let fail1 uu____30670 =
          match uu____30670 with
          | (d,s) ->
              let msg = explain env d s  in
              FStar_Errors.raise_error
                (FStar_Errors.Fatal_ErrorInSolveDeferredConstraints, msg)
                (p_loc d)
           in
        let wl =
          let uu___4088_30693 =
            wl_of_guard env g.FStar_TypeChecker_Common.deferred  in
          {
            attempting = (uu___4088_30693.attempting);
            wl_deferred = (uu___4088_30693.wl_deferred);
            ctr = (uu___4088_30693.ctr);
            defer_ok;
            smt_ok = (uu___4088_30693.smt_ok);
            umax_heuristic_ok = (uu___4088_30693.umax_heuristic_ok);
            tcenv = (uu___4088_30693.tcenv);
            wl_implicits = (uu___4088_30693.wl_implicits)
          }  in
        (let uu____30696 =
           FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
             (FStar_Options.Other "Rel")
            in
         if uu____30696
         then
           let uu____30701 = FStar_Util.string_of_bool defer_ok  in
           let uu____30703 = wl_to_string wl  in
           let uu____30705 =
             FStar_Util.string_of_int
               (FStar_List.length g.FStar_TypeChecker_Common.implicits)
              in
           FStar_Util.print3
             "Trying to solve carried problems (defer_ok=%s): begin\n\t%s\nend\n and %s implicits\n"
             uu____30701 uu____30703 uu____30705
         else ());
        (let g1 =
           let uu____30711 = solve_and_commit env wl fail1  in
           match uu____30711 with
           | FStar_Pervasives_Native.Some
               (uu____30718::uu____30719,uu____30720) when
               Prims.op_Negation defer_ok ->
               failwith "Impossible: Unexpected deferred constraints remain"
           | FStar_Pervasives_Native.Some (deferred,imps) ->
               let uu___4103_30749 = g  in
               {
                 FStar_TypeChecker_Common.guard_f =
                   (uu___4103_30749.FStar_TypeChecker_Common.guard_f);
                 FStar_TypeChecker_Common.deferred = deferred;
                 FStar_TypeChecker_Common.univ_ineqs =
                   (uu___4103_30749.FStar_TypeChecker_Common.univ_ineqs);
                 FStar_TypeChecker_Common.implicits =
                   (FStar_List.append g.FStar_TypeChecker_Common.implicits
                      imps)
               }
           | uu____30750 ->
               failwith "Impossible: should have raised a failure already"
            in
         solve_universe_inequalities env
           g1.FStar_TypeChecker_Common.univ_ineqs;
         (let uu___4108_30759 = g1  in
          {
            FStar_TypeChecker_Common.guard_f =
              (uu___4108_30759.FStar_TypeChecker_Common.guard_f);
            FStar_TypeChecker_Common.deferred =
              (uu___4108_30759.FStar_TypeChecker_Common.deferred);
            FStar_TypeChecker_Common.univ_ineqs = ([], []);
            FStar_TypeChecker_Common.implicits =
              (uu___4108_30759.FStar_TypeChecker_Common.implicits)
          }))
  
let (solve_deferred_constraints :
  FStar_TypeChecker_Env.env ->
    FStar_TypeChecker_Common.guard_t -> FStar_TypeChecker_Common.guard_t)
  = fun env  -> fun g  -> try_solve_deferred_constraints false env g 
let (solve_some_deferred_constraints :
  FStar_TypeChecker_Env.env ->
    FStar_TypeChecker_Common.guard_t -> FStar_TypeChecker_Common.guard_t)
  = fun env  -> fun g  -> try_solve_deferred_constraints true env g 
let (discharge_guard' :
  (unit -> Prims.string) FStar_Pervasives_Native.option ->
    FStar_TypeChecker_Env.env ->
      FStar_TypeChecker_Common.guard_t ->
        Prims.bool ->
          FStar_TypeChecker_Common.guard_t FStar_Pervasives_Native.option)
  =
  fun use_env_range_msg  ->
    fun env  ->
      fun g  ->
        fun use_smt  ->
          let debug1 =
            ((FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                (FStar_Options.Other "Rel"))
               ||
               (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                  (FStar_Options.Other "SMTQuery")))
              ||
              (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                 (FStar_Options.Other "Tac"))
             in
          let g1 = solve_deferred_constraints env g  in
          let ret_g =
            let uu___4120_30836 = g1  in
            {
              FStar_TypeChecker_Common.guard_f =
                FStar_TypeChecker_Common.Trivial;
              FStar_TypeChecker_Common.deferred =
                (uu___4120_30836.FStar_TypeChecker_Common.deferred);
              FStar_TypeChecker_Common.univ_ineqs =
                (uu___4120_30836.FStar_TypeChecker_Common.univ_ineqs);
              FStar_TypeChecker_Common.implicits =
                (uu___4120_30836.FStar_TypeChecker_Common.implicits)
            }  in
          let uu____30837 =
            let uu____30839 = FStar_TypeChecker_Env.should_verify env  in
            Prims.op_Negation uu____30839  in
          if uu____30837
          then FStar_Pervasives_Native.Some ret_g
          else
            (match g1.FStar_TypeChecker_Common.guard_f with
             | FStar_TypeChecker_Common.Trivial  ->
                 FStar_Pervasives_Native.Some ret_g
             | FStar_TypeChecker_Common.NonTrivial vc ->
                 (if debug1
                  then
                    (let uu____30851 = FStar_TypeChecker_Env.get_range env
                        in
                     let uu____30852 =
                       let uu____30854 = FStar_Syntax_Print.term_to_string vc
                          in
                       FStar_Util.format1 "Before normalization VC=\n%s\n"
                         uu____30854
                        in
                     FStar_Errors.diag uu____30851 uu____30852)
                  else ();
                  (let vc1 =
                     FStar_TypeChecker_Normalize.normalize
                       [FStar_TypeChecker_Env.Eager_unfolding;
                       FStar_TypeChecker_Env.Simplify;
                       FStar_TypeChecker_Env.Primops] env vc
                      in
                   if debug1
                   then
                     (let uu____30862 = FStar_TypeChecker_Env.get_range env
                         in
                      let uu____30863 =
                        let uu____30865 =
                          FStar_Syntax_Print.term_to_string vc1  in
                        FStar_Util.format1 "After normalization VC=\n%s\n"
                          uu____30865
                         in
                      FStar_Errors.diag uu____30862 uu____30863)
                   else ();
                   (let uu____30871 = FStar_TypeChecker_Env.get_range env  in
                    FStar_TypeChecker_Env.def_check_closed_in_env uu____30871
                      "discharge_guard'" env vc1);
                   (let uu____30873 =
                      FStar_TypeChecker_Common.check_trivial vc1  in
                    match uu____30873 with
                    | FStar_TypeChecker_Common.Trivial  ->
                        FStar_Pervasives_Native.Some ret_g
                    | FStar_TypeChecker_Common.NonTrivial vc2 ->
                        if Prims.op_Negation use_smt
                        then
                          (if debug1
                           then
                             (let uu____30882 =
                                FStar_TypeChecker_Env.get_range env  in
                              let uu____30883 =
                                let uu____30885 =
                                  FStar_Syntax_Print.term_to_string vc2  in
                                FStar_Util.format1
                                  "Cannot solve without SMT : %s\n"
                                  uu____30885
                                 in
                              FStar_Errors.diag uu____30882 uu____30883)
                           else ();
                           FStar_Pervasives_Native.None)
                        else
                          (if debug1
                           then
                             (let uu____30895 =
                                FStar_TypeChecker_Env.get_range env  in
                              let uu____30896 =
                                let uu____30898 =
                                  FStar_Syntax_Print.term_to_string vc2  in
                                FStar_Util.format1 "Checking VC=\n%s\n"
                                  uu____30898
                                 in
                              FStar_Errors.diag uu____30895 uu____30896)
                           else ();
                           (let vcs =
                              let uu____30912 = FStar_Options.use_tactics ()
                                 in
                              if uu____30912
                              then
                                FStar_Options.with_saved_options
                                  (fun uu____30934  ->
                                     (let uu____30936 =
                                        FStar_Options.set_options
                                          "--no_tactics"
                                         in
                                      FStar_All.pipe_left (fun a1  -> ())
                                        uu____30936);
                                     (let vcs =
                                        (env.FStar_TypeChecker_Env.solver).FStar_TypeChecker_Env.preprocess
                                          env vc2
                                         in
                                      FStar_All.pipe_right vcs
                                        (FStar_List.map
                                           (fun uu____30980  ->
                                              match uu____30980 with
                                              | (env1,goal,opts) ->
                                                  let uu____30996 =
                                                    FStar_TypeChecker_Normalize.normalize
                                                      [FStar_TypeChecker_Env.Simplify;
                                                      FStar_TypeChecker_Env.Primops]
                                                      env1 goal
                                                     in
                                                  (env1, uu____30996, opts)))))
                              else
                                (let uu____30999 =
                                   let uu____31006 = FStar_Options.peek ()
                                      in
                                   (env, vc2, uu____31006)  in
                                 [uu____30999])
                               in
                            FStar_All.pipe_right vcs
                              (FStar_List.iter
                                 (fun uu____31039  ->
                                    match uu____31039 with
                                    | (env1,goal,opts) ->
                                        let uu____31049 =
                                          FStar_TypeChecker_Common.check_trivial
                                            goal
                                           in
                                        (match uu____31049 with
                                         | FStar_TypeChecker_Common.Trivial 
                                             ->
                                             if debug1
                                             then
                                               FStar_Util.print_string
                                                 "Goal completely solved by tactic\n"
                                             else ()
                                         | FStar_TypeChecker_Common.NonTrivial
                                             goal1 ->
                                             (FStar_Options.push ();
                                              FStar_Options.set opts;
                                              if debug1
                                              then
                                                (let uu____31060 =
                                                   FStar_TypeChecker_Env.get_range
                                                     env1
                                                    in
                                                 let uu____31061 =
                                                   let uu____31063 =
                                                     FStar_Syntax_Print.term_to_string
                                                       goal1
                                                      in
                                                   let uu____31065 =
                                                     FStar_TypeChecker_Env.string_of_proof_ns
                                                       env1
                                                      in
                                                   FStar_Util.format2
                                                     "Trying to solve:\n> %s\nWith proof_ns:\n %s\n"
                                                     uu____31063 uu____31065
                                                    in
                                                 FStar_Errors.diag
                                                   uu____31060 uu____31061)
                                              else ();
                                              if debug1
                                              then
                                                (let uu____31072 =
                                                   FStar_TypeChecker_Env.get_range
                                                     env1
                                                    in
                                                 let uu____31073 =
                                                   let uu____31075 =
                                                     FStar_Syntax_Print.term_to_string
                                                       goal1
                                                      in
                                                   FStar_Util.format1
                                                     "Before calling solver VC=\n%s\n"
                                                     uu____31075
                                                    in
                                                 FStar_Errors.diag
                                                   uu____31072 uu____31073)
                                              else ();
                                              (env1.FStar_TypeChecker_Env.solver).FStar_TypeChecker_Env.solve
                                                use_env_range_msg env1 goal1;
                                              FStar_Options.pop ())))));
                           FStar_Pervasives_Native.Some ret_g)))))
  
let (discharge_guard_no_smt :
  FStar_TypeChecker_Env.env ->
    FStar_TypeChecker_Common.guard_t -> FStar_TypeChecker_Common.guard_t)
  =
  fun env  ->
    fun g  ->
      let uu____31093 =
        discharge_guard' FStar_Pervasives_Native.None env g false  in
      match uu____31093 with
      | FStar_Pervasives_Native.Some g1 -> g1
      | FStar_Pervasives_Native.None  ->
          let uu____31102 = FStar_TypeChecker_Env.get_range env  in
          FStar_Errors.raise_error
            (FStar_Errors.Fatal_ExpectTrivialPreCondition,
              "Expected a trivial pre-condition") uu____31102
  
let (discharge_guard :
  FStar_TypeChecker_Env.env ->
    FStar_TypeChecker_Common.guard_t -> FStar_TypeChecker_Common.guard_t)
  =
  fun env  ->
    fun g  ->
      let uu____31116 =
        discharge_guard' FStar_Pervasives_Native.None env g true  in
      match uu____31116 with
      | FStar_Pervasives_Native.Some g1 -> g1
      | FStar_Pervasives_Native.None  ->
          failwith
            "Impossible, with use_smt = true, discharge_guard' should never have returned None"
  
let (teq_nosmt :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.typ ->
      FStar_Syntax_Syntax.typ ->
        FStar_TypeChecker_Common.guard_t FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun t1  ->
      fun t2  ->
        let uu____31146 = try_teq false env t1 t2  in
        match uu____31146 with
        | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
        | FStar_Pervasives_Native.Some g ->
            discharge_guard' FStar_Pervasives_Native.None env g false
  
let (resolve_implicits' :
  FStar_TypeChecker_Env.env ->
    Prims.bool ->
      Prims.bool ->
        FStar_TypeChecker_Common.guard_t -> FStar_TypeChecker_Common.guard_t)
  =
  fun env  ->
    fun must_total  ->
      fun forcelax  ->
        fun g  ->
          let rec unresolved ctx_u =
            let uu____31190 =
              FStar_Syntax_Unionfind.find
                ctx_u.FStar_Syntax_Syntax.ctx_uvar_head
               in
            match uu____31190 with
            | FStar_Pervasives_Native.Some r ->
                (match ctx_u.FStar_Syntax_Syntax.ctx_uvar_meta with
                 | FStar_Pervasives_Native.None  -> false
                 | FStar_Pervasives_Native.Some uu____31203 ->
                     let uu____31216 =
                       let uu____31217 = FStar_Syntax_Subst.compress r  in
                       uu____31217.FStar_Syntax_Syntax.n  in
                     (match uu____31216 with
                      | FStar_Syntax_Syntax.Tm_uvar (ctx_u',uu____31222) ->
                          unresolved ctx_u'
                      | uu____31239 -> false))
            | FStar_Pervasives_Native.None  -> true  in
          let rec until_fixpoint acc implicits =
            let uu____31263 = acc  in
            match uu____31263 with
            | (out,changed) ->
                (match implicits with
                 | [] ->
                     if Prims.op_Negation changed
                     then out
                     else until_fixpoint ([], false) out
                 | hd1::tl1 ->
                     let uu____31282 = hd1  in
                     (match uu____31282 with
                      | { FStar_TypeChecker_Common.imp_reason = reason;
                          FStar_TypeChecker_Common.imp_uvar = ctx_u;
                          FStar_TypeChecker_Common.imp_tm = tm;
                          FStar_TypeChecker_Common.imp_range = r;_} ->
                          if
                            ctx_u.FStar_Syntax_Syntax.ctx_uvar_should_check =
                              FStar_Syntax_Syntax.Allow_unresolved
                          then until_fixpoint (out, true) tl1
                          else
                            (let uu____31293 = unresolved ctx_u  in
                             if uu____31293
                             then
                               match ctx_u.FStar_Syntax_Syntax.ctx_uvar_meta
                               with
                               | FStar_Pervasives_Native.None  ->
                                   until_fixpoint ((hd1 :: out), changed) tl1
                               | FStar_Pervasives_Native.Some (env_dyn,tau)
                                   ->
                                   let env1 = FStar_Dyn.undyn env_dyn  in
                                   ((let uu____31317 =
                                       FStar_TypeChecker_Env.debug env1
                                         (FStar_Options.Other "Tac")
                                        in
                                     if uu____31317
                                     then
                                       let uu____31321 =
                                         FStar_Syntax_Print.ctx_uvar_to_string
                                           ctx_u
                                          in
                                       FStar_Util.print1
                                         "Running tactic for meta-arg %s\n"
                                         uu____31321
                                     else ());
                                    (let t =
                                       env1.FStar_TypeChecker_Env.synth_hook
                                         env1
                                         (hd1.FStar_TypeChecker_Common.imp_uvar).FStar_Syntax_Syntax.ctx_uvar_typ
                                         tau
                                        in
                                     let extra =
                                       let uu____31330 = teq_nosmt env1 t tm
                                          in
                                       match uu____31330 with
                                       | FStar_Pervasives_Native.None  ->
                                           failwith
                                             "resolve_implicits: unifying with an unresolved uvar failed?"
                                       | FStar_Pervasives_Native.Some g1 ->
                                           g1.FStar_TypeChecker_Common.implicits
                                        in
                                     let ctx_u1 =
                                       let uu___4232_31340 = ctx_u  in
                                       {
                                         FStar_Syntax_Syntax.ctx_uvar_head =
                                           (uu___4232_31340.FStar_Syntax_Syntax.ctx_uvar_head);
                                         FStar_Syntax_Syntax.ctx_uvar_gamma =
                                           (uu___4232_31340.FStar_Syntax_Syntax.ctx_uvar_gamma);
                                         FStar_Syntax_Syntax.ctx_uvar_binders
                                           =
                                           (uu___4232_31340.FStar_Syntax_Syntax.ctx_uvar_binders);
                                         FStar_Syntax_Syntax.ctx_uvar_typ =
                                           (uu___4232_31340.FStar_Syntax_Syntax.ctx_uvar_typ);
                                         FStar_Syntax_Syntax.ctx_uvar_reason
                                           =
                                           (uu___4232_31340.FStar_Syntax_Syntax.ctx_uvar_reason);
                                         FStar_Syntax_Syntax.ctx_uvar_should_check
                                           =
                                           (uu___4232_31340.FStar_Syntax_Syntax.ctx_uvar_should_check);
                                         FStar_Syntax_Syntax.ctx_uvar_range =
                                           (uu___4232_31340.FStar_Syntax_Syntax.ctx_uvar_range);
                                         FStar_Syntax_Syntax.ctx_uvar_meta =
                                           FStar_Pervasives_Native.None
                                       }  in
                                     let hd2 =
                                       let uu___4235_31348 = hd1  in
                                       {
                                         FStar_TypeChecker_Common.imp_reason
                                           =
                                           (uu___4235_31348.FStar_TypeChecker_Common.imp_reason);
                                         FStar_TypeChecker_Common.imp_uvar =
                                           ctx_u1;
                                         FStar_TypeChecker_Common.imp_tm =
                                           (uu___4235_31348.FStar_TypeChecker_Common.imp_tm);
                                         FStar_TypeChecker_Common.imp_range =
                                           (uu___4235_31348.FStar_TypeChecker_Common.imp_range)
                                       }  in
                                     until_fixpoint (out, true) (hd2 ::
                                       (FStar_List.append extra tl1))))
                             else
                               if
                                 ctx_u.FStar_Syntax_Syntax.ctx_uvar_should_check
                                   = FStar_Syntax_Syntax.Allow_untyped
                               then until_fixpoint (out, true) tl1
                               else
                                 (let env1 =
                                    let uu___4239_31359 = env  in
                                    {
                                      FStar_TypeChecker_Env.solver =
                                        (uu___4239_31359.FStar_TypeChecker_Env.solver);
                                      FStar_TypeChecker_Env.range =
                                        (uu___4239_31359.FStar_TypeChecker_Env.range);
                                      FStar_TypeChecker_Env.curmodule =
                                        (uu___4239_31359.FStar_TypeChecker_Env.curmodule);
                                      FStar_TypeChecker_Env.gamma =
                                        (ctx_u.FStar_Syntax_Syntax.ctx_uvar_gamma);
                                      FStar_TypeChecker_Env.gamma_sig =
                                        (uu___4239_31359.FStar_TypeChecker_Env.gamma_sig);
                                      FStar_TypeChecker_Env.gamma_cache =
                                        (uu___4239_31359.FStar_TypeChecker_Env.gamma_cache);
                                      FStar_TypeChecker_Env.modules =
                                        (uu___4239_31359.FStar_TypeChecker_Env.modules);
                                      FStar_TypeChecker_Env.expected_typ =
                                        (uu___4239_31359.FStar_TypeChecker_Env.expected_typ);
                                      FStar_TypeChecker_Env.sigtab =
                                        (uu___4239_31359.FStar_TypeChecker_Env.sigtab);
                                      FStar_TypeChecker_Env.attrtab =
                                        (uu___4239_31359.FStar_TypeChecker_Env.attrtab);
                                      FStar_TypeChecker_Env.instantiate_imp =
                                        (uu___4239_31359.FStar_TypeChecker_Env.instantiate_imp);
                                      FStar_TypeChecker_Env.effects =
                                        (uu___4239_31359.FStar_TypeChecker_Env.effects);
                                      FStar_TypeChecker_Env.generalize =
                                        (uu___4239_31359.FStar_TypeChecker_Env.generalize);
                                      FStar_TypeChecker_Env.letrecs =
                                        (uu___4239_31359.FStar_TypeChecker_Env.letrecs);
                                      FStar_TypeChecker_Env.top_level =
                                        (uu___4239_31359.FStar_TypeChecker_Env.top_level);
                                      FStar_TypeChecker_Env.check_uvars =
                                        (uu___4239_31359.FStar_TypeChecker_Env.check_uvars);
                                      FStar_TypeChecker_Env.use_eq =
                                        (uu___4239_31359.FStar_TypeChecker_Env.use_eq);
                                      FStar_TypeChecker_Env.is_iface =
                                        (uu___4239_31359.FStar_TypeChecker_Env.is_iface);
                                      FStar_TypeChecker_Env.admit =
                                        (uu___4239_31359.FStar_TypeChecker_Env.admit);
                                      FStar_TypeChecker_Env.lax =
                                        (uu___4239_31359.FStar_TypeChecker_Env.lax);
                                      FStar_TypeChecker_Env.lax_universes =
                                        (uu___4239_31359.FStar_TypeChecker_Env.lax_universes);
                                      FStar_TypeChecker_Env.phase1 =
                                        (uu___4239_31359.FStar_TypeChecker_Env.phase1);
                                      FStar_TypeChecker_Env.failhard =
                                        (uu___4239_31359.FStar_TypeChecker_Env.failhard);
                                      FStar_TypeChecker_Env.nosynth =
                                        (uu___4239_31359.FStar_TypeChecker_Env.nosynth);
                                      FStar_TypeChecker_Env.uvar_subtyping =
                                        (uu___4239_31359.FStar_TypeChecker_Env.uvar_subtyping);
                                      FStar_TypeChecker_Env.tc_term =
                                        (uu___4239_31359.FStar_TypeChecker_Env.tc_term);
                                      FStar_TypeChecker_Env.type_of =
                                        (uu___4239_31359.FStar_TypeChecker_Env.type_of);
                                      FStar_TypeChecker_Env.universe_of =
                                        (uu___4239_31359.FStar_TypeChecker_Env.universe_of);
                                      FStar_TypeChecker_Env.check_type_of =
                                        (uu___4239_31359.FStar_TypeChecker_Env.check_type_of);
                                      FStar_TypeChecker_Env.use_bv_sorts =
                                        (uu___4239_31359.FStar_TypeChecker_Env.use_bv_sorts);
                                      FStar_TypeChecker_Env.qtbl_name_and_index
                                        =
                                        (uu___4239_31359.FStar_TypeChecker_Env.qtbl_name_and_index);
                                      FStar_TypeChecker_Env.normalized_eff_names
                                        =
                                        (uu___4239_31359.FStar_TypeChecker_Env.normalized_eff_names);
                                      FStar_TypeChecker_Env.fv_delta_depths =
                                        (uu___4239_31359.FStar_TypeChecker_Env.fv_delta_depths);
                                      FStar_TypeChecker_Env.proof_ns =
                                        (uu___4239_31359.FStar_TypeChecker_Env.proof_ns);
                                      FStar_TypeChecker_Env.synth_hook =
                                        (uu___4239_31359.FStar_TypeChecker_Env.synth_hook);
                                      FStar_TypeChecker_Env.splice =
                                        (uu___4239_31359.FStar_TypeChecker_Env.splice);
                                      FStar_TypeChecker_Env.mpreprocess =
                                        (uu___4239_31359.FStar_TypeChecker_Env.mpreprocess);
                                      FStar_TypeChecker_Env.postprocess =
                                        (uu___4239_31359.FStar_TypeChecker_Env.postprocess);
                                      FStar_TypeChecker_Env.is_native_tactic
                                        =
                                        (uu___4239_31359.FStar_TypeChecker_Env.is_native_tactic);
                                      FStar_TypeChecker_Env.identifier_info =
                                        (uu___4239_31359.FStar_TypeChecker_Env.identifier_info);
                                      FStar_TypeChecker_Env.tc_hooks =
                                        (uu___4239_31359.FStar_TypeChecker_Env.tc_hooks);
                                      FStar_TypeChecker_Env.dsenv =
                                        (uu___4239_31359.FStar_TypeChecker_Env.dsenv);
                                      FStar_TypeChecker_Env.nbe =
                                        (uu___4239_31359.FStar_TypeChecker_Env.nbe);
                                      FStar_TypeChecker_Env.strict_args_tab =
                                        (uu___4239_31359.FStar_TypeChecker_Env.strict_args_tab);
                                      FStar_TypeChecker_Env.erasable_types_tab
                                        =
                                        (uu___4239_31359.FStar_TypeChecker_Env.erasable_types_tab)
                                    }  in
                                  let tm1 =
                                    FStar_TypeChecker_Normalize.normalize
                                      [FStar_TypeChecker_Env.Beta] env1 tm
                                     in
                                  let env2 =
                                    if forcelax
                                    then
                                      let uu___4244_31363 = env1  in
                                      {
                                        FStar_TypeChecker_Env.solver =
                                          (uu___4244_31363.FStar_TypeChecker_Env.solver);
                                        FStar_TypeChecker_Env.range =
                                          (uu___4244_31363.FStar_TypeChecker_Env.range);
                                        FStar_TypeChecker_Env.curmodule =
                                          (uu___4244_31363.FStar_TypeChecker_Env.curmodule);
                                        FStar_TypeChecker_Env.gamma =
                                          (uu___4244_31363.FStar_TypeChecker_Env.gamma);
                                        FStar_TypeChecker_Env.gamma_sig =
                                          (uu___4244_31363.FStar_TypeChecker_Env.gamma_sig);
                                        FStar_TypeChecker_Env.gamma_cache =
                                          (uu___4244_31363.FStar_TypeChecker_Env.gamma_cache);
                                        FStar_TypeChecker_Env.modules =
                                          (uu___4244_31363.FStar_TypeChecker_Env.modules);
                                        FStar_TypeChecker_Env.expected_typ =
                                          (uu___4244_31363.FStar_TypeChecker_Env.expected_typ);
                                        FStar_TypeChecker_Env.sigtab =
                                          (uu___4244_31363.FStar_TypeChecker_Env.sigtab);
                                        FStar_TypeChecker_Env.attrtab =
                                          (uu___4244_31363.FStar_TypeChecker_Env.attrtab);
                                        FStar_TypeChecker_Env.instantiate_imp
                                          =
                                          (uu___4244_31363.FStar_TypeChecker_Env.instantiate_imp);
                                        FStar_TypeChecker_Env.effects =
                                          (uu___4244_31363.FStar_TypeChecker_Env.effects);
                                        FStar_TypeChecker_Env.generalize =
                                          (uu___4244_31363.FStar_TypeChecker_Env.generalize);
                                        FStar_TypeChecker_Env.letrecs =
                                          (uu___4244_31363.FStar_TypeChecker_Env.letrecs);
                                        FStar_TypeChecker_Env.top_level =
                                          (uu___4244_31363.FStar_TypeChecker_Env.top_level);
                                        FStar_TypeChecker_Env.check_uvars =
                                          (uu___4244_31363.FStar_TypeChecker_Env.check_uvars);
                                        FStar_TypeChecker_Env.use_eq =
                                          (uu___4244_31363.FStar_TypeChecker_Env.use_eq);
                                        FStar_TypeChecker_Env.is_iface =
                                          (uu___4244_31363.FStar_TypeChecker_Env.is_iface);
                                        FStar_TypeChecker_Env.admit =
                                          (uu___4244_31363.FStar_TypeChecker_Env.admit);
                                        FStar_TypeChecker_Env.lax = true;
                                        FStar_TypeChecker_Env.lax_universes =
                                          (uu___4244_31363.FStar_TypeChecker_Env.lax_universes);
                                        FStar_TypeChecker_Env.phase1 =
                                          (uu___4244_31363.FStar_TypeChecker_Env.phase1);
                                        FStar_TypeChecker_Env.failhard =
                                          (uu___4244_31363.FStar_TypeChecker_Env.failhard);
                                        FStar_TypeChecker_Env.nosynth =
                                          (uu___4244_31363.FStar_TypeChecker_Env.nosynth);
                                        FStar_TypeChecker_Env.uvar_subtyping
                                          =
                                          (uu___4244_31363.FStar_TypeChecker_Env.uvar_subtyping);
                                        FStar_TypeChecker_Env.tc_term =
                                          (uu___4244_31363.FStar_TypeChecker_Env.tc_term);
                                        FStar_TypeChecker_Env.type_of =
                                          (uu___4244_31363.FStar_TypeChecker_Env.type_of);
                                        FStar_TypeChecker_Env.universe_of =
                                          (uu___4244_31363.FStar_TypeChecker_Env.universe_of);
                                        FStar_TypeChecker_Env.check_type_of =
                                          (uu___4244_31363.FStar_TypeChecker_Env.check_type_of);
                                        FStar_TypeChecker_Env.use_bv_sorts =
                                          (uu___4244_31363.FStar_TypeChecker_Env.use_bv_sorts);
                                        FStar_TypeChecker_Env.qtbl_name_and_index
                                          =
                                          (uu___4244_31363.FStar_TypeChecker_Env.qtbl_name_and_index);
                                        FStar_TypeChecker_Env.normalized_eff_names
                                          =
                                          (uu___4244_31363.FStar_TypeChecker_Env.normalized_eff_names);
                                        FStar_TypeChecker_Env.fv_delta_depths
                                          =
                                          (uu___4244_31363.FStar_TypeChecker_Env.fv_delta_depths);
                                        FStar_TypeChecker_Env.proof_ns =
                                          (uu___4244_31363.FStar_TypeChecker_Env.proof_ns);
                                        FStar_TypeChecker_Env.synth_hook =
                                          (uu___4244_31363.FStar_TypeChecker_Env.synth_hook);
                                        FStar_TypeChecker_Env.splice =
                                          (uu___4244_31363.FStar_TypeChecker_Env.splice);
                                        FStar_TypeChecker_Env.mpreprocess =
                                          (uu___4244_31363.FStar_TypeChecker_Env.mpreprocess);
                                        FStar_TypeChecker_Env.postprocess =
                                          (uu___4244_31363.FStar_TypeChecker_Env.postprocess);
                                        FStar_TypeChecker_Env.is_native_tactic
                                          =
                                          (uu___4244_31363.FStar_TypeChecker_Env.is_native_tactic);
                                        FStar_TypeChecker_Env.identifier_info
                                          =
                                          (uu___4244_31363.FStar_TypeChecker_Env.identifier_info);
                                        FStar_TypeChecker_Env.tc_hooks =
                                          (uu___4244_31363.FStar_TypeChecker_Env.tc_hooks);
                                        FStar_TypeChecker_Env.dsenv =
                                          (uu___4244_31363.FStar_TypeChecker_Env.dsenv);
                                        FStar_TypeChecker_Env.nbe =
                                          (uu___4244_31363.FStar_TypeChecker_Env.nbe);
                                        FStar_TypeChecker_Env.strict_args_tab
                                          =
                                          (uu___4244_31363.FStar_TypeChecker_Env.strict_args_tab);
                                        FStar_TypeChecker_Env.erasable_types_tab
                                          =
                                          (uu___4244_31363.FStar_TypeChecker_Env.erasable_types_tab)
                                      }
                                    else env1  in
                                  (let uu____31368 =
                                     FStar_All.pipe_left
                                       (FStar_TypeChecker_Env.debug env2)
                                       (FStar_Options.Other "Rel")
                                      in
                                   if uu____31368
                                   then
                                     let uu____31373 =
                                       FStar_Syntax_Print.uvar_to_string
                                         ctx_u.FStar_Syntax_Syntax.ctx_uvar_head
                                        in
                                     let uu____31375 =
                                       FStar_Syntax_Print.term_to_string tm1
                                        in
                                     let uu____31377 =
                                       FStar_Syntax_Print.term_to_string
                                         ctx_u.FStar_Syntax_Syntax.ctx_uvar_typ
                                        in
                                     let uu____31379 =
                                       FStar_Range.string_of_range r  in
                                     FStar_Util.print5
                                       "Checking uvar %s resolved to %s at type %s, introduce for %s at %s\n"
                                       uu____31373 uu____31375 uu____31377
                                       reason uu____31379
                                   else ());
                                  (let g1 =
                                     try
                                       (fun uu___4250_31386  ->
                                          match () with
                                          | () ->
                                              env2.FStar_TypeChecker_Env.check_type_of
                                                must_total env2 tm1
                                                ctx_u.FStar_Syntax_Syntax.ctx_uvar_typ)
                                         ()
                                     with
                                     | e when FStar_Errors.handleable e ->
                                         ((let uu____31393 =
                                             let uu____31403 =
                                               let uu____31411 =
                                                 let uu____31413 =
                                                   FStar_Syntax_Print.uvar_to_string
                                                     ctx_u.FStar_Syntax_Syntax.ctx_uvar_head
                                                    in
                                                 let uu____31415 =
                                                   FStar_TypeChecker_Normalize.term_to_string
                                                     env2 tm1
                                                    in
                                                 let uu____31417 =
                                                   FStar_TypeChecker_Normalize.term_to_string
                                                     env2
                                                     ctx_u.FStar_Syntax_Syntax.ctx_uvar_typ
                                                    in
                                                 FStar_Util.format3
                                                   "Failed while checking implicit %s set to %s of expected type %s"
                                                   uu____31413 uu____31415
                                                   uu____31417
                                                  in
                                               (FStar_Errors.Error_BadImplicit,
                                                 uu____31411, r)
                                                in
                                             [uu____31403]  in
                                           FStar_Errors.add_errors
                                             uu____31393);
                                          FStar_Exn.raise e)
                                      in
                                   let g' =
                                     let uu____31436 =
                                       discharge_guard'
                                         (FStar_Pervasives_Native.Some
                                            (fun uu____31447  ->
                                               let uu____31448 =
                                                 FStar_Syntax_Print.term_to_string
                                                   tm1
                                                  in
                                               let uu____31450 =
                                                 FStar_Range.string_of_range
                                                   r
                                                  in
                                               let uu____31452 =
                                                 FStar_Range.string_of_range
                                                   tm1.FStar_Syntax_Syntax.pos
                                                  in
                                               FStar_Util.format4
                                                 "%s (Introduced at %s for %s resolved at %s)"
                                                 uu____31448 uu____31450
                                                 reason uu____31452)) env2 g1
                                         true
                                        in
                                     match uu____31436 with
                                     | FStar_Pervasives_Native.Some g2 -> g2
                                     | FStar_Pervasives_Native.None  ->
                                         failwith
                                           "Impossible, with use_smt = true, discharge_guard' should never have returned None"
                                      in
                                   until_fixpoint
                                     ((FStar_List.append
                                         g'.FStar_TypeChecker_Common.implicits
                                         out), true) tl1)))))
             in
          let uu___4262_31460 = g  in
          let uu____31461 =
            until_fixpoint ([], false) g.FStar_TypeChecker_Common.implicits
             in
          {
            FStar_TypeChecker_Common.guard_f =
              (uu___4262_31460.FStar_TypeChecker_Common.guard_f);
            FStar_TypeChecker_Common.deferred =
              (uu___4262_31460.FStar_TypeChecker_Common.deferred);
            FStar_TypeChecker_Common.univ_ineqs =
              (uu___4262_31460.FStar_TypeChecker_Common.univ_ineqs);
            FStar_TypeChecker_Common.implicits = uu____31461
          }
  
let (resolve_implicits :
  FStar_TypeChecker_Env.env ->
    FStar_TypeChecker_Common.guard_t -> FStar_TypeChecker_Common.guard_t)
  =
  fun env  ->
    fun g  ->
      resolve_implicits' env
        ((Prims.op_Negation env.FStar_TypeChecker_Env.phase1) &&
           (Prims.op_Negation env.FStar_TypeChecker_Env.lax)) false g
  
let (resolve_implicits_tac :
  FStar_TypeChecker_Env.env ->
    FStar_TypeChecker_Common.guard_t -> FStar_TypeChecker_Common.guard_t)
  = fun env  -> fun g  -> resolve_implicits' env false true g 
let (force_trivial_guard :
  FStar_TypeChecker_Env.env -> FStar_TypeChecker_Common.guard_t -> unit) =
  fun env  ->
    fun g  ->
      let g1 =
        let uu____31501 = solve_deferred_constraints env g  in
        FStar_All.pipe_right uu____31501 (resolve_implicits env)  in
      match g1.FStar_TypeChecker_Common.implicits with
      | [] ->
          let uu____31502 = discharge_guard env g1  in
          FStar_All.pipe_left (fun a2  -> ()) uu____31502
      | imp::uu____31504 ->
          let uu____31507 =
            let uu____31513 =
              let uu____31515 =
                FStar_Syntax_Print.uvar_to_string
                  (imp.FStar_TypeChecker_Common.imp_uvar).FStar_Syntax_Syntax.ctx_uvar_head
                 in
              let uu____31517 =
                FStar_TypeChecker_Normalize.term_to_string env
                  (imp.FStar_TypeChecker_Common.imp_uvar).FStar_Syntax_Syntax.ctx_uvar_typ
                 in
              FStar_Util.format3
                "Failed to resolve implicit argument %s of type %s introduced for %s"
                uu____31515 uu____31517
                imp.FStar_TypeChecker_Common.imp_reason
               in
            (FStar_Errors.Fatal_FailToResolveImplicitArgument, uu____31513)
             in
          FStar_Errors.raise_error uu____31507
            imp.FStar_TypeChecker_Common.imp_range
  
let (teq_force :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.typ -> FStar_Syntax_Syntax.typ -> unit)
  =
  fun env  ->
    fun t1  ->
      fun t2  ->
        let uu____31537 = teq env t1 t2  in
        force_trivial_guard env uu____31537
  
let (teq_nosmt_force :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.typ -> FStar_Syntax_Syntax.typ -> Prims.bool)
  =
  fun env  ->
    fun t1  ->
      fun t2  ->
        let uu____31556 = teq_nosmt env t1 t2  in
        match uu____31556 with
        | FStar_Pervasives_Native.None  -> false
        | FStar_Pervasives_Native.Some g -> (force_trivial_guard env g; true)
  
let (universe_inequality :
  FStar_Syntax_Syntax.universe ->
    FStar_Syntax_Syntax.universe -> FStar_TypeChecker_Common.guard_t)
  =
  fun u1  ->
    fun u2  ->
      let uu___4287_31575 = FStar_TypeChecker_Common.trivial_guard  in
      {
        FStar_TypeChecker_Common.guard_f =
          (uu___4287_31575.FStar_TypeChecker_Common.guard_f);
        FStar_TypeChecker_Common.deferred =
          (uu___4287_31575.FStar_TypeChecker_Common.deferred);
        FStar_TypeChecker_Common.univ_ineqs = ([], [(u1, u2)]);
        FStar_TypeChecker_Common.implicits =
          (uu___4287_31575.FStar_TypeChecker_Common.implicits)
      }
  
let (check_subtyping :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
      FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
        (FStar_Syntax_Syntax.bv * FStar_TypeChecker_Common.guard_t)
          FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun t1  ->
      fun t2  ->
        (let uu____31611 =
           FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
             (FStar_Options.Other "Rel")
            in
         if uu____31611
         then
           let uu____31616 =
             FStar_TypeChecker_Normalize.term_to_string env t1  in
           let uu____31618 =
             FStar_TypeChecker_Normalize.term_to_string env t2  in
           FStar_Util.print2 "check_subtyping of %s and %s\n" uu____31616
             uu____31618
         else ());
        (let uu____31623 =
           new_t_prob (empty_worklist env) env t1
             FStar_TypeChecker_Common.SUB t2
            in
         match uu____31623 with
         | (prob,x,wl) ->
             let g =
               let uu____31642 =
                 solve_and_commit env (singleton wl prob true)
                   (fun uu____31651  -> FStar_Pervasives_Native.None)
                  in
               FStar_All.pipe_left (with_guard env prob) uu____31642  in
             ((let uu____31669 =
                 (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                    (FStar_Options.Other "Rel"))
                   && (FStar_Util.is_some g)
                  in
               if uu____31669
               then
                 let uu____31674 =
                   FStar_TypeChecker_Normalize.term_to_string env t1  in
                 let uu____31676 =
                   FStar_TypeChecker_Normalize.term_to_string env t2  in
                 let uu____31678 =
                   let uu____31680 = FStar_Util.must g  in
                   guard_to_string env uu____31680  in
                 FStar_Util.print3
                   "check_subtyping succeeded: %s <: %s\n\tguard is %s\n"
                   uu____31674 uu____31676 uu____31678
               else ());
              (match g with
               | FStar_Pervasives_Native.None  ->
                   FStar_Pervasives_Native.None
               | FStar_Pervasives_Native.Some g1 ->
                   FStar_Pervasives_Native.Some (x, g1))))
  
let (get_subtyping_predicate :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.typ ->
      FStar_Syntax_Syntax.typ ->
        FStar_TypeChecker_Common.guard_t FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun t1  ->
      fun t2  ->
        let uu____31717 = check_subtyping env t1 t2  in
        match uu____31717 with
        | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
        | FStar_Pervasives_Native.Some (x,g) ->
            let uu____31736 =
              let uu____31737 = FStar_Syntax_Syntax.mk_binder x  in
              FStar_TypeChecker_Env.abstract_guard uu____31737 g  in
            FStar_Pervasives_Native.Some uu____31736
  
let (get_subtyping_prop :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.typ ->
      FStar_Syntax_Syntax.typ ->
        FStar_TypeChecker_Common.guard_t FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun t1  ->
      fun t2  ->
        let uu____31756 = check_subtyping env t1 t2  in
        match uu____31756 with
        | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
        | FStar_Pervasives_Native.Some (x,g) ->
            let uu____31775 =
              let uu____31776 =
                let uu____31777 = FStar_Syntax_Syntax.mk_binder x  in
                [uu____31777]  in
              FStar_TypeChecker_Env.close_guard env uu____31776 g  in
            FStar_Pervasives_Native.Some uu____31775
  
let (subtype_nosmt :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.typ ->
      FStar_Syntax_Syntax.typ ->
        FStar_TypeChecker_Common.guard_t FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun t1  ->
      fun t2  ->
        (let uu____31815 =
           FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
             (FStar_Options.Other "Rel")
            in
         if uu____31815
         then
           let uu____31820 =
             FStar_TypeChecker_Normalize.term_to_string env t1  in
           let uu____31822 =
             FStar_TypeChecker_Normalize.term_to_string env t2  in
           FStar_Util.print2 "try_subtype_no_smt of %s and %s\n" uu____31820
             uu____31822
         else ());
        (let uu____31827 =
           new_t_prob (empty_worklist env) env t1
             FStar_TypeChecker_Common.SUB t2
            in
         match uu____31827 with
         | (prob,x,wl) ->
             let g =
               let uu____31842 =
                 solve_and_commit env (singleton wl prob false)
                   (fun uu____31851  -> FStar_Pervasives_Native.None)
                  in
               FStar_All.pipe_left (with_guard env prob) uu____31842  in
             (match g with
              | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
              | FStar_Pervasives_Native.Some g1 ->
                  let g2 =
                    let uu____31872 =
                      let uu____31873 = FStar_Syntax_Syntax.mk_binder x  in
                      [uu____31873]  in
                    FStar_TypeChecker_Env.close_guard env uu____31872 g1  in
                  discharge_guard' FStar_Pervasives_Native.None env g2 false))
  
let (subtype_nosmt_force :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.typ -> FStar_Syntax_Syntax.typ -> Prims.bool)
  =
  fun env  ->
    fun t1  ->
      fun t2  ->
        let uu____31914 = subtype_nosmt env t1 t2  in
        match uu____31914 with
        | FStar_Pervasives_Native.None  -> false
        | FStar_Pervasives_Native.Some g -> (force_trivial_guard env g; true)
  