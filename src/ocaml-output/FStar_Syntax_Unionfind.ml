open Prims
type vops_t =
  {
  next_major: unit -> FStar_Syntax_Syntax.version ;
  next_minor: unit -> FStar_Syntax_Syntax.version }
let (__proj__Mkvops_t__item__next_major :
  vops_t -> unit -> FStar_Syntax_Syntax.version) =
  fun projectee  ->
    match projectee with | { next_major; next_minor;_} -> next_major
  
let (__proj__Mkvops_t__item__next_minor :
  vops_t -> unit -> FStar_Syntax_Syntax.version) =
  fun projectee  ->
    match projectee with | { next_major; next_minor;_} -> next_minor
  
let (vops : vops_t) =
  let major = FStar_Util.mk_ref Prims.int_zero  in
  let minor = FStar_Util.mk_ref Prims.int_zero  in
  let next_major uu____85 =
    FStar_ST.op_Colon_Equals minor Prims.int_zero;
    (let uu____109 = FStar_Util.incr major; FStar_ST.op_Bang major  in
     {
       FStar_Syntax_Syntax.major = uu____109;
       FStar_Syntax_Syntax.minor = Prims.int_zero
     })
     in
  let next_minor uu____139 =
    let uu____140 = FStar_ST.op_Bang major  in
    let uu____163 = FStar_Util.incr minor; FStar_ST.op_Bang minor  in
    {
      FStar_Syntax_Syntax.major = uu____140;
      FStar_Syntax_Syntax.minor = uu____163
    }  in
  { next_major; next_minor } 
type tgraph =
  FStar_Syntax_Syntax.term FStar_Pervasives_Native.option FStar_Unionfind.puf
type ugraph =
  FStar_Syntax_Syntax.universe FStar_Pervasives_Native.option
    FStar_Unionfind.puf
type uf =
  {
  term_graph: tgraph ;
  univ_graph: ugraph ;
  version: FStar_Syntax_Syntax.version }
let (__proj__Mkuf__item__term_graph : uf -> tgraph) =
  fun projectee  ->
    match projectee with | { term_graph; univ_graph; version;_} -> term_graph
  
let (__proj__Mkuf__item__univ_graph : uf -> ugraph) =
  fun projectee  ->
    match projectee with | { term_graph; univ_graph; version;_} -> univ_graph
  
let (__proj__Mkuf__item__version : uf -> FStar_Syntax_Syntax.version) =
  fun projectee  ->
    match projectee with | { term_graph; univ_graph; version;_} -> version
  
let (empty : FStar_Syntax_Syntax.version -> uf) =
  fun v1  ->
    let uu____243 = FStar_Unionfind.puf_empty ()  in
    let uu____246 = FStar_Unionfind.puf_empty ()  in
    { term_graph = uu____243; univ_graph = uu____246; version = v1 }
  
let (version_to_string : FStar_Syntax_Syntax.version -> Prims.string) =
  fun v1  ->
    let uu____256 = FStar_Util.string_of_int v1.FStar_Syntax_Syntax.major  in
    let uu____258 = FStar_Util.string_of_int v1.FStar_Syntax_Syntax.minor  in
    FStar_Util.format2 "%s.%s" uu____256 uu____258
  
let (state : uf FStar_ST.ref) =
  let uu____264 = let uu____265 = vops.next_major ()  in empty uu____265  in
  FStar_Util.mk_ref uu____264 
type tx =
  | TX of uf 
let (uu___is_TX : tx -> Prims.bool) = fun projectee  -> true 
let (__proj__TX__item___0 : tx -> uf) =
  fun projectee  -> match projectee with | TX _0 -> _0 
let (get : unit -> uf) = fun uu____291  -> FStar_ST.op_Bang state 
let (set : uf -> unit) = fun u  -> FStar_ST.op_Colon_Equals state u 
let (reset : unit -> unit) =
  fun uu____341  ->
    let v1 = vops.next_major ()  in
    let uu____343 = empty v1  in set uu____343
  
let (new_transaction : unit -> tx) =
  fun uu____349  ->
    let tx = let uu____351 = get ()  in TX uu____351  in
    (let uu____353 =
       let uu___34_354 = get ()  in
       let uu____355 = vops.next_minor ()  in
       {
         term_graph = (uu___34_354.term_graph);
         univ_graph = (uu___34_354.univ_graph);
         version = uu____355
       }  in
     set uu____353);
    tx
  
let (commit : tx -> unit) = fun tx  -> () 
let (rollback : tx -> unit) =
  fun uu____367  -> match uu____367 with | TX uf -> set uf 
let update_in_tx : 'a . 'a FStar_ST.ref -> 'a -> unit =
  fun r  -> fun x  -> () 
let (get_term_graph : unit -> tgraph) =
  fun uu____396  -> let uu____397 = get ()  in uu____397.term_graph 
let (get_version : unit -> FStar_Syntax_Syntax.version) =
  fun uu____403  -> let uu____404 = get ()  in uu____404.version 
let (get_version_string : unit -> Prims.string) =
  fun uu____411  ->
    let uu____412 = get_version ()  in
    FStar_All.pipe_right uu____412 version_to_string
  
let (set_term_graph : tgraph -> unit) =
  fun tg  ->
    let uu____420 =
      let uu___48_421 = get ()  in
      {
        term_graph = tg;
        univ_graph = (uu___48_421.univ_graph);
        version = (uu___48_421.version)
      }  in
    set uu____420
  
let (chk_v_t :
  (FStar_Syntax_Syntax.term FStar_Pervasives_Native.option
    FStar_Unionfind.p_uvar * FStar_Syntax_Syntax.version) ->
    FStar_Syntax_Syntax.term FStar_Pervasives_Native.option
      FStar_Unionfind.p_uvar)
  =
  fun uu____439  ->
    match uu____439 with
    | (u,v1) ->
        let uvar_to_string u1 =
          let uu____477 =
            let uu____479 =
              let uu____481 = get_term_graph ()  in
              FStar_Unionfind.puf_id uu____481 u1  in
            FStar_All.pipe_right uu____479 FStar_Util.string_of_int  in
          Prims.op_Hat "?" uu____477  in
        let expected = get_version ()  in
        if
          (v1.FStar_Syntax_Syntax.major = expected.FStar_Syntax_Syntax.major)
            &&
            (v1.FStar_Syntax_Syntax.minor <=
               expected.FStar_Syntax_Syntax.minor)
        then u
        else
          (let uu____500 =
             let uu____502 = uvar_to_string u  in
             let uu____504 = version_to_string expected  in
             let uu____506 = version_to_string v1  in
             FStar_Util.format3
               "Incompatible version for term unification variable %s: current version is %s; got version %s"
               uu____502 uu____504 uu____506
              in
           failwith uu____500)
  
let (uvar_id : FStar_Syntax_Syntax.uvar -> Prims.int) =
  fun u  ->
    let uu____520 = get_term_graph ()  in
    let uu____525 = chk_v_t u  in FStar_Unionfind.puf_id uu____520 uu____525
  
let (from_id : Prims.int -> FStar_Syntax_Syntax.uvar) =
  fun n1  ->
    let uu____540 =
      let uu____547 = get_term_graph ()  in
      FStar_Unionfind.puf_fromid uu____547 n1  in
    let uu____554 = get_version ()  in (uu____540, uu____554)
  
let (fresh : unit -> FStar_Syntax_Syntax.uvar) =
  fun uu____566  ->
    let uu____567 =
      let uu____574 = get_term_graph ()  in
      FStar_Unionfind.puf_fresh uu____574 FStar_Pervasives_Native.None  in
    let uu____581 = get_version ()  in (uu____567, uu____581)
  
let (find :
  FStar_Syntax_Syntax.uvar ->
    FStar_Syntax_Syntax.term FStar_Pervasives_Native.option)
  =
  fun u  ->
    let uu____596 = get_term_graph ()  in
    let uu____601 = chk_v_t u  in
    FStar_Unionfind.puf_find uu____596 uu____601
  
let (change : FStar_Syntax_Syntax.uvar -> FStar_Syntax_Syntax.term -> unit) =
  fun u  ->
    fun t  ->
      let uu____619 =
        let uu____620 = get_term_graph ()  in
        let uu____625 = chk_v_t u  in
        FStar_Unionfind.puf_change uu____620 uu____625
          (FStar_Pervasives_Native.Some t)
         in
      set_term_graph uu____619
  
let (equiv :
  FStar_Syntax_Syntax.uvar -> FStar_Syntax_Syntax.uvar -> Prims.bool) =
  fun u  ->
    fun v1  ->
      let uu____644 = get_term_graph ()  in
      let uu____649 = chk_v_t u  in
      let uu____654 = chk_v_t v1  in
      FStar_Unionfind.puf_equivalent uu____644 uu____649 uu____654
  
let (union : FStar_Syntax_Syntax.uvar -> FStar_Syntax_Syntax.uvar -> unit) =
  fun u  ->
    fun v1  ->
      let uu____672 =
        let uu____673 = get_term_graph ()  in
        let uu____678 = chk_v_t u  in
        let uu____683 = chk_v_t v1  in
        FStar_Unionfind.puf_union uu____673 uu____678 uu____683  in
      set_term_graph uu____672
  
let (get_univ_graph : unit -> ugraph) =
  fun uu____695  -> let uu____696 = get ()  in uu____696.univ_graph 
let (chk_v_u :
  (FStar_Syntax_Syntax.universe FStar_Pervasives_Native.option
    FStar_Unionfind.p_uvar * FStar_Syntax_Syntax.version) ->
    FStar_Syntax_Syntax.universe FStar_Pervasives_Native.option
      FStar_Unionfind.p_uvar)
  =
  fun uu____714  ->
    match uu____714 with
    | (u,v1) ->
        let uvar_to_string u1 =
          let uu____752 =
            let uu____754 =
              let uu____756 = get_univ_graph ()  in
              FStar_Unionfind.puf_id uu____756 u1  in
            FStar_All.pipe_right uu____754 FStar_Util.string_of_int  in
          Prims.op_Hat "?" uu____752  in
        let expected = get_version ()  in
        if
          (v1.FStar_Syntax_Syntax.major = expected.FStar_Syntax_Syntax.major)
            &&
            (v1.FStar_Syntax_Syntax.minor <=
               expected.FStar_Syntax_Syntax.minor)
        then u
        else
          (let uu____775 =
             let uu____777 = uvar_to_string u  in
             let uu____779 = version_to_string expected  in
             let uu____781 = version_to_string v1  in
             FStar_Util.format3
               "Incompatible version for universe unification variable %s: current version is %s; got version %s"
               uu____777 uu____779 uu____781
              in
           failwith uu____775)
  
let (set_univ_graph : ugraph -> unit) =
  fun ug  ->
    let uu____794 =
      let uu___76_795 = get ()  in
      {
        term_graph = (uu___76_795.term_graph);
        univ_graph = ug;
        version = (uu___76_795.version)
      }  in
    set uu____794
  
let (univ_uvar_id : FStar_Syntax_Syntax.universe_uvar -> Prims.int) =
  fun u  ->
    let uu____803 = get_univ_graph ()  in
    let uu____808 = chk_v_u u  in FStar_Unionfind.puf_id uu____803 uu____808
  
let (univ_from_id : Prims.int -> FStar_Syntax_Syntax.universe_uvar) =
  fun n1  ->
    let uu____823 =
      let uu____828 = get_univ_graph ()  in
      FStar_Unionfind.puf_fromid uu____828 n1  in
    let uu____835 = get_version ()  in (uu____823, uu____835)
  
let (univ_fresh : unit -> FStar_Syntax_Syntax.universe_uvar) =
  fun uu____845  ->
    let uu____846 =
      let uu____851 = get_univ_graph ()  in
      FStar_Unionfind.puf_fresh uu____851 FStar_Pervasives_Native.None  in
    let uu____858 = get_version ()  in (uu____846, uu____858)
  
let (univ_find :
  FStar_Syntax_Syntax.universe_uvar ->
    FStar_Syntax_Syntax.universe FStar_Pervasives_Native.option)
  =
  fun u  ->
    let uu____871 = get_univ_graph ()  in
    let uu____876 = chk_v_u u  in
    FStar_Unionfind.puf_find uu____871 uu____876
  
let (univ_change :
  FStar_Syntax_Syntax.universe_uvar -> FStar_Syntax_Syntax.universe -> unit)
  =
  fun u  ->
    fun t  ->
      let uu____894 =
        let uu____895 = get_univ_graph ()  in
        let uu____900 = chk_v_u u  in
        FStar_Unionfind.puf_change uu____895 uu____900
          (FStar_Pervasives_Native.Some t)
         in
      set_univ_graph uu____894
  
let (univ_equiv :
  FStar_Syntax_Syntax.universe_uvar ->
    FStar_Syntax_Syntax.universe_uvar -> Prims.bool)
  =
  fun u  ->
    fun v1  ->
      let uu____919 = get_univ_graph ()  in
      let uu____924 = chk_v_u u  in
      let uu____929 = chk_v_u v1  in
      FStar_Unionfind.puf_equivalent uu____919 uu____924 uu____929
  
let (univ_union :
  FStar_Syntax_Syntax.universe_uvar ->
    FStar_Syntax_Syntax.universe_uvar -> unit)
  =
  fun u  ->
    fun v1  ->
      let uu____947 =
        let uu____948 = get_univ_graph ()  in
        let uu____953 = chk_v_u u  in
        let uu____958 = chk_v_u v1  in
        FStar_Unionfind.puf_union uu____948 uu____953 uu____958  in
      set_univ_graph uu____947
  