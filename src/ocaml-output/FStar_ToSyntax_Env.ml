
open Prims
open FStar_Pervasives

type local_binding =
(FStar_Ident.ident * FStar_Syntax_Syntax.bv * Prims.bool)


type rec_binding =
(FStar_Ident.ident * FStar_Ident.lid * FStar_Syntax_Syntax.delta_depth)


type module_abbrev =
(FStar_Ident.ident * FStar_Ident.lident)

type open_kind =
| Open_module
| Open_namespace


let uu___is_Open_module : open_kind  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Open_module -> begin
true
end
| uu____21 -> begin
false
end))


let uu___is_Open_namespace : open_kind  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Open_namespace -> begin
true
end
| uu____26 -> begin
false
end))


type open_module_or_namespace =
(FStar_Ident.lident * open_kind)

type record_or_dc =
{typename : FStar_Ident.lident; constrname : FStar_Ident.ident; parms : FStar_Syntax_Syntax.binders; fields : (FStar_Ident.ident * FStar_Syntax_Syntax.typ) Prims.list; is_private_or_abstract : Prims.bool; is_record : Prims.bool}


let __proj__Mkrecord_or_dc__item__typename : record_or_dc  ->  FStar_Ident.lident = (fun projectee -> (match (projectee) with
| {typename = __fname__typename; constrname = __fname__constrname; parms = __fname__parms; fields = __fname__fields; is_private_or_abstract = __fname__is_private_or_abstract; is_record = __fname__is_record} -> begin
__fname__typename
end))


let __proj__Mkrecord_or_dc__item__constrname : record_or_dc  ->  FStar_Ident.ident = (fun projectee -> (match (projectee) with
| {typename = __fname__typename; constrname = __fname__constrname; parms = __fname__parms; fields = __fname__fields; is_private_or_abstract = __fname__is_private_or_abstract; is_record = __fname__is_record} -> begin
__fname__constrname
end))


let __proj__Mkrecord_or_dc__item__parms : record_or_dc  ->  FStar_Syntax_Syntax.binders = (fun projectee -> (match (projectee) with
| {typename = __fname__typename; constrname = __fname__constrname; parms = __fname__parms; fields = __fname__fields; is_private_or_abstract = __fname__is_private_or_abstract; is_record = __fname__is_record} -> begin
__fname__parms
end))


let __proj__Mkrecord_or_dc__item__fields : record_or_dc  ->  (FStar_Ident.ident * FStar_Syntax_Syntax.typ) Prims.list = (fun projectee -> (match (projectee) with
| {typename = __fname__typename; constrname = __fname__constrname; parms = __fname__parms; fields = __fname__fields; is_private_or_abstract = __fname__is_private_or_abstract; is_record = __fname__is_record} -> begin
__fname__fields
end))


let __proj__Mkrecord_or_dc__item__is_private_or_abstract : record_or_dc  ->  Prims.bool = (fun projectee -> (match (projectee) with
| {typename = __fname__typename; constrname = __fname__constrname; parms = __fname__parms; fields = __fname__fields; is_private_or_abstract = __fname__is_private_or_abstract; is_record = __fname__is_record} -> begin
__fname__is_private_or_abstract
end))


let __proj__Mkrecord_or_dc__item__is_record : record_or_dc  ->  Prims.bool = (fun projectee -> (match (projectee) with
| {typename = __fname__typename; constrname = __fname__constrname; parms = __fname__parms; fields = __fname__fields; is_private_or_abstract = __fname__is_private_or_abstract; is_record = __fname__is_record} -> begin
__fname__is_record
end))

type scope_mod =
| Local_binding of local_binding
| Rec_binding of rec_binding
| Module_abbrev of module_abbrev
| Open_module_or_namespace of open_module_or_namespace
| Top_level_def of FStar_Ident.ident
| Record_or_dc of record_or_dc


let uu___is_Local_binding : scope_mod  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Local_binding (_0) -> begin
true
end
| uu____198 -> begin
false
end))


let __proj__Local_binding__item___0 : scope_mod  ->  local_binding = (fun projectee -> (match (projectee) with
| Local_binding (_0) -> begin
_0
end))


let uu___is_Rec_binding : scope_mod  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Rec_binding (_0) -> begin
true
end
| uu____212 -> begin
false
end))


let __proj__Rec_binding__item___0 : scope_mod  ->  rec_binding = (fun projectee -> (match (projectee) with
| Rec_binding (_0) -> begin
_0
end))


let uu___is_Module_abbrev : scope_mod  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Module_abbrev (_0) -> begin
true
end
| uu____226 -> begin
false
end))


let __proj__Module_abbrev__item___0 : scope_mod  ->  module_abbrev = (fun projectee -> (match (projectee) with
| Module_abbrev (_0) -> begin
_0
end))


let uu___is_Open_module_or_namespace : scope_mod  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Open_module_or_namespace (_0) -> begin
true
end
| uu____240 -> begin
false
end))


let __proj__Open_module_or_namespace__item___0 : scope_mod  ->  open_module_or_namespace = (fun projectee -> (match (projectee) with
| Open_module_or_namespace (_0) -> begin
_0
end))


let uu___is_Top_level_def : scope_mod  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Top_level_def (_0) -> begin
true
end
| uu____254 -> begin
false
end))


let __proj__Top_level_def__item___0 : scope_mod  ->  FStar_Ident.ident = (fun projectee -> (match (projectee) with
| Top_level_def (_0) -> begin
_0
end))


let uu___is_Record_or_dc : scope_mod  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Record_or_dc (_0) -> begin
true
end
| uu____268 -> begin
false
end))


let __proj__Record_or_dc__item___0 : scope_mod  ->  record_or_dc = (fun projectee -> (match (projectee) with
| Record_or_dc (_0) -> begin
_0
end))


type string_set =
Prims.string FStar_Util.set

type exported_id_kind =
| Exported_id_term_type
| Exported_id_field


let uu___is_Exported_id_term_type : exported_id_kind  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Exported_id_term_type -> begin
true
end
| uu____283 -> begin
false
end))


let uu___is_Exported_id_field : exported_id_kind  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Exported_id_field -> begin
true
end
| uu____288 -> begin
false
end))


type exported_id_set =
exported_id_kind  ->  string_set FStar_ST.ref

type env =
{curmodule : FStar_Ident.lident FStar_Pervasives_Native.option; curmonad : FStar_Ident.ident FStar_Pervasives_Native.option; modules : (FStar_Ident.lident * FStar_Syntax_Syntax.modul) Prims.list; scope_mods : scope_mod Prims.list; exported_ids : exported_id_set FStar_Util.smap; trans_exported_ids : exported_id_set FStar_Util.smap; includes : FStar_Ident.lident Prims.list FStar_ST.ref FStar_Util.smap; sigaccum : FStar_Syntax_Syntax.sigelts; sigmap : (FStar_Syntax_Syntax.sigelt * Prims.bool) FStar_Util.smap; iface : Prims.bool; admitted_iface : Prims.bool; expect_typ : Prims.bool; docs : FStar_Parser_AST.fsdoc FStar_Util.smap; remaining_iface_decls : (FStar_Ident.lident * FStar_Parser_AST.decl Prims.list) Prims.list; syntax_only : Prims.bool; ds_hooks : dsenv_hooks} 
 and dsenv_hooks =
{ds_push_open_hook : env  ->  open_module_or_namespace  ->  Prims.unit; ds_push_include_hook : env  ->  FStar_Ident.lident  ->  Prims.unit; ds_push_module_abbrev_hook : env  ->  FStar_Ident.ident  ->  FStar_Ident.lident  ->  Prims.unit}


let __proj__Mkenv__item__curmodule : env  ->  FStar_Ident.lident FStar_Pervasives_Native.option = (fun projectee -> (match (projectee) with
| {curmodule = __fname__curmodule; curmonad = __fname__curmonad; modules = __fname__modules; scope_mods = __fname__scope_mods; exported_ids = __fname__exported_ids; trans_exported_ids = __fname__trans_exported_ids; includes = __fname__includes; sigaccum = __fname__sigaccum; sigmap = __fname__sigmap; iface = __fname__iface; admitted_iface = __fname__admitted_iface; expect_typ = __fname__expect_typ; docs = __fname__docs; remaining_iface_decls = __fname__remaining_iface_decls; syntax_only = __fname__syntax_only; ds_hooks = __fname__ds_hooks} -> begin
__fname__curmodule
end))


let __proj__Mkenv__item__curmonad : env  ->  FStar_Ident.ident FStar_Pervasives_Native.option = (fun projectee -> (match (projectee) with
| {curmodule = __fname__curmodule; curmonad = __fname__curmonad; modules = __fname__modules; scope_mods = __fname__scope_mods; exported_ids = __fname__exported_ids; trans_exported_ids = __fname__trans_exported_ids; includes = __fname__includes; sigaccum = __fname__sigaccum; sigmap = __fname__sigmap; iface = __fname__iface; admitted_iface = __fname__admitted_iface; expect_typ = __fname__expect_typ; docs = __fname__docs; remaining_iface_decls = __fname__remaining_iface_decls; syntax_only = __fname__syntax_only; ds_hooks = __fname__ds_hooks} -> begin
__fname__curmonad
end))


let __proj__Mkenv__item__modules : env  ->  (FStar_Ident.lident * FStar_Syntax_Syntax.modul) Prims.list = (fun projectee -> (match (projectee) with
| {curmodule = __fname__curmodule; curmonad = __fname__curmonad; modules = __fname__modules; scope_mods = __fname__scope_mods; exported_ids = __fname__exported_ids; trans_exported_ids = __fname__trans_exported_ids; includes = __fname__includes; sigaccum = __fname__sigaccum; sigmap = __fname__sigmap; iface = __fname__iface; admitted_iface = __fname__admitted_iface; expect_typ = __fname__expect_typ; docs = __fname__docs; remaining_iface_decls = __fname__remaining_iface_decls; syntax_only = __fname__syntax_only; ds_hooks = __fname__ds_hooks} -> begin
__fname__modules
end))


let __proj__Mkenv__item__scope_mods : env  ->  scope_mod Prims.list = (fun projectee -> (match (projectee) with
| {curmodule = __fname__curmodule; curmonad = __fname__curmonad; modules = __fname__modules; scope_mods = __fname__scope_mods; exported_ids = __fname__exported_ids; trans_exported_ids = __fname__trans_exported_ids; includes = __fname__includes; sigaccum = __fname__sigaccum; sigmap = __fname__sigmap; iface = __fname__iface; admitted_iface = __fname__admitted_iface; expect_typ = __fname__expect_typ; docs = __fname__docs; remaining_iface_decls = __fname__remaining_iface_decls; syntax_only = __fname__syntax_only; ds_hooks = __fname__ds_hooks} -> begin
__fname__scope_mods
end))


let __proj__Mkenv__item__exported_ids : env  ->  exported_id_set FStar_Util.smap = (fun projectee -> (match (projectee) with
| {curmodule = __fname__curmodule; curmonad = __fname__curmonad; modules = __fname__modules; scope_mods = __fname__scope_mods; exported_ids = __fname__exported_ids; trans_exported_ids = __fname__trans_exported_ids; includes = __fname__includes; sigaccum = __fname__sigaccum; sigmap = __fname__sigmap; iface = __fname__iface; admitted_iface = __fname__admitted_iface; expect_typ = __fname__expect_typ; docs = __fname__docs; remaining_iface_decls = __fname__remaining_iface_decls; syntax_only = __fname__syntax_only; ds_hooks = __fname__ds_hooks} -> begin
__fname__exported_ids
end))


let __proj__Mkenv__item__trans_exported_ids : env  ->  exported_id_set FStar_Util.smap = (fun projectee -> (match (projectee) with
| {curmodule = __fname__curmodule; curmonad = __fname__curmonad; modules = __fname__modules; scope_mods = __fname__scope_mods; exported_ids = __fname__exported_ids; trans_exported_ids = __fname__trans_exported_ids; includes = __fname__includes; sigaccum = __fname__sigaccum; sigmap = __fname__sigmap; iface = __fname__iface; admitted_iface = __fname__admitted_iface; expect_typ = __fname__expect_typ; docs = __fname__docs; remaining_iface_decls = __fname__remaining_iface_decls; syntax_only = __fname__syntax_only; ds_hooks = __fname__ds_hooks} -> begin
__fname__trans_exported_ids
end))


let __proj__Mkenv__item__includes : env  ->  FStar_Ident.lident Prims.list FStar_ST.ref FStar_Util.smap = (fun projectee -> (match (projectee) with
| {curmodule = __fname__curmodule; curmonad = __fname__curmonad; modules = __fname__modules; scope_mods = __fname__scope_mods; exported_ids = __fname__exported_ids; trans_exported_ids = __fname__trans_exported_ids; includes = __fname__includes; sigaccum = __fname__sigaccum; sigmap = __fname__sigmap; iface = __fname__iface; admitted_iface = __fname__admitted_iface; expect_typ = __fname__expect_typ; docs = __fname__docs; remaining_iface_decls = __fname__remaining_iface_decls; syntax_only = __fname__syntax_only; ds_hooks = __fname__ds_hooks} -> begin
__fname__includes
end))


let __proj__Mkenv__item__sigaccum : env  ->  FStar_Syntax_Syntax.sigelts = (fun projectee -> (match (projectee) with
| {curmodule = __fname__curmodule; curmonad = __fname__curmonad; modules = __fname__modules; scope_mods = __fname__scope_mods; exported_ids = __fname__exported_ids; trans_exported_ids = __fname__trans_exported_ids; includes = __fname__includes; sigaccum = __fname__sigaccum; sigmap = __fname__sigmap; iface = __fname__iface; admitted_iface = __fname__admitted_iface; expect_typ = __fname__expect_typ; docs = __fname__docs; remaining_iface_decls = __fname__remaining_iface_decls; syntax_only = __fname__syntax_only; ds_hooks = __fname__ds_hooks} -> begin
__fname__sigaccum
end))


let __proj__Mkenv__item__sigmap : env  ->  (FStar_Syntax_Syntax.sigelt * Prims.bool) FStar_Util.smap = (fun projectee -> (match (projectee) with
| {curmodule = __fname__curmodule; curmonad = __fname__curmonad; modules = __fname__modules; scope_mods = __fname__scope_mods; exported_ids = __fname__exported_ids; trans_exported_ids = __fname__trans_exported_ids; includes = __fname__includes; sigaccum = __fname__sigaccum; sigmap = __fname__sigmap; iface = __fname__iface; admitted_iface = __fname__admitted_iface; expect_typ = __fname__expect_typ; docs = __fname__docs; remaining_iface_decls = __fname__remaining_iface_decls; syntax_only = __fname__syntax_only; ds_hooks = __fname__ds_hooks} -> begin
__fname__sigmap
end))


let __proj__Mkenv__item__iface : env  ->  Prims.bool = (fun projectee -> (match (projectee) with
| {curmodule = __fname__curmodule; curmonad = __fname__curmonad; modules = __fname__modules; scope_mods = __fname__scope_mods; exported_ids = __fname__exported_ids; trans_exported_ids = __fname__trans_exported_ids; includes = __fname__includes; sigaccum = __fname__sigaccum; sigmap = __fname__sigmap; iface = __fname__iface; admitted_iface = __fname__admitted_iface; expect_typ = __fname__expect_typ; docs = __fname__docs; remaining_iface_decls = __fname__remaining_iface_decls; syntax_only = __fname__syntax_only; ds_hooks = __fname__ds_hooks} -> begin
__fname__iface
end))


let __proj__Mkenv__item__admitted_iface : env  ->  Prims.bool = (fun projectee -> (match (projectee) with
| {curmodule = __fname__curmodule; curmonad = __fname__curmonad; modules = __fname__modules; scope_mods = __fname__scope_mods; exported_ids = __fname__exported_ids; trans_exported_ids = __fname__trans_exported_ids; includes = __fname__includes; sigaccum = __fname__sigaccum; sigmap = __fname__sigmap; iface = __fname__iface; admitted_iface = __fname__admitted_iface; expect_typ = __fname__expect_typ; docs = __fname__docs; remaining_iface_decls = __fname__remaining_iface_decls; syntax_only = __fname__syntax_only; ds_hooks = __fname__ds_hooks} -> begin
__fname__admitted_iface
end))


let __proj__Mkenv__item__expect_typ : env  ->  Prims.bool = (fun projectee -> (match (projectee) with
| {curmodule = __fname__curmodule; curmonad = __fname__curmonad; modules = __fname__modules; scope_mods = __fname__scope_mods; exported_ids = __fname__exported_ids; trans_exported_ids = __fname__trans_exported_ids; includes = __fname__includes; sigaccum = __fname__sigaccum; sigmap = __fname__sigmap; iface = __fname__iface; admitted_iface = __fname__admitted_iface; expect_typ = __fname__expect_typ; docs = __fname__docs; remaining_iface_decls = __fname__remaining_iface_decls; syntax_only = __fname__syntax_only; ds_hooks = __fname__ds_hooks} -> begin
__fname__expect_typ
end))


let __proj__Mkenv__item__docs : env  ->  FStar_Parser_AST.fsdoc FStar_Util.smap = (fun projectee -> (match (projectee) with
| {curmodule = __fname__curmodule; curmonad = __fname__curmonad; modules = __fname__modules; scope_mods = __fname__scope_mods; exported_ids = __fname__exported_ids; trans_exported_ids = __fname__trans_exported_ids; includes = __fname__includes; sigaccum = __fname__sigaccum; sigmap = __fname__sigmap; iface = __fname__iface; admitted_iface = __fname__admitted_iface; expect_typ = __fname__expect_typ; docs = __fname__docs; remaining_iface_decls = __fname__remaining_iface_decls; syntax_only = __fname__syntax_only; ds_hooks = __fname__ds_hooks} -> begin
__fname__docs
end))


let __proj__Mkenv__item__remaining_iface_decls : env  ->  (FStar_Ident.lident * FStar_Parser_AST.decl Prims.list) Prims.list = (fun projectee -> (match (projectee) with
| {curmodule = __fname__curmodule; curmonad = __fname__curmonad; modules = __fname__modules; scope_mods = __fname__scope_mods; exported_ids = __fname__exported_ids; trans_exported_ids = __fname__trans_exported_ids; includes = __fname__includes; sigaccum = __fname__sigaccum; sigmap = __fname__sigmap; iface = __fname__iface; admitted_iface = __fname__admitted_iface; expect_typ = __fname__expect_typ; docs = __fname__docs; remaining_iface_decls = __fname__remaining_iface_decls; syntax_only = __fname__syntax_only; ds_hooks = __fname__ds_hooks} -> begin
__fname__remaining_iface_decls
end))


let __proj__Mkenv__item__syntax_only : env  ->  Prims.bool = (fun projectee -> (match (projectee) with
| {curmodule = __fname__curmodule; curmonad = __fname__curmonad; modules = __fname__modules; scope_mods = __fname__scope_mods; exported_ids = __fname__exported_ids; trans_exported_ids = __fname__trans_exported_ids; includes = __fname__includes; sigaccum = __fname__sigaccum; sigmap = __fname__sigmap; iface = __fname__iface; admitted_iface = __fname__admitted_iface; expect_typ = __fname__expect_typ; docs = __fname__docs; remaining_iface_decls = __fname__remaining_iface_decls; syntax_only = __fname__syntax_only; ds_hooks = __fname__ds_hooks} -> begin
__fname__syntax_only
end))


let __proj__Mkenv__item__ds_hooks : env  ->  dsenv_hooks = (fun projectee -> (match (projectee) with
| {curmodule = __fname__curmodule; curmonad = __fname__curmonad; modules = __fname__modules; scope_mods = __fname__scope_mods; exported_ids = __fname__exported_ids; trans_exported_ids = __fname__trans_exported_ids; includes = __fname__includes; sigaccum = __fname__sigaccum; sigmap = __fname__sigmap; iface = __fname__iface; admitted_iface = __fname__admitted_iface; expect_typ = __fname__expect_typ; docs = __fname__docs; remaining_iface_decls = __fname__remaining_iface_decls; syntax_only = __fname__syntax_only; ds_hooks = __fname__ds_hooks} -> begin
__fname__ds_hooks
end))


let __proj__Mkdsenv_hooks__item__ds_push_open_hook : dsenv_hooks  ->  env  ->  open_module_or_namespace  ->  Prims.unit = (fun projectee -> (match (projectee) with
| {ds_push_open_hook = __fname__ds_push_open_hook; ds_push_include_hook = __fname__ds_push_include_hook; ds_push_module_abbrev_hook = __fname__ds_push_module_abbrev_hook} -> begin
__fname__ds_push_open_hook
end))


let __proj__Mkdsenv_hooks__item__ds_push_include_hook : dsenv_hooks  ->  env  ->  FStar_Ident.lident  ->  Prims.unit = (fun projectee -> (match (projectee) with
| {ds_push_open_hook = __fname__ds_push_open_hook; ds_push_include_hook = __fname__ds_push_include_hook; ds_push_module_abbrev_hook = __fname__ds_push_module_abbrev_hook} -> begin
__fname__ds_push_include_hook
end))


let __proj__Mkdsenv_hooks__item__ds_push_module_abbrev_hook : dsenv_hooks  ->  env  ->  FStar_Ident.ident  ->  FStar_Ident.lident  ->  Prims.unit = (fun projectee -> (match (projectee) with
| {ds_push_open_hook = __fname__ds_push_open_hook; ds_push_include_hook = __fname__ds_push_include_hook; ds_push_module_abbrev_hook = __fname__ds_push_module_abbrev_hook} -> begin
__fname__ds_push_module_abbrev_hook
end))


let default_ds_hooks : dsenv_hooks = {ds_push_open_hook = (fun uu____1561 uu____1562 -> ()); ds_push_include_hook = (fun uu____1565 uu____1566 -> ()); ds_push_module_abbrev_hook = (fun uu____1570 uu____1571 uu____1572 -> ())}

type foundname =
| Term_name of (FStar_Syntax_Syntax.typ * Prims.bool)
| Eff_name of (FStar_Syntax_Syntax.sigelt * FStar_Ident.lident)


let uu___is_Term_name : foundname  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Term_name (_0) -> begin
true
end
| uu____1598 -> begin
false
end))


let __proj__Term_name__item___0 : foundname  ->  (FStar_Syntax_Syntax.typ * Prims.bool) = (fun projectee -> (match (projectee) with
| Term_name (_0) -> begin
_0
end))


let uu___is_Eff_name : foundname  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Eff_name (_0) -> begin
true
end
| uu____1628 -> begin
false
end))


let __proj__Eff_name__item___0 : foundname  ->  (FStar_Syntax_Syntax.sigelt * FStar_Ident.lident) = (fun projectee -> (match (projectee) with
| Eff_name (_0) -> begin
_0
end))


let set_iface : env  ->  Prims.bool  ->  env = (fun env b -> (

let uu___184_1657 = env
in {curmodule = uu___184_1657.curmodule; curmonad = uu___184_1657.curmonad; modules = uu___184_1657.modules; scope_mods = uu___184_1657.scope_mods; exported_ids = uu___184_1657.exported_ids; trans_exported_ids = uu___184_1657.trans_exported_ids; includes = uu___184_1657.includes; sigaccum = uu___184_1657.sigaccum; sigmap = uu___184_1657.sigmap; iface = b; admitted_iface = uu___184_1657.admitted_iface; expect_typ = uu___184_1657.expect_typ; docs = uu___184_1657.docs; remaining_iface_decls = uu___184_1657.remaining_iface_decls; syntax_only = uu___184_1657.syntax_only; ds_hooks = uu___184_1657.ds_hooks}))


let iface : env  ->  Prims.bool = (fun e -> e.iface)


let set_admitted_iface : env  ->  Prims.bool  ->  env = (fun e b -> (

let uu___185_1670 = e
in {curmodule = uu___185_1670.curmodule; curmonad = uu___185_1670.curmonad; modules = uu___185_1670.modules; scope_mods = uu___185_1670.scope_mods; exported_ids = uu___185_1670.exported_ids; trans_exported_ids = uu___185_1670.trans_exported_ids; includes = uu___185_1670.includes; sigaccum = uu___185_1670.sigaccum; sigmap = uu___185_1670.sigmap; iface = uu___185_1670.iface; admitted_iface = b; expect_typ = uu___185_1670.expect_typ; docs = uu___185_1670.docs; remaining_iface_decls = uu___185_1670.remaining_iface_decls; syntax_only = uu___185_1670.syntax_only; ds_hooks = uu___185_1670.ds_hooks}))


let admitted_iface : env  ->  Prims.bool = (fun e -> e.admitted_iface)


let set_expect_typ : env  ->  Prims.bool  ->  env = (fun e b -> (

let uu___186_1683 = e
in {curmodule = uu___186_1683.curmodule; curmonad = uu___186_1683.curmonad; modules = uu___186_1683.modules; scope_mods = uu___186_1683.scope_mods; exported_ids = uu___186_1683.exported_ids; trans_exported_ids = uu___186_1683.trans_exported_ids; includes = uu___186_1683.includes; sigaccum = uu___186_1683.sigaccum; sigmap = uu___186_1683.sigmap; iface = uu___186_1683.iface; admitted_iface = uu___186_1683.admitted_iface; expect_typ = b; docs = uu___186_1683.docs; remaining_iface_decls = uu___186_1683.remaining_iface_decls; syntax_only = uu___186_1683.syntax_only; ds_hooks = uu___186_1683.ds_hooks}))


let expect_typ : env  ->  Prims.bool = (fun e -> e.expect_typ)


let all_exported_id_kinds : exported_id_kind Prims.list = (Exported_id_field)::(Exported_id_term_type)::[]


let transitive_exported_ids : env  ->  FStar_Ident.lident  ->  Prims.string Prims.list = (fun env lid -> (

let module_name = (FStar_Ident.string_of_lid lid)
in (

let uu____1701 = (FStar_Util.smap_try_find env.trans_exported_ids module_name)
in (match (uu____1701) with
| FStar_Pervasives_Native.None -> begin
[]
end
| FStar_Pervasives_Native.Some (exported_id_set) -> begin
(

let uu____1707 = (

let uu____1708 = (exported_id_set Exported_id_term_type)
in (FStar_ST.op_Bang uu____1708))
in (FStar_All.pipe_right uu____1707 FStar_Util.set_elements))
end))))


let open_modules : env  ->  (FStar_Ident.lident * FStar_Syntax_Syntax.modul) Prims.list = (fun e -> e.modules)


let open_modules_and_namespaces : env  ->  FStar_Ident.lident Prims.list = (fun env -> (FStar_List.filter_map (fun uu___153_1973 -> (match (uu___153_1973) with
| Open_module_or_namespace (lid, _info) -> begin
FStar_Pervasives_Native.Some (lid)
end
| uu____1978 -> begin
FStar_Pervasives_Native.None
end)) env.scope_mods))


let set_current_module : env  ->  FStar_Ident.lident  ->  env = (fun e l -> (

let uu___187_1987 = e
in {curmodule = FStar_Pervasives_Native.Some (l); curmonad = uu___187_1987.curmonad; modules = uu___187_1987.modules; scope_mods = uu___187_1987.scope_mods; exported_ids = uu___187_1987.exported_ids; trans_exported_ids = uu___187_1987.trans_exported_ids; includes = uu___187_1987.includes; sigaccum = uu___187_1987.sigaccum; sigmap = uu___187_1987.sigmap; iface = uu___187_1987.iface; admitted_iface = uu___187_1987.admitted_iface; expect_typ = uu___187_1987.expect_typ; docs = uu___187_1987.docs; remaining_iface_decls = uu___187_1987.remaining_iface_decls; syntax_only = uu___187_1987.syntax_only; ds_hooks = uu___187_1987.ds_hooks}))


let current_module : env  ->  FStar_Ident.lident = (fun env -> (match (env.curmodule) with
| FStar_Pervasives_Native.None -> begin
(failwith "Unset current module")
end
| FStar_Pervasives_Native.Some (m) -> begin
m
end))


let iface_decls : env  ->  FStar_Ident.lident  ->  FStar_Parser_AST.decl Prims.list FStar_Pervasives_Native.option = (fun env l -> (

let uu____2005 = (FStar_All.pipe_right env.remaining_iface_decls (FStar_List.tryFind (fun uu____2039 -> (match (uu____2039) with
| (m, uu____2047) -> begin
(FStar_Ident.lid_equals l m)
end))))
in (match (uu____2005) with
| FStar_Pervasives_Native.None -> begin
FStar_Pervasives_Native.None
end
| FStar_Pervasives_Native.Some (uu____2064, decls) -> begin
FStar_Pervasives_Native.Some (decls)
end)))


let set_iface_decls : env  ->  FStar_Ident.lident  ->  FStar_Parser_AST.decl Prims.list  ->  env = (fun env l ds -> (

let uu____2094 = (FStar_List.partition (fun uu____2124 -> (match (uu____2124) with
| (m, uu____2132) -> begin
(FStar_Ident.lid_equals l m)
end)) env.remaining_iface_decls)
in (match (uu____2094) with
| (uu____2137, rest) -> begin
(

let uu___188_2171 = env
in {curmodule = uu___188_2171.curmodule; curmonad = uu___188_2171.curmonad; modules = uu___188_2171.modules; scope_mods = uu___188_2171.scope_mods; exported_ids = uu___188_2171.exported_ids; trans_exported_ids = uu___188_2171.trans_exported_ids; includes = uu___188_2171.includes; sigaccum = uu___188_2171.sigaccum; sigmap = uu___188_2171.sigmap; iface = uu___188_2171.iface; admitted_iface = uu___188_2171.admitted_iface; expect_typ = uu___188_2171.expect_typ; docs = uu___188_2171.docs; remaining_iface_decls = (((l), (ds)))::rest; syntax_only = uu___188_2171.syntax_only; ds_hooks = uu___188_2171.ds_hooks})
end)))


let qual : FStar_Ident.lident  ->  FStar_Ident.ident  ->  FStar_Ident.lident = FStar_Syntax_Util.qual_id


let qualify : env  ->  FStar_Ident.ident  ->  FStar_Ident.lident = (fun env id -> (match (env.curmonad) with
| FStar_Pervasives_Native.None -> begin
(

let uu____2194 = (current_module env)
in (qual uu____2194 id))
end
| FStar_Pervasives_Native.Some (monad) -> begin
(

let uu____2196 = (

let uu____2197 = (current_module env)
in (qual uu____2197 monad))
in (FStar_Syntax_Util.mk_field_projector_name_from_ident uu____2196 id))
end))


let syntax_only : env  ->  Prims.bool = (fun env -> env.syntax_only)


let set_syntax_only : env  ->  Prims.bool  ->  env = (fun env b -> (

let uu___189_2210 = env
in {curmodule = uu___189_2210.curmodule; curmonad = uu___189_2210.curmonad; modules = uu___189_2210.modules; scope_mods = uu___189_2210.scope_mods; exported_ids = uu___189_2210.exported_ids; trans_exported_ids = uu___189_2210.trans_exported_ids; includes = uu___189_2210.includes; sigaccum = uu___189_2210.sigaccum; sigmap = uu___189_2210.sigmap; iface = uu___189_2210.iface; admitted_iface = uu___189_2210.admitted_iface; expect_typ = uu___189_2210.expect_typ; docs = uu___189_2210.docs; remaining_iface_decls = uu___189_2210.remaining_iface_decls; syntax_only = b; ds_hooks = uu___189_2210.ds_hooks}))


let ds_hooks : env  ->  dsenv_hooks = (fun env -> env.ds_hooks)


let set_ds_hooks : env  ->  dsenv_hooks  ->  env = (fun env hooks -> (

let uu___190_2223 = env
in {curmodule = uu___190_2223.curmodule; curmonad = uu___190_2223.curmonad; modules = uu___190_2223.modules; scope_mods = uu___190_2223.scope_mods; exported_ids = uu___190_2223.exported_ids; trans_exported_ids = uu___190_2223.trans_exported_ids; includes = uu___190_2223.includes; sigaccum = uu___190_2223.sigaccum; sigmap = uu___190_2223.sigmap; iface = uu___190_2223.iface; admitted_iface = uu___190_2223.admitted_iface; expect_typ = uu___190_2223.expect_typ; docs = uu___190_2223.docs; remaining_iface_decls = uu___190_2223.remaining_iface_decls; syntax_only = uu___190_2223.syntax_only; ds_hooks = hooks}))


let new_sigmap : 'Auu____2228 . Prims.unit  ->  'Auu____2228 FStar_Util.smap = (fun uu____2234 -> (FStar_Util.smap_create (Prims.parse_int "100")))


let empty_env : Prims.unit  ->  env = (fun uu____2238 -> (

let uu____2239 = (new_sigmap ())
in (

let uu____2242 = (new_sigmap ())
in (

let uu____2245 = (new_sigmap ())
in (

let uu____2256 = (new_sigmap ())
in (

let uu____2267 = (new_sigmap ())
in {curmodule = FStar_Pervasives_Native.None; curmonad = FStar_Pervasives_Native.None; modules = []; scope_mods = []; exported_ids = uu____2239; trans_exported_ids = uu____2242; includes = uu____2245; sigaccum = []; sigmap = uu____2256; iface = false; admitted_iface = false; expect_typ = false; docs = uu____2267; remaining_iface_decls = []; syntax_only = false; ds_hooks = default_ds_hooks}))))))


let sigmap : env  ->  (FStar_Syntax_Syntax.sigelt * Prims.bool) FStar_Util.smap = (fun env -> env.sigmap)


let has_all_in_scope : env  ->  Prims.bool = (fun env -> (FStar_List.existsb (fun uu____2301 -> (match (uu____2301) with
| (m, uu____2307) -> begin
(FStar_Ident.lid_equals m FStar_Parser_Const.all_lid)
end)) env.modules))


let set_bv_range : FStar_Syntax_Syntax.bv  ->  FStar_Range.range  ->  FStar_Syntax_Syntax.bv = (fun bv r -> (

let id = (

let uu___191_2317 = bv.FStar_Syntax_Syntax.ppname
in {FStar_Ident.idText = uu___191_2317.FStar_Ident.idText; FStar_Ident.idRange = r})
in (

let uu___192_2318 = bv
in {FStar_Syntax_Syntax.ppname = id; FStar_Syntax_Syntax.index = uu___192_2318.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = uu___192_2318.FStar_Syntax_Syntax.sort})))


let bv_to_name : FStar_Syntax_Syntax.bv  ->  FStar_Range.range  ->  FStar_Syntax_Syntax.term = (fun bv r -> (FStar_Syntax_Syntax.bv_to_name (set_bv_range bv r)))


let unmangleMap : (Prims.string * Prims.string * FStar_Syntax_Syntax.delta_depth * FStar_Syntax_Syntax.fv_qual FStar_Pervasives_Native.option) Prims.list = ((("op_ColonColon"), ("Cons"), (FStar_Syntax_Syntax.Delta_constant), (FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Data_ctor))))::((("not"), ("op_Negation"), (FStar_Syntax_Syntax.Delta_equational), (FStar_Pervasives_Native.None)))::[]


let unmangleOpName : FStar_Ident.ident  ->  (FStar_Syntax_Syntax.term * Prims.bool) FStar_Pervasives_Native.option = (fun id -> (

let t = (FStar_Util.find_map unmangleMap (fun uu____2408 -> (match (uu____2408) with
| (x, y, dd, dq) -> begin
(match ((Prims.op_Equality id.FStar_Ident.idText x)) with
| true -> begin
(

let uu____2431 = (

let uu____2432 = (FStar_Ident.lid_of_path (("Prims")::(y)::[]) id.FStar_Ident.idRange)
in (FStar_Syntax_Syntax.fvar uu____2432 dd dq))
in FStar_Pervasives_Native.Some (uu____2431))
end
| uu____2433 -> begin
FStar_Pervasives_Native.None
end)
end)))
in (match (t) with
| FStar_Pervasives_Native.Some (v1) -> begin
FStar_Pervasives_Native.Some (((v1), (false)))
end
| FStar_Pervasives_Native.None -> begin
FStar_Pervasives_Native.None
end)))

type 'a cont_t =
| Cont_ok of 'a
| Cont_fail
| Cont_ignore


let uu___is_Cont_ok : 'a . 'a cont_t  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Cont_ok (_0) -> begin
true
end
| uu____2477 -> begin
false
end))


let __proj__Cont_ok__item___0 : 'a . 'a cont_t  ->  'a = (fun projectee -> (match (projectee) with
| Cont_ok (_0) -> begin
_0
end))


let uu___is_Cont_fail : 'a . 'a cont_t  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Cont_fail -> begin
true
end
| uu____2510 -> begin
false
end))


let uu___is_Cont_ignore : 'a . 'a cont_t  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Cont_ignore -> begin
true
end
| uu____2526 -> begin
false
end))


let option_of_cont : 'a . (Prims.unit  ->  'a FStar_Pervasives_Native.option)  ->  'a cont_t  ->  'a FStar_Pervasives_Native.option = (fun k_ignore uu___154_2552 -> (match (uu___154_2552) with
| Cont_ok (a) -> begin
FStar_Pervasives_Native.Some (a)
end
| Cont_fail -> begin
FStar_Pervasives_Native.None
end
| Cont_ignore -> begin
(k_ignore ())
end))


let find_in_record : 'Auu____2570 . FStar_Ident.ident Prims.list  ->  FStar_Ident.ident  ->  record_or_dc  ->  (record_or_dc  ->  'Auu____2570 cont_t)  ->  'Auu____2570 cont_t = (fun ns id record cont -> (

let typename' = (FStar_Ident.lid_of_ids (FStar_List.append ns ((record.typename.FStar_Ident.ident)::[])))
in (match ((FStar_Ident.lid_equals typename' record.typename)) with
| true -> begin
(

let fname = (FStar_Ident.lid_of_ids (FStar_List.append record.typename.FStar_Ident.ns ((id)::[])))
in (

let find1 = (FStar_Util.find_map record.fields (fun uu____2616 -> (match (uu____2616) with
| (f, uu____2624) -> begin
(match ((Prims.op_Equality id.FStar_Ident.idText f.FStar_Ident.idText)) with
| true -> begin
FStar_Pervasives_Native.Some (record)
end
| uu____2627 -> begin
FStar_Pervasives_Native.None
end)
end)))
in (match (find1) with
| FStar_Pervasives_Native.Some (r) -> begin
(cont r)
end
| FStar_Pervasives_Native.None -> begin
Cont_ignore
end)))
end
| uu____2631 -> begin
Cont_ignore
end)))


let get_exported_id_set : env  ->  Prims.string  ->  (exported_id_kind  ->  string_set FStar_ST.ref) FStar_Pervasives_Native.option = (fun e mname -> (FStar_Util.smap_try_find e.exported_ids mname))


let get_trans_exported_id_set : env  ->  Prims.string  ->  (exported_id_kind  ->  string_set FStar_ST.ref) FStar_Pervasives_Native.option = (fun e mname -> (FStar_Util.smap_try_find e.trans_exported_ids mname))


let string_of_exported_id_kind : exported_id_kind  ->  Prims.string = (fun uu___155_2675 -> (match (uu___155_2675) with
| Exported_id_field -> begin
"field"
end
| Exported_id_term_type -> begin
"term/type"
end))


let find_in_module_with_includes : 'a . exported_id_kind  ->  (FStar_Ident.lident  ->  'a cont_t)  ->  'a cont_t  ->  env  ->  FStar_Ident.lident  ->  FStar_Ident.ident  ->  'a cont_t = (fun eikind find_in_module find_in_module_default env ns id -> (

let idstr = id.FStar_Ident.idText
in (

let rec aux = (fun uu___156_2738 -> (match (uu___156_2738) with
| [] -> begin
find_in_module_default
end
| (modul)::q -> begin
(

let mname = modul.FStar_Ident.str
in (

let not_shadowed = (

let uu____2749 = (get_exported_id_set env mname)
in (match (uu____2749) with
| FStar_Pervasives_Native.None -> begin
true
end
| FStar_Pervasives_Native.Some (mex) -> begin
(

let mexports = (

let uu____2770 = (mex eikind)
in (FStar_ST.op_Bang uu____2770))
in (FStar_Util.set_mem idstr mexports))
end))
in (

let mincludes = (

let uu____3017 = (FStar_Util.smap_try_find env.includes mname)
in (match (uu____3017) with
| FStar_Pervasives_Native.None -> begin
[]
end
| FStar_Pervasives_Native.Some (minc) -> begin
(FStar_ST.op_Bang minc)
end))
in (

let look_into = (match (not_shadowed) with
| true -> begin
(

let uu____3112 = (qual modul id)
in (find_in_module uu____3112))
end
| uu____3113 -> begin
Cont_ignore
end)
in (match (look_into) with
| Cont_ignore -> begin
(aux (FStar_List.append mincludes q))
end
| uu____3116 -> begin
look_into
end)))))
end))
in (aux ((ns)::[])))))


let is_exported_id_field : exported_id_kind  ->  Prims.bool = (fun uu___157_3122 -> (match (uu___157_3122) with
| Exported_id_field -> begin
true
end
| uu____3123 -> begin
false
end))


let try_lookup_id'' : 'a . env  ->  FStar_Ident.ident  ->  exported_id_kind  ->  (local_binding  ->  'a cont_t)  ->  (rec_binding  ->  'a cont_t)  ->  (record_or_dc  ->  'a cont_t)  ->  (FStar_Ident.lident  ->  'a cont_t)  ->  ('a cont_t  ->  FStar_Ident.ident  ->  'a cont_t)  ->  'a FStar_Pervasives_Native.option = (fun env id eikind k_local_binding k_rec_binding k_record find_in_module lookup_default_id -> (

let check_local_binding_id = (fun uu___158_3234 -> (match (uu___158_3234) with
| (id', uu____3236, uu____3237) -> begin
(Prims.op_Equality id'.FStar_Ident.idText id.FStar_Ident.idText)
end))
in (

let check_rec_binding_id = (fun uu___159_3241 -> (match (uu___159_3241) with
| (id', uu____3243, uu____3244) -> begin
(Prims.op_Equality id'.FStar_Ident.idText id.FStar_Ident.idText)
end))
in (

let curmod_ns = (

let uu____3248 = (current_module env)
in (FStar_Ident.ids_of_lid uu____3248))
in (

let proc = (fun uu___160_3254 -> (match (uu___160_3254) with
| Local_binding (l) when (check_local_binding_id l) -> begin
(k_local_binding l)
end
| Rec_binding (r) when (check_rec_binding_id r) -> begin
(k_rec_binding r)
end
| Open_module_or_namespace (ns, Open_module) -> begin
(find_in_module_with_includes eikind find_in_module Cont_ignore env ns id)
end
| Top_level_def (id') when (Prims.op_Equality id'.FStar_Ident.idText id.FStar_Ident.idText) -> begin
(lookup_default_id Cont_ignore id)
end
| Record_or_dc (r) when (is_exported_id_field eikind) -> begin
(

let uu____3262 = (FStar_Ident.lid_of_ids curmod_ns)
in (find_in_module_with_includes Exported_id_field (fun lid -> (

let id1 = lid.FStar_Ident.ident
in (find_in_record lid.FStar_Ident.ns id1 r k_record))) Cont_ignore env uu____3262 id))
end
| uu____3267 -> begin
Cont_ignore
end))
in (

let rec aux = (fun uu___161_3275 -> (match (uu___161_3275) with
| (a)::q -> begin
(

let uu____3284 = (proc a)
in (option_of_cont (fun uu____3288 -> (aux q)) uu____3284))
end
| [] -> begin
(

let uu____3289 = (lookup_default_id Cont_fail id)
in (option_of_cont (fun uu____3293 -> FStar_Pervasives_Native.None) uu____3289))
end))
in (aux env.scope_mods)))))))


let found_local_binding : 'Auu____3302 'Auu____3303 . FStar_Range.range  ->  ('Auu____3303 * FStar_Syntax_Syntax.bv * 'Auu____3302)  ->  (FStar_Syntax_Syntax.term * 'Auu____3302) = (fun r uu____3321 -> (match (uu____3321) with
| (id', x, mut) -> begin
(

let uu____3331 = (bv_to_name x r)
in ((uu____3331), (mut)))
end))


let find_in_module : 'Auu____3342 . env  ->  FStar_Ident.lident  ->  (FStar_Ident.lident  ->  (FStar_Syntax_Syntax.sigelt * Prims.bool)  ->  'Auu____3342)  ->  'Auu____3342  ->  'Auu____3342 = (fun env lid k_global_def k_not_found -> (

let uu____3377 = (FStar_Util.smap_try_find (sigmap env) lid.FStar_Ident.str)
in (match (uu____3377) with
| FStar_Pervasives_Native.Some (sb) -> begin
(k_global_def lid sb)
end
| FStar_Pervasives_Native.None -> begin
k_not_found
end)))


let try_lookup_id : env  ->  FStar_Ident.ident  ->  (FStar_Syntax_Syntax.term * Prims.bool) FStar_Pervasives_Native.option = (fun env id -> (

let uu____3415 = (unmangleOpName id)
in (match (uu____3415) with
| FStar_Pervasives_Native.Some (f) -> begin
FStar_Pervasives_Native.Some (f)
end
| uu____3441 -> begin
(try_lookup_id'' env id Exported_id_term_type (fun r -> (

let uu____3455 = (found_local_binding id.FStar_Ident.idRange r)
in Cont_ok (uu____3455))) (fun uu____3465 -> Cont_fail) (fun uu____3471 -> Cont_ignore) (fun i -> (find_in_module env i (fun uu____3486 uu____3487 -> Cont_fail) Cont_ignore)) (fun uu____3502 uu____3503 -> Cont_fail))
end)))


let lookup_default_id : 'a . env  ->  FStar_Ident.ident  ->  (FStar_Ident.lident  ->  (FStar_Syntax_Syntax.sigelt * Prims.bool)  ->  'a cont_t)  ->  'a cont_t  ->  'a cont_t = (fun env id k_global_def k_not_found -> (

let find_in_monad = (match (env.curmonad) with
| FStar_Pervasives_Native.Some (uu____3578) -> begin
(

let lid = (qualify env id)
in (

let uu____3580 = (FStar_Util.smap_try_find (sigmap env) lid.FStar_Ident.str)
in (match (uu____3580) with
| FStar_Pervasives_Native.Some (r) -> begin
(

let uu____3604 = (k_global_def lid r)
in FStar_Pervasives_Native.Some (uu____3604))
end
| FStar_Pervasives_Native.None -> begin
FStar_Pervasives_Native.None
end)))
end
| FStar_Pervasives_Native.None -> begin
FStar_Pervasives_Native.None
end)
in (match (find_in_monad) with
| FStar_Pervasives_Native.Some (v1) -> begin
v1
end
| FStar_Pervasives_Native.None -> begin
(

let lid = (

let uu____3627 = (current_module env)
in (qual uu____3627 id))
in (find_in_module env lid k_global_def k_not_found))
end)))


let module_is_defined : env  ->  FStar_Ident.lident  ->  Prims.bool = (fun env lid -> ((match (env.curmodule) with
| FStar_Pervasives_Native.None -> begin
false
end
| FStar_Pervasives_Native.Some (m) -> begin
(

let uu____3639 = (current_module env)
in (FStar_Ident.lid_equals lid uu____3639))
end) || (FStar_List.existsb (fun x -> (FStar_Ident.lid_equals lid (FStar_Pervasives_Native.fst x))) env.modules)))


let resolve_module_name : env  ->  FStar_Ident.lident  ->  Prims.bool  ->  FStar_Ident.lident FStar_Pervasives_Native.option = (fun env lid honor_ns -> (

let nslen = (FStar_List.length lid.FStar_Ident.ns)
in (

let rec aux = (fun uu___162_3674 -> (match (uu___162_3674) with
| [] -> begin
(

let uu____3679 = (module_is_defined env lid)
in (match (uu____3679) with
| true -> begin
FStar_Pervasives_Native.Some (lid)
end
| uu____3682 -> begin
FStar_Pervasives_Native.None
end))
end
| (Open_module_or_namespace (ns, Open_namespace))::q when honor_ns -> begin
(

let new_lid = (

let uu____3688 = (

let uu____3691 = (FStar_Ident.path_of_lid ns)
in (

let uu____3694 = (FStar_Ident.path_of_lid lid)
in (FStar_List.append uu____3691 uu____3694)))
in (FStar_Ident.lid_of_path uu____3688 (FStar_Ident.range_of_lid lid)))
in (

let uu____3697 = (module_is_defined env new_lid)
in (match (uu____3697) with
| true -> begin
FStar_Pervasives_Native.Some (new_lid)
end
| uu____3700 -> begin
(aux q)
end)))
end
| (Module_abbrev (name, modul))::uu____3703 when ((Prims.op_Equality nslen (Prims.parse_int "0")) && (Prims.op_Equality name.FStar_Ident.idText lid.FStar_Ident.ident.FStar_Ident.idText)) -> begin
FStar_Pervasives_Native.Some (modul)
end
| (uu____3710)::q -> begin
(aux q)
end))
in (aux env.scope_mods))))


let fail_if_curmodule : env  ->  FStar_Ident.lident  ->  FStar_Ident.lident  ->  Prims.unit = (fun env ns_original ns_resolved -> (

let uu____3726 = (

let uu____3727 = (current_module env)
in (FStar_Ident.lid_equals ns_resolved uu____3727))
in (match (uu____3726) with
| true -> begin
(match ((FStar_Ident.lid_equals ns_resolved FStar_Parser_Const.prims_lid)) with
| true -> begin
()
end
| uu____3728 -> begin
(

let uu____3729 = (

let uu____3730 = (

let uu____3735 = (FStar_Util.format1 "Reference %s to current module is forbidden (see GitHub issue #451)" ns_original.FStar_Ident.str)
in ((uu____3735), ((FStar_Ident.range_of_lid ns_original))))
in FStar_Errors.Error (uu____3730))
in (FStar_Exn.raise uu____3729))
end)
end
| uu____3736 -> begin
()
end)))


let fail_if_qualified_by_curmodule : env  ->  FStar_Ident.lident  ->  Prims.unit = (fun env lid -> (match (lid.FStar_Ident.ns) with
| [] -> begin
()
end
| uu____3745 -> begin
(

let modul_orig = (FStar_Ident.lid_of_ids lid.FStar_Ident.ns)
in (

let uu____3749 = (resolve_module_name env modul_orig true)
in (match (uu____3749) with
| FStar_Pervasives_Native.Some (modul_res) -> begin
(fail_if_curmodule env modul_orig modul_res)
end
| uu____3753 -> begin
()
end)))
end))


let namespace_is_open : env  ->  FStar_Ident.lident  ->  Prims.bool = (fun env lid -> (FStar_List.existsb (fun uu___163_3766 -> (match (uu___163_3766) with
| Open_module_or_namespace (ns, Open_namespace) -> begin
(FStar_Ident.lid_equals lid ns)
end
| uu____3768 -> begin
false
end)) env.scope_mods))


let shorten_module_path : env  ->  FStar_Ident.ident Prims.list  ->  Prims.bool  ->  (FStar_Ident.ident Prims.list * FStar_Ident.ident Prims.list) = (fun env ids is_full_path -> (

let rec aux = (fun revns id -> (

let lid = (FStar_Ident.lid_of_ns_and_id (FStar_List.rev revns) id)
in (match ((namespace_is_open env lid)) with
| true -> begin
FStar_Pervasives_Native.Some ((((FStar_List.rev ((id)::revns))), ([])))
end
| uu____3837 -> begin
(match (revns) with
| [] -> begin
FStar_Pervasives_Native.None
end
| (ns_last_id)::rev_ns_prefix -> begin
(

let uu____3860 = (aux rev_ns_prefix ns_last_id)
in (FStar_All.pipe_right uu____3860 (FStar_Util.map_option (fun uu____3910 -> (match (uu____3910) with
| (stripped_ids, rev_kept_ids) -> begin
((stripped_ids), ((id)::rev_kept_ids))
end)))))
end)
end)))
in (

let uu____3941 = (is_full_path && (

let uu____3943 = (FStar_Ident.lid_of_ids ids)
in (module_is_defined env uu____3943)))
in (match (uu____3941) with
| true -> begin
((ids), ([]))
end
| uu____3956 -> begin
(match ((FStar_List.rev ids)) with
| [] -> begin
(([]), ([]))
end
| (ns_last_id)::ns_rev_prefix -> begin
(

let uu____3973 = (aux ns_rev_prefix ns_last_id)
in (match (uu____3973) with
| FStar_Pervasives_Native.None -> begin
(([]), (ids))
end
| FStar_Pervasives_Native.Some (stripped_ids, rev_kept_ids) -> begin
((stripped_ids), ((FStar_List.rev rev_kept_ids)))
end))
end)
end))))


let shorten_lid : env  ->  FStar_Ident.lid  ->  FStar_Ident.lid = (fun env lid -> (

let uu____4034 = (shorten_module_path env lid.FStar_Ident.ns true)
in (match (uu____4034) with
| (uu____4043, short) -> begin
(FStar_Ident.lid_of_ns_and_id short lid.FStar_Ident.ident)
end)))


let resolve_in_open_namespaces'' : 'a . env  ->  FStar_Ident.lident  ->  exported_id_kind  ->  (local_binding  ->  'a cont_t)  ->  (rec_binding  ->  'a cont_t)  ->  (record_or_dc  ->  'a cont_t)  ->  (FStar_Ident.lident  ->  'a cont_t)  ->  ('a cont_t  ->  FStar_Ident.ident  ->  'a cont_t)  ->  'a FStar_Pervasives_Native.option = (fun env lid eikind k_local_binding k_rec_binding k_record f_module l_default -> (match (lid.FStar_Ident.ns) with
| (uu____4160)::uu____4161 -> begin
(

let uu____4164 = (

let uu____4167 = (

let uu____4168 = (FStar_Ident.lid_of_ids lid.FStar_Ident.ns)
in (FStar_Ident.set_lid_range uu____4168 (FStar_Ident.range_of_lid lid)))
in (resolve_module_name env uu____4167 true))
in (match (uu____4164) with
| FStar_Pervasives_Native.None -> begin
FStar_Pervasives_Native.None
end
| FStar_Pervasives_Native.Some (modul) -> begin
(

let uu____4172 = (find_in_module_with_includes eikind f_module Cont_fail env modul lid.FStar_Ident.ident)
in (option_of_cont (fun uu____4176 -> FStar_Pervasives_Native.None) uu____4172))
end))
end
| [] -> begin
(try_lookup_id'' env lid.FStar_Ident.ident eikind k_local_binding k_rec_binding k_record f_module l_default)
end))


let cont_of_option : 'a . 'a cont_t  ->  'a FStar_Pervasives_Native.option  ->  'a cont_t = (fun k_none uu___164_4197 -> (match (uu___164_4197) with
| FStar_Pervasives_Native.Some (v1) -> begin
Cont_ok (v1)
end
| FStar_Pervasives_Native.None -> begin
k_none
end))


let resolve_in_open_namespaces' : 'a . env  ->  FStar_Ident.lident  ->  (local_binding  ->  'a FStar_Pervasives_Native.option)  ->  (rec_binding  ->  'a FStar_Pervasives_Native.option)  ->  (FStar_Ident.lident  ->  (FStar_Syntax_Syntax.sigelt * Prims.bool)  ->  'a FStar_Pervasives_Native.option)  ->  'a FStar_Pervasives_Native.option = (fun env lid k_local_binding k_rec_binding k_global_def -> (

let k_global_def' = (fun k lid1 def -> (

let uu____4302 = (k_global_def lid1 def)
in (cont_of_option k uu____4302)))
in (

let f_module = (fun lid' -> (

let k = Cont_ignore
in (find_in_module env lid' (k_global_def' k) k)))
in (

let l_default = (fun k i -> (lookup_default_id env i (k_global_def' k) k))
in (resolve_in_open_namespaces'' env lid Exported_id_term_type (fun l -> (

let uu____4332 = (k_local_binding l)
in (cont_of_option Cont_fail uu____4332))) (fun r -> (

let uu____4338 = (k_rec_binding r)
in (cont_of_option Cont_fail uu____4338))) (fun uu____4342 -> Cont_ignore) f_module l_default)))))


let fv_qual_of_se : FStar_Syntax_Syntax.sigelt  ->  FStar_Syntax_Syntax.fv_qual FStar_Pervasives_Native.option = (fun se -> (match (se.FStar_Syntax_Syntax.sigel) with
| FStar_Syntax_Syntax.Sig_datacon (uu____4351, uu____4352, uu____4353, l, uu____4355, uu____4356) -> begin
(

let qopt = (FStar_Util.find_map se.FStar_Syntax_Syntax.sigquals (fun uu___165_4367 -> (match (uu___165_4367) with
| FStar_Syntax_Syntax.RecordConstructor (uu____4370, fs) -> begin
FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Record_ctor (((l), (fs))))
end
| uu____4382 -> begin
FStar_Pervasives_Native.None
end)))
in (match (qopt) with
| FStar_Pervasives_Native.None -> begin
FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Data_ctor)
end
| x -> begin
x
end))
end
| FStar_Syntax_Syntax.Sig_declare_typ (uu____4388, uu____4389, uu____4390) -> begin
FStar_Pervasives_Native.None
end
| uu____4391 -> begin
FStar_Pervasives_Native.None
end))


let lb_fv : FStar_Syntax_Syntax.letbinding Prims.list  ->  FStar_Ident.lident  ->  FStar_Syntax_Syntax.fv = (fun lbs lid -> (

let uu____4404 = (FStar_Util.find_map lbs (fun lb -> (

let fv = (FStar_Util.right lb.FStar_Syntax_Syntax.lbname)
in (

let uu____4412 = (FStar_Syntax_Syntax.fv_eq_lid fv lid)
in (match (uu____4412) with
| true -> begin
FStar_Pervasives_Native.Some (fv)
end
| uu____4415 -> begin
FStar_Pervasives_Native.None
end)))))
in (FStar_All.pipe_right uu____4404 FStar_Util.must)))


let ns_of_lid_equals : FStar_Ident.lident  ->  FStar_Ident.lident  ->  Prims.bool = (fun lid ns -> ((Prims.op_Equality (FStar_List.length lid.FStar_Ident.ns) (FStar_List.length (FStar_Ident.ids_of_lid ns))) && (

let uu____4427 = (FStar_Ident.lid_of_ids lid.FStar_Ident.ns)
in (FStar_Ident.lid_equals uu____4427 ns))))


let try_lookup_name : Prims.bool  ->  Prims.bool  ->  env  ->  FStar_Ident.lident  ->  foundname FStar_Pervasives_Native.option = (fun any_val exclude_interf env lid -> (

let occurrence_range = (FStar_Ident.range_of_lid lid)
in (

let k_global_def = (fun source_lid uu___169_4461 -> (match (uu___169_4461) with
| (uu____4468, true) when exclude_interf -> begin
FStar_Pervasives_Native.None
end
| (se, uu____4470) -> begin
(match (se.FStar_Syntax_Syntax.sigel) with
| FStar_Syntax_Syntax.Sig_inductive_typ (uu____4473) -> begin
(

let uu____4490 = (

let uu____4491 = (

let uu____4496 = (FStar_Syntax_Syntax.fvar source_lid FStar_Syntax_Syntax.Delta_constant FStar_Pervasives_Native.None)
in ((uu____4496), (false)))
in Term_name (uu____4491))
in FStar_Pervasives_Native.Some (uu____4490))
end
| FStar_Syntax_Syntax.Sig_datacon (uu____4497) -> begin
(

let uu____4512 = (

let uu____4513 = (

let uu____4518 = (

let uu____4519 = (fv_qual_of_se se)
in (FStar_Syntax_Syntax.fvar source_lid FStar_Syntax_Syntax.Delta_constant uu____4519))
in ((uu____4518), (false)))
in Term_name (uu____4513))
in FStar_Pervasives_Native.Some (uu____4512))
end
| FStar_Syntax_Syntax.Sig_let ((uu____4522, lbs), uu____4524) -> begin
(

let fv = (lb_fv lbs source_lid)
in (

let uu____4540 = (

let uu____4541 = (

let uu____4546 = (FStar_Syntax_Syntax.fvar source_lid fv.FStar_Syntax_Syntax.fv_delta fv.FStar_Syntax_Syntax.fv_qual)
in ((uu____4546), (false)))
in Term_name (uu____4541))
in FStar_Pervasives_Native.Some (uu____4540)))
end
| FStar_Syntax_Syntax.Sig_declare_typ (lid1, uu____4548, uu____4549) -> begin
(

let quals = se.FStar_Syntax_Syntax.sigquals
in (

let uu____4553 = (any_val || (FStar_All.pipe_right quals (FStar_Util.for_some (fun uu___166_4557 -> (match (uu___166_4557) with
| FStar_Syntax_Syntax.Assumption -> begin
true
end
| uu____4558 -> begin
false
end)))))
in (match (uu____4553) with
| true -> begin
(

let lid2 = (FStar_Ident.set_lid_range lid1 (FStar_Ident.range_of_lid source_lid))
in (

let dd = (

let uu____4563 = ((FStar_Syntax_Util.is_primop_lid lid2) || (FStar_All.pipe_right quals (FStar_Util.for_some (fun uu___167_4568 -> (match (uu___167_4568) with
| FStar_Syntax_Syntax.Projector (uu____4569) -> begin
true
end
| FStar_Syntax_Syntax.Discriminator (uu____4574) -> begin
true
end
| uu____4575 -> begin
false
end)))))
in (match (uu____4563) with
| true -> begin
FStar_Syntax_Syntax.Delta_equational
end
| uu____4576 -> begin
FStar_Syntax_Syntax.Delta_constant
end))
in (

let uu____4577 = (FStar_Util.find_map quals (fun uu___168_4582 -> (match (uu___168_4582) with
| FStar_Syntax_Syntax.Reflectable (refl_monad) -> begin
FStar_Pervasives_Native.Some (refl_monad)
end
| uu____4586 -> begin
FStar_Pervasives_Native.None
end)))
in (match (uu____4577) with
| FStar_Pervasives_Native.Some (refl_monad) -> begin
(

let refl_const = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_reflect (refl_monad))) FStar_Pervasives_Native.None occurrence_range)
in FStar_Pervasives_Native.Some (Term_name (((refl_const), (false)))))
end
| uu____4595 -> begin
(

let uu____4598 = (

let uu____4599 = (

let uu____4604 = (

let uu____4605 = (fv_qual_of_se se)
in (FStar_Syntax_Syntax.fvar lid2 dd uu____4605))
in ((uu____4604), (false)))
in Term_name (uu____4599))
in FStar_Pervasives_Native.Some (uu____4598))
end))))
end
| uu____4608 -> begin
FStar_Pervasives_Native.None
end)))
end
| FStar_Syntax_Syntax.Sig_new_effect_for_free (ne) -> begin
FStar_Pervasives_Native.Some (Eff_name (((se), ((FStar_Ident.set_lid_range ne.FStar_Syntax_Syntax.mname (FStar_Ident.range_of_lid source_lid))))))
end
| FStar_Syntax_Syntax.Sig_new_effect (ne) -> begin
FStar_Pervasives_Native.Some (Eff_name (((se), ((FStar_Ident.set_lid_range ne.FStar_Syntax_Syntax.mname (FStar_Ident.range_of_lid source_lid))))))
end
| FStar_Syntax_Syntax.Sig_effect_abbrev (uu____4611) -> begin
FStar_Pervasives_Native.Some (Eff_name (((se), (source_lid))))
end
| uu____4624 -> begin
FStar_Pervasives_Native.None
end)
end))
in (

let k_local_binding = (fun r -> (

let uu____4643 = (

let uu____4644 = (found_local_binding (FStar_Ident.range_of_lid lid) r)
in Term_name (uu____4644))
in FStar_Pervasives_Native.Some (uu____4643)))
in (

let k_rec_binding = (fun uu____4660 -> (match (uu____4660) with
| (id, l, dd) -> begin
(

let uu____4672 = (

let uu____4673 = (

let uu____4678 = (FStar_Syntax_Syntax.fvar (FStar_Ident.set_lid_range l (FStar_Ident.range_of_lid lid)) dd FStar_Pervasives_Native.None)
in ((uu____4678), (false)))
in Term_name (uu____4673))
in FStar_Pervasives_Native.Some (uu____4672))
end))
in (

let found_unmangled = (match (lid.FStar_Ident.ns) with
| [] -> begin
(

let uu____4684 = (unmangleOpName lid.FStar_Ident.ident)
in (match (uu____4684) with
| FStar_Pervasives_Native.Some (f) -> begin
FStar_Pervasives_Native.Some (Term_name (f))
end
| uu____4702 -> begin
FStar_Pervasives_Native.None
end))
end
| uu____4709 -> begin
FStar_Pervasives_Native.None
end)
in (match (found_unmangled) with
| FStar_Pervasives_Native.None -> begin
(resolve_in_open_namespaces' env lid k_local_binding k_rec_binding k_global_def)
end
| x -> begin
x
end)))))))


let try_lookup_effect_name' : Prims.bool  ->  env  ->  FStar_Ident.lident  ->  (FStar_Syntax_Syntax.sigelt * FStar_Ident.lident) FStar_Pervasives_Native.option = (fun exclude_interf env lid -> (

let uu____4741 = (try_lookup_name true exclude_interf env lid)
in (match (uu____4741) with
| FStar_Pervasives_Native.Some (Eff_name (o, l)) -> begin
FStar_Pervasives_Native.Some (((o), (l)))
end
| uu____4756 -> begin
FStar_Pervasives_Native.None
end)))


let try_lookup_effect_name : env  ->  FStar_Ident.lident  ->  FStar_Ident.lident FStar_Pervasives_Native.option = (fun env l -> (

let uu____4773 = (try_lookup_effect_name' (not (env.iface)) env l)
in (match (uu____4773) with
| FStar_Pervasives_Native.Some (o, l1) -> begin
FStar_Pervasives_Native.Some (l1)
end
| uu____4788 -> begin
FStar_Pervasives_Native.None
end)))


let try_lookup_effect_name_and_attributes : env  ->  FStar_Ident.lident  ->  (FStar_Ident.lident * FStar_Syntax_Syntax.cflags Prims.list) FStar_Pervasives_Native.option = (fun env l -> (

let uu____4811 = (try_lookup_effect_name' (not (env.iface)) env l)
in (match (uu____4811) with
| FStar_Pervasives_Native.Some ({FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_new_effect (ne); FStar_Syntax_Syntax.sigrng = uu____4827; FStar_Syntax_Syntax.sigquals = uu____4828; FStar_Syntax_Syntax.sigmeta = uu____4829; FStar_Syntax_Syntax.sigattrs = uu____4830}, l1) -> begin
FStar_Pervasives_Native.Some (((l1), (ne.FStar_Syntax_Syntax.cattributes)))
end
| FStar_Pervasives_Native.Some ({FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_new_effect_for_free (ne); FStar_Syntax_Syntax.sigrng = uu____4849; FStar_Syntax_Syntax.sigquals = uu____4850; FStar_Syntax_Syntax.sigmeta = uu____4851; FStar_Syntax_Syntax.sigattrs = uu____4852}, l1) -> begin
FStar_Pervasives_Native.Some (((l1), (ne.FStar_Syntax_Syntax.cattributes)))
end
| FStar_Pervasives_Native.Some ({FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_effect_abbrev (uu____4870, uu____4871, uu____4872, uu____4873, cattributes); FStar_Syntax_Syntax.sigrng = uu____4875; FStar_Syntax_Syntax.sigquals = uu____4876; FStar_Syntax_Syntax.sigmeta = uu____4877; FStar_Syntax_Syntax.sigattrs = uu____4878}, l1) -> begin
FStar_Pervasives_Native.Some (((l1), (cattributes)))
end
| uu____4900 -> begin
FStar_Pervasives_Native.None
end)))


let try_lookup_effect_defn : env  ->  FStar_Ident.lident  ->  FStar_Syntax_Syntax.eff_decl FStar_Pervasives_Native.option = (fun env l -> (

let uu____4923 = (try_lookup_effect_name' (not (env.iface)) env l)
in (match (uu____4923) with
| FStar_Pervasives_Native.Some ({FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_new_effect (ne); FStar_Syntax_Syntax.sigrng = uu____4933; FStar_Syntax_Syntax.sigquals = uu____4934; FStar_Syntax_Syntax.sigmeta = uu____4935; FStar_Syntax_Syntax.sigattrs = uu____4936}, uu____4937) -> begin
FStar_Pervasives_Native.Some (ne)
end
| FStar_Pervasives_Native.Some ({FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_new_effect_for_free (ne); FStar_Syntax_Syntax.sigrng = uu____4947; FStar_Syntax_Syntax.sigquals = uu____4948; FStar_Syntax_Syntax.sigmeta = uu____4949; FStar_Syntax_Syntax.sigattrs = uu____4950}, uu____4951) -> begin
FStar_Pervasives_Native.Some (ne)
end
| uu____4960 -> begin
FStar_Pervasives_Native.None
end)))


let is_effect_name : env  ->  FStar_Ident.lident  ->  Prims.bool = (fun env lid -> (

let uu____4975 = (try_lookup_effect_name env lid)
in (match (uu____4975) with
| FStar_Pervasives_Native.None -> begin
false
end
| FStar_Pervasives_Native.Some (uu____4978) -> begin
true
end)))


let try_lookup_root_effect_name : env  ->  FStar_Ident.lident  ->  FStar_Ident.lident FStar_Pervasives_Native.option = (fun env l -> (

let uu____4989 = (try_lookup_effect_name' (not (env.iface)) env l)
in (match (uu____4989) with
| FStar_Pervasives_Native.Some ({FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_effect_abbrev (l', uu____4999, uu____5000, uu____5001, uu____5002); FStar_Syntax_Syntax.sigrng = uu____5003; FStar_Syntax_Syntax.sigquals = uu____5004; FStar_Syntax_Syntax.sigmeta = uu____5005; FStar_Syntax_Syntax.sigattrs = uu____5006}, uu____5007) -> begin
(

let rec aux = (fun new_name -> (

let uu____5026 = (FStar_Util.smap_try_find (sigmap env) new_name.FStar_Ident.str)
in (match (uu____5026) with
| FStar_Pervasives_Native.None -> begin
FStar_Pervasives_Native.None
end
| FStar_Pervasives_Native.Some (s, uu____5044) -> begin
(match (s.FStar_Syntax_Syntax.sigel) with
| FStar_Syntax_Syntax.Sig_new_effect_for_free (ne) -> begin
FStar_Pervasives_Native.Some ((FStar_Ident.set_lid_range ne.FStar_Syntax_Syntax.mname (FStar_Ident.range_of_lid l)))
end
| FStar_Syntax_Syntax.Sig_new_effect (ne) -> begin
FStar_Pervasives_Native.Some ((FStar_Ident.set_lid_range ne.FStar_Syntax_Syntax.mname (FStar_Ident.range_of_lid l)))
end
| FStar_Syntax_Syntax.Sig_effect_abbrev (uu____5053, uu____5054, uu____5055, cmp, uu____5057) -> begin
(

let l'' = (FStar_Syntax_Util.comp_effect_name cmp)
in (aux l''))
end
| uu____5063 -> begin
FStar_Pervasives_Native.None
end)
end)))
in (aux l'))
end
| FStar_Pervasives_Native.Some (uu____5064, l') -> begin
FStar_Pervasives_Native.Some (l')
end
| uu____5070 -> begin
FStar_Pervasives_Native.None
end)))


let lookup_letbinding_quals : env  ->  FStar_Ident.lident  ->  FStar_Syntax_Syntax.qualifier Prims.list = (fun env lid -> (

let k_global_def = (fun lid1 uu___170_5101 -> (match (uu___170_5101) with
| ({FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_declare_typ (uu____5110, uu____5111, uu____5112); FStar_Syntax_Syntax.sigrng = uu____5113; FStar_Syntax_Syntax.sigquals = quals; FStar_Syntax_Syntax.sigmeta = uu____5115; FStar_Syntax_Syntax.sigattrs = uu____5116}, uu____5117) -> begin
FStar_Pervasives_Native.Some (quals)
end
| uu____5124 -> begin
FStar_Pervasives_Native.None
end))
in (

let uu____5131 = (resolve_in_open_namespaces' env lid (fun uu____5139 -> FStar_Pervasives_Native.None) (fun uu____5143 -> FStar_Pervasives_Native.None) k_global_def)
in (match (uu____5131) with
| FStar_Pervasives_Native.Some (quals) -> begin
quals
end
| uu____5153 -> begin
[]
end))))


let try_lookup_module : env  ->  Prims.string Prims.list  ->  FStar_Syntax_Syntax.modul FStar_Pervasives_Native.option = (fun env path -> (

let uu____5172 = (FStar_List.tryFind (fun uu____5187 -> (match (uu____5187) with
| (mlid, modul) -> begin
(

let uu____5194 = (FStar_Ident.path_of_lid mlid)
in (Prims.op_Equality uu____5194 path))
end)) env.modules)
in (match (uu____5172) with
| FStar_Pervasives_Native.Some (uu____5201, modul) -> begin
FStar_Pervasives_Native.Some (modul)
end
| FStar_Pervasives_Native.None -> begin
FStar_Pervasives_Native.None
end)))


let try_lookup_let : env  ->  FStar_Ident.lident  ->  FStar_Syntax_Syntax.term FStar_Pervasives_Native.option = (fun env lid -> (

let k_global_def = (fun lid1 uu___171_5233 -> (match (uu___171_5233) with
| ({FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_let ((uu____5240, lbs), uu____5242); FStar_Syntax_Syntax.sigrng = uu____5243; FStar_Syntax_Syntax.sigquals = uu____5244; FStar_Syntax_Syntax.sigmeta = uu____5245; FStar_Syntax_Syntax.sigattrs = uu____5246}, uu____5247) -> begin
(

let fv = (lb_fv lbs lid1)
in (

let uu____5267 = (FStar_Syntax_Syntax.fvar lid1 fv.FStar_Syntax_Syntax.fv_delta fv.FStar_Syntax_Syntax.fv_qual)
in FStar_Pervasives_Native.Some (uu____5267)))
end
| uu____5268 -> begin
FStar_Pervasives_Native.None
end))
in (resolve_in_open_namespaces' env lid (fun uu____5274 -> FStar_Pervasives_Native.None) (fun uu____5276 -> FStar_Pervasives_Native.None) k_global_def)))


let try_lookup_definition : env  ->  FStar_Ident.lident  ->  FStar_Syntax_Syntax.term FStar_Pervasives_Native.option = (fun env lid -> (

let k_global_def = (fun lid1 uu___172_5301 -> (match (uu___172_5301) with
| ({FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_let (lbs, uu____5311); FStar_Syntax_Syntax.sigrng = uu____5312; FStar_Syntax_Syntax.sigquals = uu____5313; FStar_Syntax_Syntax.sigmeta = uu____5314; FStar_Syntax_Syntax.sigattrs = uu____5315}, uu____5316) -> begin
(FStar_Util.find_map (FStar_Pervasives_Native.snd lbs) (fun lb -> (match (lb.FStar_Syntax_Syntax.lbname) with
| FStar_Util.Inr (fv) when (FStar_Syntax_Syntax.fv_eq_lid fv lid1) -> begin
FStar_Pervasives_Native.Some (lb.FStar_Syntax_Syntax.lbdef)
end
| uu____5339 -> begin
FStar_Pervasives_Native.None
end)))
end
| uu____5346 -> begin
FStar_Pervasives_Native.None
end))
in (resolve_in_open_namespaces' env lid (fun uu____5356 -> FStar_Pervasives_Native.None) (fun uu____5360 -> FStar_Pervasives_Native.None) k_global_def)))


let empty_include_smap : FStar_Ident.lident Prims.list FStar_ST.ref FStar_Util.smap = (new_sigmap ())


let empty_exported_id_smap : exported_id_set FStar_Util.smap = (new_sigmap ())


let try_lookup_lid' : Prims.bool  ->  Prims.bool  ->  env  ->  FStar_Ident.lident  ->  (FStar_Syntax_Syntax.term * Prims.bool) FStar_Pervasives_Native.option = (fun any_val exclude_interf env lid -> (

let uu____5403 = (try_lookup_name any_val exclude_interf env lid)
in (match (uu____5403) with
| FStar_Pervasives_Native.Some (Term_name (e, mut)) -> begin
FStar_Pervasives_Native.Some (((e), (mut)))
end
| uu____5418 -> begin
FStar_Pervasives_Native.None
end)))


let try_lookup_lid : env  ->  FStar_Ident.lident  ->  (FStar_Syntax_Syntax.term * Prims.bool) FStar_Pervasives_Native.option = (fun env l -> (try_lookup_lid' env.iface false env l))


let resolve_to_fully_qualified_name : env  ->  FStar_Ident.lident  ->  FStar_Ident.lident FStar_Pervasives_Native.option = (fun env l -> (

let uu____5449 = (try_lookup_lid env l)
in (match (uu____5449) with
| FStar_Pervasives_Native.None -> begin
FStar_Pervasives_Native.None
end
| FStar_Pervasives_Native.Some (e, uu____5463) -> begin
(

let uu____5468 = (

let uu____5469 = (FStar_Syntax_Subst.compress e)
in uu____5469.FStar_Syntax_Syntax.n)
in (match (uu____5468) with
| FStar_Syntax_Syntax.Tm_fvar (fv) -> begin
FStar_Pervasives_Native.Some (fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v)
end
| uu____5475 -> begin
FStar_Pervasives_Native.None
end))
end)))


let try_lookup_lid_no_resolve : env  ->  FStar_Ident.lident  ->  (FStar_Syntax_Syntax.term * Prims.bool) FStar_Pervasives_Native.option = (fun env l -> (

let env' = (

let uu___193_5491 = env
in {curmodule = uu___193_5491.curmodule; curmonad = uu___193_5491.curmonad; modules = uu___193_5491.modules; scope_mods = []; exported_ids = empty_exported_id_smap; trans_exported_ids = uu___193_5491.trans_exported_ids; includes = empty_include_smap; sigaccum = uu___193_5491.sigaccum; sigmap = uu___193_5491.sigmap; iface = uu___193_5491.iface; admitted_iface = uu___193_5491.admitted_iface; expect_typ = uu___193_5491.expect_typ; docs = uu___193_5491.docs; remaining_iface_decls = uu___193_5491.remaining_iface_decls; syntax_only = uu___193_5491.syntax_only; ds_hooks = uu___193_5491.ds_hooks})
in (try_lookup_lid env' l)))


let try_lookup_doc : env  ->  FStar_Ident.lid  ->  FStar_Parser_AST.fsdoc FStar_Pervasives_Native.option = (fun env l -> (FStar_Util.smap_try_find env.docs l.FStar_Ident.str))


let try_lookup_datacon : env  ->  FStar_Ident.lident  ->  FStar_Syntax_Syntax.fv FStar_Pervasives_Native.option = (fun env lid -> (

let k_global_def = (fun lid1 uu___174_5524 -> (match (uu___174_5524) with
| ({FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_declare_typ (uu____5531, uu____5532, uu____5533); FStar_Syntax_Syntax.sigrng = uu____5534; FStar_Syntax_Syntax.sigquals = quals; FStar_Syntax_Syntax.sigmeta = uu____5536; FStar_Syntax_Syntax.sigattrs = uu____5537}, uu____5538) -> begin
(

let uu____5543 = (FStar_All.pipe_right quals (FStar_Util.for_some (fun uu___173_5547 -> (match (uu___173_5547) with
| FStar_Syntax_Syntax.Assumption -> begin
true
end
| uu____5548 -> begin
false
end))))
in (match (uu____5543) with
| true -> begin
(

let uu____5551 = (FStar_Syntax_Syntax.lid_as_fv lid1 FStar_Syntax_Syntax.Delta_constant FStar_Pervasives_Native.None)
in FStar_Pervasives_Native.Some (uu____5551))
end
| uu____5552 -> begin
FStar_Pervasives_Native.None
end))
end
| ({FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_datacon (uu____5553); FStar_Syntax_Syntax.sigrng = uu____5554; FStar_Syntax_Syntax.sigquals = uu____5555; FStar_Syntax_Syntax.sigmeta = uu____5556; FStar_Syntax_Syntax.sigattrs = uu____5557}, uu____5558) -> begin
(

let uu____5577 = (FStar_Syntax_Syntax.lid_as_fv lid1 FStar_Syntax_Syntax.Delta_constant (FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Data_ctor)))
in FStar_Pervasives_Native.Some (uu____5577))
end
| uu____5578 -> begin
FStar_Pervasives_Native.None
end))
in (resolve_in_open_namespaces' env lid (fun uu____5584 -> FStar_Pervasives_Native.None) (fun uu____5586 -> FStar_Pervasives_Native.None) k_global_def)))


let find_all_datacons : env  ->  FStar_Ident.lident  ->  FStar_Ident.lident Prims.list FStar_Pervasives_Native.option = (fun env lid -> (

let k_global_def = (fun lid1 uu___175_5613 -> (match (uu___175_5613) with
| ({FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_inductive_typ (uu____5622, uu____5623, uu____5624, uu____5625, datas, uu____5627); FStar_Syntax_Syntax.sigrng = uu____5628; FStar_Syntax_Syntax.sigquals = uu____5629; FStar_Syntax_Syntax.sigmeta = uu____5630; FStar_Syntax_Syntax.sigattrs = uu____5631}, uu____5632) -> begin
FStar_Pervasives_Native.Some (datas)
end
| uu____5647 -> begin
FStar_Pervasives_Native.None
end))
in (resolve_in_open_namespaces' env lid (fun uu____5657 -> FStar_Pervasives_Native.None) (fun uu____5661 -> FStar_Pervasives_Native.None) k_global_def)))


let record_cache_aux_with_filter : (((Prims.unit  ->  Prims.unit) * (Prims.unit  ->  Prims.unit) * (Prims.unit  ->  record_or_dc Prims.list) * (record_or_dc  ->  Prims.unit)) * (Prims.unit  ->  Prims.unit)) = (

let record_cache = (FStar_Util.mk_ref (([])::[]))
in (

let push1 = (fun uu____5706 -> (

let uu____5707 = (

let uu____5712 = (

let uu____5715 = (FStar_ST.op_Bang record_cache)
in (FStar_List.hd uu____5715))
in (

let uu____5790 = (FStar_ST.op_Bang record_cache)
in (uu____5712)::uu____5790))
in (FStar_ST.op_Colon_Equals record_cache uu____5707)))
in (

let pop1 = (fun uu____5936 -> (

let uu____5937 = (

let uu____5942 = (FStar_ST.op_Bang record_cache)
in (FStar_List.tl uu____5942))
in (FStar_ST.op_Colon_Equals record_cache uu____5937)))
in (

let peek1 = (fun uu____6090 -> (

let uu____6091 = (FStar_ST.op_Bang record_cache)
in (FStar_List.hd uu____6091)))
in (

let insert = (fun r -> (

let uu____6170 = (

let uu____6175 = (

let uu____6178 = (peek1 ())
in (r)::uu____6178)
in (

let uu____6181 = (

let uu____6186 = (FStar_ST.op_Bang record_cache)
in (FStar_List.tl uu____6186))
in (uu____6175)::uu____6181))
in (FStar_ST.op_Colon_Equals record_cache uu____6170)))
in (

let filter1 = (fun uu____6334 -> (

let rc = (peek1 ())
in (

let filtered = (FStar_List.filter (fun r -> (not (r.is_private_or_abstract))) rc)
in (

let uu____6343 = (

let uu____6348 = (

let uu____6353 = (FStar_ST.op_Bang record_cache)
in (FStar_List.tl uu____6353))
in (filtered)::uu____6348)
in (FStar_ST.op_Colon_Equals record_cache uu____6343)))))
in (

let aux = ((push1), (pop1), (peek1), (insert))
in ((aux), (filter1)))))))))


let record_cache_aux : ((Prims.unit  ->  Prims.unit) * (Prims.unit  ->  Prims.unit) * (Prims.unit  ->  record_or_dc Prims.list) * (record_or_dc  ->  Prims.unit)) = (

let uu____6565 = record_cache_aux_with_filter
in (match (uu____6565) with
| (aux, uu____6609) -> begin
aux
end))


let filter_record_cache : Prims.unit  ->  Prims.unit = (

let uu____6653 = record_cache_aux_with_filter
in (match (uu____6653) with
| (uu____6680, filter1) -> begin
filter1
end))


let push_record_cache : Prims.unit  ->  Prims.unit = (

let uu____6725 = record_cache_aux
in (match (uu____6725) with
| (push1, uu____6747, uu____6748, uu____6749) -> begin
push1
end))


let pop_record_cache : Prims.unit  ->  Prims.unit = (

let uu____6773 = record_cache_aux
in (match (uu____6773) with
| (uu____6794, pop1, uu____6796, uu____6797) -> begin
pop1
end))


let peek_record_cache : Prims.unit  ->  record_or_dc Prims.list = (

let uu____6823 = record_cache_aux
in (match (uu____6823) with
| (uu____6846, uu____6847, peek1, uu____6849) -> begin
peek1
end))


let insert_record_cache : record_or_dc  ->  Prims.unit = (

let uu____6873 = record_cache_aux
in (match (uu____6873) with
| (uu____6894, uu____6895, uu____6896, insert) -> begin
insert
end))


let extract_record : env  ->  scope_mod Prims.list FStar_ST.ref  ->  FStar_Syntax_Syntax.sigelt  ->  Prims.unit = (fun e new_globs se -> (match (se.FStar_Syntax_Syntax.sigel) with
| FStar_Syntax_Syntax.Sig_bundle (sigs, uu____6953) -> begin
(

let is_record = (FStar_Util.for_some (fun uu___176_6969 -> (match (uu___176_6969) with
| FStar_Syntax_Syntax.RecordType (uu____6970) -> begin
true
end
| FStar_Syntax_Syntax.RecordConstructor (uu____6979) -> begin
true
end
| uu____6988 -> begin
false
end)))
in (

let find_dc = (fun dc -> (FStar_All.pipe_right sigs (FStar_Util.find_opt (fun uu___177_7010 -> (match (uu___177_7010) with
| {FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_datacon (lid, uu____7012, uu____7013, uu____7014, uu____7015, uu____7016); FStar_Syntax_Syntax.sigrng = uu____7017; FStar_Syntax_Syntax.sigquals = uu____7018; FStar_Syntax_Syntax.sigmeta = uu____7019; FStar_Syntax_Syntax.sigattrs = uu____7020} -> begin
(FStar_Ident.lid_equals dc lid)
end
| uu____7029 -> begin
false
end)))))
in (FStar_All.pipe_right sigs (FStar_List.iter (fun uu___178_7064 -> (match (uu___178_7064) with
| {FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_inductive_typ (typename, univs1, parms, uu____7068, uu____7069, (dc)::[]); FStar_Syntax_Syntax.sigrng = uu____7071; FStar_Syntax_Syntax.sigquals = typename_quals; FStar_Syntax_Syntax.sigmeta = uu____7073; FStar_Syntax_Syntax.sigattrs = uu____7074} -> begin
(

let uu____7085 = (

let uu____7086 = (find_dc dc)
in (FStar_All.pipe_left FStar_Util.must uu____7086))
in (match (uu____7085) with
| {FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_datacon (constrname, uu____7092, t, uu____7094, uu____7095, uu____7096); FStar_Syntax_Syntax.sigrng = uu____7097; FStar_Syntax_Syntax.sigquals = uu____7098; FStar_Syntax_Syntax.sigmeta = uu____7099; FStar_Syntax_Syntax.sigattrs = uu____7100} -> begin
(

let uu____7109 = (FStar_Syntax_Util.arrow_formals t)
in (match (uu____7109) with
| (formals, uu____7123) -> begin
(

let is_rec = (is_record typename_quals)
in (

let formals' = (FStar_All.pipe_right formals (FStar_List.collect (fun uu____7172 -> (match (uu____7172) with
| (x, q) -> begin
(

let uu____7185 = ((FStar_Syntax_Syntax.is_null_bv x) || (is_rec && (FStar_Syntax_Syntax.is_implicit q)))
in (match (uu____7185) with
| true -> begin
[]
end
| uu____7196 -> begin
(((x), (q)))::[]
end))
end))))
in (

let fields' = (FStar_All.pipe_right formals' (FStar_List.map (fun uu____7242 -> (match (uu____7242) with
| (x, q) -> begin
(

let uu____7255 = (match (is_rec) with
| true -> begin
(FStar_Syntax_Util.unmangle_field_name x.FStar_Syntax_Syntax.ppname)
end
| uu____7256 -> begin
x.FStar_Syntax_Syntax.ppname
end)
in ((uu____7255), (x.FStar_Syntax_Syntax.sort)))
end))))
in (

let fields = fields'
in (

let record = {typename = typename; constrname = constrname.FStar_Ident.ident; parms = parms; fields = fields; is_private_or_abstract = ((FStar_List.contains FStar_Syntax_Syntax.Private typename_quals) || (FStar_List.contains FStar_Syntax_Syntax.Abstract typename_quals)); is_record = is_rec}
in ((

let uu____7270 = (

let uu____7273 = (FStar_ST.op_Bang new_globs)
in (Record_or_dc (record))::uu____7273)
in (FStar_ST.op_Colon_Equals new_globs uu____7270));
(match (()) with
| () -> begin
((

let add_field = (fun uu____7414 -> (match (uu____7414) with
| (id, uu____7422) -> begin
(

let modul = (

let uu____7428 = (FStar_Ident.lid_of_ids constrname.FStar_Ident.ns)
in uu____7428.FStar_Ident.str)
in (

let uu____7429 = (get_exported_id_set e modul)
in (match (uu____7429) with
| FStar_Pervasives_Native.Some (my_ex) -> begin
(

let my_exported_ids = (my_ex Exported_id_field)
in ((

let uu____7456 = (

let uu____7457 = (FStar_ST.op_Bang my_exported_ids)
in (FStar_Util.set_add id.FStar_Ident.idText uu____7457))
in (FStar_ST.op_Colon_Equals my_exported_ids uu____7456));
(match (()) with
| () -> begin
(

let projname = (

let uu____7581 = (

let uu____7582 = (FStar_Syntax_Util.mk_field_projector_name_from_ident constrname id)
in uu____7582.FStar_Ident.ident)
in uu____7581.FStar_Ident.idText)
in (

let uu____7584 = (

let uu____7585 = (FStar_ST.op_Bang my_exported_ids)
in (FStar_Util.set_add projname uu____7585))
in (FStar_ST.op_Colon_Equals my_exported_ids uu____7584)))
end);
))
end
| FStar_Pervasives_Native.None -> begin
()
end)))
end))
in (FStar_List.iter add_field fields'));
(match (()) with
| () -> begin
(insert_record_cache record)
end);
)
end);
))))))
end))
end
| uu____7718 -> begin
()
end))
end
| uu____7719 -> begin
()
end))))))
end
| uu____7720 -> begin
()
end))


let try_lookup_record_or_dc_by_field_name : env  ->  FStar_Ident.lident  ->  record_or_dc FStar_Pervasives_Native.option = (fun env fieldname -> (

let find_in_cache = (fun fieldname1 -> (

let uu____7737 = ((fieldname1.FStar_Ident.ns), (fieldname1.FStar_Ident.ident))
in (match (uu____7737) with
| (ns, id) -> begin
(

let uu____7754 = (peek_record_cache ())
in (FStar_Util.find_map uu____7754 (fun record -> (

let uu____7760 = (find_in_record ns id record (fun r -> Cont_ok (r)))
in (option_of_cont (fun uu____7766 -> FStar_Pervasives_Native.None) uu____7760)))))
end)))
in (resolve_in_open_namespaces'' env fieldname Exported_id_field (fun uu____7768 -> Cont_ignore) (fun uu____7770 -> Cont_ignore) (fun r -> Cont_ok (r)) (fun fn -> (

let uu____7776 = (find_in_cache fn)
in (cont_of_option Cont_ignore uu____7776))) (fun k uu____7782 -> k))))


let try_lookup_record_by_field_name : env  ->  FStar_Ident.lident  ->  record_or_dc FStar_Pervasives_Native.option = (fun env fieldname -> (

let uu____7795 = (try_lookup_record_or_dc_by_field_name env fieldname)
in (match (uu____7795) with
| FStar_Pervasives_Native.Some (r) when r.is_record -> begin
FStar_Pervasives_Native.Some (r)
end
| uu____7801 -> begin
FStar_Pervasives_Native.None
end)))


let belongs_to_record : env  ->  FStar_Ident.lident  ->  record_or_dc  ->  Prims.bool = (fun env lid record -> (

let uu____7816 = (try_lookup_record_by_field_name env lid)
in (match (uu____7816) with
| FStar_Pervasives_Native.Some (record') when (

let uu____7820 = (

let uu____7821 = (FStar_Ident.path_of_ns record.typename.FStar_Ident.ns)
in (FStar_Ident.text_of_path uu____7821))
in (

let uu____7824 = (

let uu____7825 = (FStar_Ident.path_of_ns record'.typename.FStar_Ident.ns)
in (FStar_Ident.text_of_path uu____7825))
in (Prims.op_Equality uu____7820 uu____7824))) -> begin
(

let uu____7828 = (find_in_record record.typename.FStar_Ident.ns lid.FStar_Ident.ident record (fun uu____7832 -> Cont_ok (())))
in (match (uu____7828) with
| Cont_ok (uu____7833) -> begin
true
end
| uu____7834 -> begin
false
end))
end
| uu____7837 -> begin
false
end)))


let try_lookup_dc_by_field_name : env  ->  FStar_Ident.lident  ->  (FStar_Ident.lident * Prims.bool) FStar_Pervasives_Native.option = (fun env fieldname -> (

let uu____7854 = (try_lookup_record_or_dc_by_field_name env fieldname)
in (match (uu____7854) with
| FStar_Pervasives_Native.Some (r) -> begin
(

let uu____7864 = (

let uu____7869 = (

let uu____7870 = (FStar_Ident.lid_of_ids (FStar_List.append r.typename.FStar_Ident.ns ((r.constrname)::[])))
in (FStar_Ident.set_lid_range uu____7870 (FStar_Ident.range_of_lid fieldname)))
in ((uu____7869), (r.is_record)))
in FStar_Pervasives_Native.Some (uu____7864))
end
| uu____7875 -> begin
FStar_Pervasives_Native.None
end)))


let string_set_ref_new : Prims.unit  ->  Prims.string FStar_Util.set FStar_ST.ref = (fun uu____7896 -> (

let uu____7897 = (FStar_Util.new_set FStar_Util.compare)
in (FStar_Util.mk_ref uu____7897)))


let exported_id_set_new : Prims.unit  ->  exported_id_kind  ->  Prims.string FStar_Util.set FStar_ST.ref = (fun uu____7918 -> (

let term_type_set = (string_set_ref_new ())
in (

let field_set = (string_set_ref_new ())
in (fun uu___179_7929 -> (match (uu___179_7929) with
| Exported_id_term_type -> begin
term_type_set
end
| Exported_id_field -> begin
field_set
end)))))


let unique : Prims.bool  ->  Prims.bool  ->  env  ->  FStar_Ident.lident  ->  Prims.bool = (fun any_val exclude_if env lid -> (

let filter_scope_mods = (fun uu___180_7967 -> (match (uu___180_7967) with
| Rec_binding (uu____7968) -> begin
true
end
| uu____7969 -> begin
false
end))
in (

let this_env = (

let uu___194_7971 = env
in (

let uu____7972 = (FStar_List.filter filter_scope_mods env.scope_mods)
in {curmodule = uu___194_7971.curmodule; curmonad = uu___194_7971.curmonad; modules = uu___194_7971.modules; scope_mods = uu____7972; exported_ids = empty_exported_id_smap; trans_exported_ids = uu___194_7971.trans_exported_ids; includes = empty_include_smap; sigaccum = uu___194_7971.sigaccum; sigmap = uu___194_7971.sigmap; iface = uu___194_7971.iface; admitted_iface = uu___194_7971.admitted_iface; expect_typ = uu___194_7971.expect_typ; docs = uu___194_7971.docs; remaining_iface_decls = uu___194_7971.remaining_iface_decls; syntax_only = uu___194_7971.syntax_only; ds_hooks = uu___194_7971.ds_hooks}))
in (

let uu____7975 = (try_lookup_lid' any_val exclude_if this_env lid)
in (match (uu____7975) with
| FStar_Pervasives_Native.None -> begin
true
end
| FStar_Pervasives_Native.Some (uu____7986) -> begin
false
end)))))


let push_scope_mod : env  ->  scope_mod  ->  env = (fun env scope_mod -> (

let uu___195_8003 = env
in {curmodule = uu___195_8003.curmodule; curmonad = uu___195_8003.curmonad; modules = uu___195_8003.modules; scope_mods = (scope_mod)::env.scope_mods; exported_ids = uu___195_8003.exported_ids; trans_exported_ids = uu___195_8003.trans_exported_ids; includes = uu___195_8003.includes; sigaccum = uu___195_8003.sigaccum; sigmap = uu___195_8003.sigmap; iface = uu___195_8003.iface; admitted_iface = uu___195_8003.admitted_iface; expect_typ = uu___195_8003.expect_typ; docs = uu___195_8003.docs; remaining_iface_decls = uu___195_8003.remaining_iface_decls; syntax_only = uu___195_8003.syntax_only; ds_hooks = uu___195_8003.ds_hooks}))


let push_bv' : env  ->  FStar_Ident.ident  ->  Prims.bool  ->  (env * FStar_Syntax_Syntax.bv) = (fun env x is_mutable -> (

let bv = (FStar_Syntax_Syntax.gen_bv x.FStar_Ident.idText (FStar_Pervasives_Native.Some (x.FStar_Ident.idRange)) FStar_Syntax_Syntax.tun)
in (((push_scope_mod env (Local_binding (((x), (bv), (is_mutable)))))), (bv))))


let push_bv_mutable : env  ->  FStar_Ident.ident  ->  (env * FStar_Syntax_Syntax.bv) = (fun env x -> (push_bv' env x true))


let push_bv : env  ->  FStar_Ident.ident  ->  (env * FStar_Syntax_Syntax.bv) = (fun env x -> (push_bv' env x false))


let push_top_level_rec_binding : env  ->  FStar_Ident.ident  ->  FStar_Syntax_Syntax.delta_depth  ->  env = (fun env x dd -> (

let l = (qualify env x)
in (

let uu____8058 = ((unique false true env l) || (FStar_Options.interactive ()))
in (match (uu____8058) with
| true -> begin
(push_scope_mod env (Rec_binding (((x), (l), (dd)))))
end
| uu____8059 -> begin
(FStar_Exn.raise (FStar_Errors.Error ((((Prims.strcat "Duplicate top-level names " l.FStar_Ident.str)), ((FStar_Ident.range_of_lid l))))))
end))))


let push_sigelt : env  ->  FStar_Syntax_Syntax.sigelt  ->  env = (fun env s -> (

let err1 = (fun l -> (

let sopt = (FStar_Util.smap_try_find (sigmap env) l.FStar_Ident.str)
in (

let r = (match (sopt) with
| FStar_Pervasives_Native.Some (se, uu____8085) -> begin
(

let uu____8090 = (FStar_Util.find_opt (FStar_Ident.lid_equals l) (FStar_Syntax_Util.lids_of_sigelt se))
in (match (uu____8090) with
| FStar_Pervasives_Native.Some (l1) -> begin
(FStar_All.pipe_left FStar_Range.string_of_range (FStar_Ident.range_of_lid l1))
end
| FStar_Pervasives_Native.None -> begin
"<unknown>"
end))
end
| FStar_Pervasives_Native.None -> begin
"<unknown>"
end)
in (

let uu____8098 = (

let uu____8099 = (

let uu____8104 = (FStar_Util.format2 "Duplicate top-level names [%s]; previously declared at %s" (FStar_Ident.text_of_lid l) r)
in ((uu____8104), ((FStar_Ident.range_of_lid l))))
in FStar_Errors.Error (uu____8099))
in (FStar_Exn.raise uu____8098)))))
in (

let globals = (FStar_Util.mk_ref env.scope_mods)
in (

let env1 = (

let uu____8113 = (match (s.FStar_Syntax_Syntax.sigel) with
| FStar_Syntax_Syntax.Sig_let (uu____8122) -> begin
((false), (true))
end
| FStar_Syntax_Syntax.Sig_bundle (uu____8129) -> begin
((true), (true))
end
| uu____8138 -> begin
((false), (false))
end)
in (match (uu____8113) with
| (any_val, exclude_if) -> begin
(

let lids = (FStar_Syntax_Util.lids_of_sigelt s)
in (

let uu____8144 = (FStar_Util.find_map lids (fun l -> (

let uu____8150 = (

let uu____8151 = (unique any_val exclude_if env l)
in (not (uu____8151)))
in (match (uu____8150) with
| true -> begin
FStar_Pervasives_Native.Some (l)
end
| uu____8154 -> begin
FStar_Pervasives_Native.None
end))))
in (match (uu____8144) with
| FStar_Pervasives_Native.Some (l) when (

let uu____8156 = (FStar_Options.interactive ())
in (not (uu____8156))) -> begin
(err1 l)
end
| uu____8157 -> begin
((extract_record env globals s);
(

let uu___196_8175 = env
in {curmodule = uu___196_8175.curmodule; curmonad = uu___196_8175.curmonad; modules = uu___196_8175.modules; scope_mods = uu___196_8175.scope_mods; exported_ids = uu___196_8175.exported_ids; trans_exported_ids = uu___196_8175.trans_exported_ids; includes = uu___196_8175.includes; sigaccum = (s)::env.sigaccum; sigmap = uu___196_8175.sigmap; iface = uu___196_8175.iface; admitted_iface = uu___196_8175.admitted_iface; expect_typ = uu___196_8175.expect_typ; docs = uu___196_8175.docs; remaining_iface_decls = uu___196_8175.remaining_iface_decls; syntax_only = uu___196_8175.syntax_only; ds_hooks = uu___196_8175.ds_hooks});
)
end)))
end))
in (

let env2 = (

let uu___197_8177 = env1
in (

let uu____8178 = (FStar_ST.op_Bang globals)
in {curmodule = uu___197_8177.curmodule; curmonad = uu___197_8177.curmonad; modules = uu___197_8177.modules; scope_mods = uu____8178; exported_ids = uu___197_8177.exported_ids; trans_exported_ids = uu___197_8177.trans_exported_ids; includes = uu___197_8177.includes; sigaccum = uu___197_8177.sigaccum; sigmap = uu___197_8177.sigmap; iface = uu___197_8177.iface; admitted_iface = uu___197_8177.admitted_iface; expect_typ = uu___197_8177.expect_typ; docs = uu___197_8177.docs; remaining_iface_decls = uu___197_8177.remaining_iface_decls; syntax_only = uu___197_8177.syntax_only; ds_hooks = uu___197_8177.ds_hooks}))
in (

let uu____8245 = (match (s.FStar_Syntax_Syntax.sigel) with
| FStar_Syntax_Syntax.Sig_bundle (ses, uu____8271) -> begin
(

let uu____8280 = (FStar_List.map (fun se -> (((FStar_Syntax_Util.lids_of_sigelt se)), (se))) ses)
in ((env2), (uu____8280)))
end
| uu____8307 -> begin
((env2), (((((FStar_Syntax_Util.lids_of_sigelt s)), (s)))::[]))
end)
in (match (uu____8245) with
| (env3, lss) -> begin
((FStar_All.pipe_right lss (FStar_List.iter (fun uu____8366 -> (match (uu____8366) with
| (lids, se) -> begin
(FStar_All.pipe_right lids (FStar_List.iter (fun lid -> ((

let uu____8387 = (

let uu____8390 = (FStar_ST.op_Bang globals)
in (Top_level_def (lid.FStar_Ident.ident))::uu____8390)
in (FStar_ST.op_Colon_Equals globals uu____8387));
(match (()) with
| () -> begin
(

let modul = (

let uu____8522 = (FStar_Ident.lid_of_ids lid.FStar_Ident.ns)
in uu____8522.FStar_Ident.str)
in ((

let uu____8524 = (get_exported_id_set env3 modul)
in (match (uu____8524) with
| FStar_Pervasives_Native.Some (f) -> begin
(

let my_exported_ids = (f Exported_id_term_type)
in (

let uu____8550 = (

let uu____8551 = (FStar_ST.op_Bang my_exported_ids)
in (FStar_Util.set_add lid.FStar_Ident.ident.FStar_Ident.idText uu____8551))
in (FStar_ST.op_Colon_Equals my_exported_ids uu____8550)))
end
| FStar_Pervasives_Native.None -> begin
()
end));
(match (()) with
| () -> begin
(FStar_Util.smap_add (sigmap env3) lid.FStar_Ident.str ((se), ((env3.iface && (not (env3.admitted_iface))))))
end);
))
end);
))))
end))));
(

let env4 = (

let uu___198_8683 = env3
in (

let uu____8684 = (FStar_ST.op_Bang globals)
in {curmodule = uu___198_8683.curmodule; curmonad = uu___198_8683.curmonad; modules = uu___198_8683.modules; scope_mods = uu____8684; exported_ids = uu___198_8683.exported_ids; trans_exported_ids = uu___198_8683.trans_exported_ids; includes = uu___198_8683.includes; sigaccum = uu___198_8683.sigaccum; sigmap = uu___198_8683.sigmap; iface = uu___198_8683.iface; admitted_iface = uu___198_8683.admitted_iface; expect_typ = uu___198_8683.expect_typ; docs = uu___198_8683.docs; remaining_iface_decls = uu___198_8683.remaining_iface_decls; syntax_only = uu___198_8683.syntax_only; ds_hooks = uu___198_8683.ds_hooks}))
in env4);
)
end)))))))


let push_namespace : env  ->  FStar_Ident.lident  ->  env = (fun env ns -> (

let uu____8759 = (

let uu____8764 = (resolve_module_name env ns false)
in (match (uu____8764) with
| FStar_Pervasives_Native.None -> begin
(

let modules = env.modules
in (

let uu____8778 = (FStar_All.pipe_right modules (FStar_Util.for_some (fun uu____8792 -> (match (uu____8792) with
| (m, uu____8798) -> begin
(FStar_Util.starts_with (Prims.strcat (FStar_Ident.text_of_lid m) ".") (Prims.strcat (FStar_Ident.text_of_lid ns) "."))
end))))
in (match (uu____8778) with
| true -> begin
((ns), (Open_namespace))
end
| uu____8803 -> begin
(

let uu____8804 = (

let uu____8805 = (

let uu____8810 = (FStar_Util.format1 "Namespace %s cannot be found" (FStar_Ident.text_of_lid ns))
in ((uu____8810), ((FStar_Ident.range_of_lid ns))))
in FStar_Errors.Error (uu____8805))
in (FStar_Exn.raise uu____8804))
end)))
end
| FStar_Pervasives_Native.Some (ns') -> begin
((fail_if_curmodule env ns ns');
((ns'), (Open_module));
)
end))
in (match (uu____8759) with
| (ns', kd) -> begin
((env.ds_hooks.ds_push_open_hook env ((ns'), (kd)));
(push_scope_mod env (Open_module_or_namespace (((ns'), (kd)))));
)
end)))


let push_include : env  ->  FStar_Ident.lident  ->  env = (fun env ns -> (

let ns0 = ns
in (

let uu____8829 = (resolve_module_name env ns false)
in (match (uu____8829) with
| FStar_Pervasives_Native.Some (ns1) -> begin
((env.ds_hooks.ds_push_include_hook env ns1);
(fail_if_curmodule env ns0 ns1);
(

let env1 = (push_scope_mod env (Open_module_or_namespace (((ns1), (Open_module)))))
in (

let curmod = (

let uu____8837 = (current_module env1)
in uu____8837.FStar_Ident.str)
in ((

let uu____8839 = (FStar_Util.smap_try_find env1.includes curmod)
in (match (uu____8839) with
| FStar_Pervasives_Native.None -> begin
()
end
| FStar_Pervasives_Native.Some (incl) -> begin
(

let uu____8863 = (

let uu____8866 = (FStar_ST.op_Bang incl)
in (ns1)::uu____8866)
in (FStar_ST.op_Colon_Equals incl uu____8863))
end));
(match (()) with
| () -> begin
(

let uu____8997 = (get_trans_exported_id_set env1 ns1.FStar_Ident.str)
in (match (uu____8997) with
| FStar_Pervasives_Native.Some (ns_trans_exports) -> begin
((

let uu____9014 = (

let uu____9031 = (get_exported_id_set env1 curmod)
in (

let uu____9038 = (get_trans_exported_id_set env1 curmod)
in ((uu____9031), (uu____9038))))
in (match (uu____9014) with
| (FStar_Pervasives_Native.Some (cur_exports), FStar_Pervasives_Native.Some (cur_trans_exports)) -> begin
(

let update_exports = (fun k -> (

let ns_ex = (

let uu____9092 = (ns_trans_exports k)
in (FStar_ST.op_Bang uu____9092))
in (

let ex = (cur_exports k)
in ((

let uu____9347 = (

let uu____9348 = (FStar_ST.op_Bang ex)
in (FStar_Util.set_difference uu____9348 ns_ex))
in (FStar_ST.op_Colon_Equals ex uu____9347));
(match (()) with
| () -> begin
(

let trans_ex = (cur_trans_exports k)
in (

let uu____9482 = (

let uu____9483 = (FStar_ST.op_Bang trans_ex)
in (FStar_Util.set_union uu____9483 ns_ex))
in (FStar_ST.op_Colon_Equals trans_ex uu____9482)))
end);
))))
in (FStar_List.iter update_exports all_exported_id_kinds))
end
| uu____9606 -> begin
()
end));
(match (()) with
| () -> begin
env1
end);
)
end
| FStar_Pervasives_Native.None -> begin
(

let uu____9627 = (

let uu____9628 = (

let uu____9633 = (FStar_Util.format1 "include: Module %s was not prepared" ns1.FStar_Ident.str)
in ((uu____9633), ((FStar_Ident.range_of_lid ns1))))
in FStar_Errors.Error (uu____9628))
in (FStar_Exn.raise uu____9627))
end))
end);
)));
)
end
| uu____9634 -> begin
(

let uu____9637 = (

let uu____9638 = (

let uu____9643 = (FStar_Util.format1 "include: Module %s cannot be found" ns.FStar_Ident.str)
in ((uu____9643), ((FStar_Ident.range_of_lid ns))))
in FStar_Errors.Error (uu____9638))
in (FStar_Exn.raise uu____9637))
end))))


let push_module_abbrev : env  ->  FStar_Ident.ident  ->  FStar_Ident.lident  ->  env = (fun env x l -> (

let uu____9656 = (module_is_defined env l)
in (match (uu____9656) with
| true -> begin
((fail_if_curmodule env l l);
(env.ds_hooks.ds_push_module_abbrev_hook env x l);
(push_scope_mod env (Module_abbrev (((x), (l)))));
)
end
| uu____9659 -> begin
(

let uu____9660 = (

let uu____9661 = (

let uu____9666 = (FStar_Util.format1 "Module %s cannot be found" (FStar_Ident.text_of_lid l))
in ((uu____9666), ((FStar_Ident.range_of_lid l))))
in FStar_Errors.Error (uu____9661))
in (FStar_Exn.raise uu____9660))
end)))


let push_doc : env  ->  FStar_Ident.lident  ->  FStar_Parser_AST.fsdoc FStar_Pervasives_Native.option  ->  env = (fun env l doc_opt -> (match (doc_opt) with
| FStar_Pervasives_Native.None -> begin
env
end
| FStar_Pervasives_Native.Some (doc1) -> begin
((

let uu____9685 = (FStar_Util.smap_try_find env.docs l.FStar_Ident.str)
in (match (uu____9685) with
| FStar_Pervasives_Native.None -> begin
()
end
| FStar_Pervasives_Native.Some (old_doc) -> begin
(

let uu____9689 = (

let uu____9690 = (FStar_Ident.string_of_lid l)
in (

let uu____9691 = (FStar_Parser_AST.string_of_fsdoc old_doc)
in (

let uu____9692 = (FStar_Parser_AST.string_of_fsdoc doc1)
in (FStar_Util.format3 "Overwriting doc of %s; old doc was [%s]; new doc are [%s]" uu____9690 uu____9691 uu____9692))))
in (FStar_Errors.warn (FStar_Ident.range_of_lid l) uu____9689))
end));
(FStar_Util.smap_add env.docs l.FStar_Ident.str doc1);
env;
)
end))


let check_admits : env  ->  Prims.unit = (fun env -> (FStar_All.pipe_right env.sigaccum (FStar_List.iter (fun se -> (match (se.FStar_Syntax_Syntax.sigel) with
| FStar_Syntax_Syntax.Sig_declare_typ (l, u, t) -> begin
(

let uu____9709 = (try_lookup_lid env l)
in (match (uu____9709) with
| FStar_Pervasives_Native.None -> begin
((

let uu____9721 = (

let uu____9722 = (FStar_Options.interactive ())
in (not (uu____9722)))
in (match (uu____9721) with
| true -> begin
(

let uu____9723 = (

let uu____9724 = (FStar_Syntax_Print.lid_to_string l)
in (FStar_Util.format1 "Admitting %s without a definition" uu____9724))
in (FStar_Errors.warn (FStar_Ident.range_of_lid l) uu____9723))
end
| uu____9725 -> begin
()
end));
(

let quals = (FStar_Syntax_Syntax.Assumption)::se.FStar_Syntax_Syntax.sigquals
in (FStar_Util.smap_add (sigmap env) l.FStar_Ident.str (((

let uu___199_9734 = se
in {FStar_Syntax_Syntax.sigel = uu___199_9734.FStar_Syntax_Syntax.sigel; FStar_Syntax_Syntax.sigrng = uu___199_9734.FStar_Syntax_Syntax.sigrng; FStar_Syntax_Syntax.sigquals = quals; FStar_Syntax_Syntax.sigmeta = uu___199_9734.FStar_Syntax_Syntax.sigmeta; FStar_Syntax_Syntax.sigattrs = uu___199_9734.FStar_Syntax_Syntax.sigattrs})), (false))));
)
end
| FStar_Pervasives_Native.Some (uu____9735) -> begin
()
end))
end
| uu____9744 -> begin
()
end)))))


let finish : env  ->  FStar_Syntax_Syntax.modul  ->  env = (fun env modul -> ((FStar_All.pipe_right modul.FStar_Syntax_Syntax.declarations (FStar_List.iter (fun se -> (

let quals = se.FStar_Syntax_Syntax.sigquals
in (match (se.FStar_Syntax_Syntax.sigel) with
| FStar_Syntax_Syntax.Sig_bundle (ses, uu____9763) -> begin
(match (((FStar_List.contains FStar_Syntax_Syntax.Private quals) || (FStar_List.contains FStar_Syntax_Syntax.Abstract quals))) with
| true -> begin
(FStar_All.pipe_right ses (FStar_List.iter (fun se1 -> (match (se1.FStar_Syntax_Syntax.sigel) with
| FStar_Syntax_Syntax.Sig_datacon (lid, uu____9783, uu____9784, uu____9785, uu____9786, uu____9787) -> begin
(FStar_Util.smap_remove (sigmap env) lid.FStar_Ident.str)
end
| uu____9796 -> begin
()
end))))
end
| uu____9797 -> begin
()
end)
end
| FStar_Syntax_Syntax.Sig_declare_typ (lid, uu____9799, uu____9800) -> begin
(match ((FStar_List.contains FStar_Syntax_Syntax.Private quals)) with
| true -> begin
(FStar_Util.smap_remove (sigmap env) lid.FStar_Ident.str)
end
| uu____9805 -> begin
()
end)
end
| FStar_Syntax_Syntax.Sig_let ((uu____9806, lbs), uu____9808) -> begin
((match (((FStar_List.contains FStar_Syntax_Syntax.Private quals) || (FStar_List.contains FStar_Syntax_Syntax.Abstract quals))) with
| true -> begin
(FStar_All.pipe_right lbs (FStar_List.iter (fun lb -> (

let uu____9829 = (

let uu____9830 = (

let uu____9831 = (

let uu____9834 = (FStar_Util.right lb.FStar_Syntax_Syntax.lbname)
in uu____9834.FStar_Syntax_Syntax.fv_name)
in uu____9831.FStar_Syntax_Syntax.v)
in uu____9830.FStar_Ident.str)
in (FStar_Util.smap_remove (sigmap env) uu____9829)))))
end
| uu____9839 -> begin
()
end);
(match (((FStar_List.contains FStar_Syntax_Syntax.Abstract quals) && (not ((FStar_List.contains FStar_Syntax_Syntax.Private quals))))) with
| true -> begin
(FStar_All.pipe_right lbs (FStar_List.iter (fun lb -> (

let lid = (

let uu____9848 = (

let uu____9851 = (FStar_Util.right lb.FStar_Syntax_Syntax.lbname)
in uu____9851.FStar_Syntax_Syntax.fv_name)
in uu____9848.FStar_Syntax_Syntax.v)
in (

let quals1 = (FStar_Syntax_Syntax.Assumption)::quals
in (

let decl = (

let uu___200_9856 = se
in {FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_declare_typ (((lid), (lb.FStar_Syntax_Syntax.lbunivs), (lb.FStar_Syntax_Syntax.lbtyp))); FStar_Syntax_Syntax.sigrng = uu___200_9856.FStar_Syntax_Syntax.sigrng; FStar_Syntax_Syntax.sigquals = quals1; FStar_Syntax_Syntax.sigmeta = uu___200_9856.FStar_Syntax_Syntax.sigmeta; FStar_Syntax_Syntax.sigattrs = uu___200_9856.FStar_Syntax_Syntax.sigattrs})
in (FStar_Util.smap_add (sigmap env) lid.FStar_Ident.str ((decl), (false)))))))))
end
| uu____9865 -> begin
()
end);
)
end
| uu____9866 -> begin
()
end)))));
(

let curmod = (

let uu____9868 = (current_module env)
in uu____9868.FStar_Ident.str)
in ((

let uu____9870 = (

let uu____9887 = (get_exported_id_set env curmod)
in (

let uu____9894 = (get_trans_exported_id_set env curmod)
in ((uu____9887), (uu____9894))))
in (match (uu____9870) with
| (FStar_Pervasives_Native.Some (cur_ex), FStar_Pervasives_Native.Some (cur_trans_ex)) -> begin
(

let update_exports = (fun eikind -> (

let cur_ex_set = (

let uu____9948 = (cur_ex eikind)
in (FStar_ST.op_Bang uu____9948))
in (

let cur_trans_ex_set_ref = (cur_trans_ex eikind)
in (

let uu____10202 = (

let uu____10203 = (FStar_ST.op_Bang cur_trans_ex_set_ref)
in (FStar_Util.set_union cur_ex_set uu____10203))
in (FStar_ST.op_Colon_Equals cur_trans_ex_set_ref uu____10202)))))
in (FStar_List.iter update_exports all_exported_id_kinds))
end
| uu____10326 -> begin
()
end));
(match (()) with
| () -> begin
((filter_record_cache ());
(match (()) with
| () -> begin
(

let uu___201_10344 = env
in {curmodule = FStar_Pervasives_Native.None; curmonad = uu___201_10344.curmonad; modules = (((modul.FStar_Syntax_Syntax.name), (modul)))::env.modules; scope_mods = []; exported_ids = uu___201_10344.exported_ids; trans_exported_ids = uu___201_10344.trans_exported_ids; includes = uu___201_10344.includes; sigaccum = []; sigmap = uu___201_10344.sigmap; iface = uu___201_10344.iface; admitted_iface = uu___201_10344.admitted_iface; expect_typ = uu___201_10344.expect_typ; docs = uu___201_10344.docs; remaining_iface_decls = uu___201_10344.remaining_iface_decls; syntax_only = uu___201_10344.syntax_only; ds_hooks = uu___201_10344.ds_hooks})
end);
)
end);
));
))


let stack : env Prims.list FStar_ST.ref = (FStar_Util.mk_ref [])


let push : env  ->  env = (fun env -> ((push_record_cache ());
(

let uu____10368 = (

let uu____10371 = (FStar_ST.op_Bang stack)
in (env)::uu____10371)
in (FStar_ST.op_Colon_Equals stack uu____10368));
(

let uu___202_10474 = env
in (

let uu____10475 = (FStar_Util.smap_copy (sigmap env))
in (

let uu____10486 = (FStar_Util.smap_copy env.docs)
in {curmodule = uu___202_10474.curmodule; curmonad = uu___202_10474.curmonad; modules = uu___202_10474.modules; scope_mods = uu___202_10474.scope_mods; exported_ids = uu___202_10474.exported_ids; trans_exported_ids = uu___202_10474.trans_exported_ids; includes = uu___202_10474.includes; sigaccum = uu___202_10474.sigaccum; sigmap = uu____10475; iface = uu___202_10474.iface; admitted_iface = uu___202_10474.admitted_iface; expect_typ = uu___202_10474.expect_typ; docs = uu____10486; remaining_iface_decls = uu___202_10474.remaining_iface_decls; syntax_only = uu___202_10474.syntax_only; ds_hooks = uu___202_10474.ds_hooks})));
))


let pop : Prims.unit  ->  env = (fun uu____10492 -> (

let uu____10493 = (FStar_ST.op_Bang stack)
in (match (uu____10493) with
| (env)::tl1 -> begin
((pop_record_cache ());
(FStar_ST.op_Colon_Equals stack tl1);
env;
)
end
| uu____10602 -> begin
(failwith "Impossible: Too many pops")
end)))


let export_interface : FStar_Ident.lident  ->  env  ->  env = (fun m env -> (

let sigelt_in_m = (fun se -> (match ((FStar_Syntax_Util.lids_of_sigelt se)) with
| (l)::uu____10618 -> begin
(Prims.op_Equality l.FStar_Ident.nsstr m.FStar_Ident.str)
end
| uu____10621 -> begin
false
end))
in (

let sm = (sigmap env)
in (

let env1 = (pop ())
in (

let keys = (FStar_Util.smap_keys sm)
in (

let sm' = (sigmap env1)
in ((FStar_All.pipe_right keys (FStar_List.iter (fun k -> (

let uu____10655 = (FStar_Util.smap_try_find sm' k)
in (match (uu____10655) with
| FStar_Pervasives_Native.Some (se, true) when (sigelt_in_m se) -> begin
((FStar_Util.smap_remove sm' k);
(

let se1 = (match (se.FStar_Syntax_Syntax.sigel) with
| FStar_Syntax_Syntax.Sig_declare_typ (l, u, t) -> begin
(

let uu___203_10680 = se
in {FStar_Syntax_Syntax.sigel = uu___203_10680.FStar_Syntax_Syntax.sigel; FStar_Syntax_Syntax.sigrng = uu___203_10680.FStar_Syntax_Syntax.sigrng; FStar_Syntax_Syntax.sigquals = (FStar_Syntax_Syntax.Assumption)::se.FStar_Syntax_Syntax.sigquals; FStar_Syntax_Syntax.sigmeta = uu___203_10680.FStar_Syntax_Syntax.sigmeta; FStar_Syntax_Syntax.sigattrs = uu___203_10680.FStar_Syntax_Syntax.sigattrs})
end
| uu____10681 -> begin
se
end)
in (FStar_Util.smap_add sm' k ((se1), (false))));
)
end
| uu____10686 -> begin
()
end)))));
env1;
)))))))


let finish_module_or_interface : env  ->  FStar_Syntax_Syntax.modul  ->  env = (fun env modul -> ((match ((not (modul.FStar_Syntax_Syntax.is_interface))) with
| true -> begin
(check_admits env)
end
| uu____10702 -> begin
()
end);
(finish env modul);
))

type exported_ids =
{exported_id_terms : Prims.string Prims.list; exported_id_fields : Prims.string Prims.list}


let __proj__Mkexported_ids__item__exported_id_terms : exported_ids  ->  Prims.string Prims.list = (fun projectee -> (match (projectee) with
| {exported_id_terms = __fname__exported_id_terms; exported_id_fields = __fname__exported_id_fields} -> begin
__fname__exported_id_terms
end))


let __proj__Mkexported_ids__item__exported_id_fields : exported_ids  ->  Prims.string Prims.list = (fun projectee -> (match (projectee) with
| {exported_id_terms = __fname__exported_id_terms; exported_id_fields = __fname__exported_id_fields} -> begin
__fname__exported_id_fields
end))


let as_exported_ids : exported_id_set  ->  exported_ids = (fun e -> (

let terms = (

let uu____10771 = (

let uu____10774 = (e Exported_id_term_type)
in (FStar_ST.op_Bang uu____10774))
in (FStar_Util.set_elements uu____10771))
in (

let fields = (

let uu____11021 = (

let uu____11024 = (e Exported_id_field)
in (FStar_ST.op_Bang uu____11024))
in (FStar_Util.set_elements uu____11021))
in {exported_id_terms = terms; exported_id_fields = fields})))


let as_exported_id_set : exported_ids FStar_Pervasives_Native.option  ->  exported_id_kind  ->  Prims.string FStar_Util.set FStar_ST.ref = (fun e -> (match (e) with
| FStar_Pervasives_Native.None -> begin
(exported_id_set_new ())
end
| FStar_Pervasives_Native.Some (e1) -> begin
(

let terms = (

let uu____11301 = (FStar_Util.as_set e1.exported_id_terms FStar_Util.compare)
in (FStar_Util.mk_ref uu____11301))
in (

let fields = (

let uu____11311 = (FStar_Util.as_set e1.exported_id_fields FStar_Util.compare)
in (FStar_Util.mk_ref uu____11311))
in (fun uu___181_11316 -> (match (uu___181_11316) with
| Exported_id_term_type -> begin
terms
end
| Exported_id_field -> begin
fields
end))))
end))

type module_inclusion_info =
{mii_exported_ids : exported_ids FStar_Pervasives_Native.option; mii_trans_exported_ids : exported_ids FStar_Pervasives_Native.option; mii_includes : FStar_Ident.lident Prims.list FStar_Pervasives_Native.option}


let __proj__Mkmodule_inclusion_info__item__mii_exported_ids : module_inclusion_info  ->  exported_ids FStar_Pervasives_Native.option = (fun projectee -> (match (projectee) with
| {mii_exported_ids = __fname__mii_exported_ids; mii_trans_exported_ids = __fname__mii_trans_exported_ids; mii_includes = __fname__mii_includes} -> begin
__fname__mii_exported_ids
end))


let __proj__Mkmodule_inclusion_info__item__mii_trans_exported_ids : module_inclusion_info  ->  exported_ids FStar_Pervasives_Native.option = (fun projectee -> (match (projectee) with
| {mii_exported_ids = __fname__mii_exported_ids; mii_trans_exported_ids = __fname__mii_trans_exported_ids; mii_includes = __fname__mii_includes} -> begin
__fname__mii_trans_exported_ids
end))


let __proj__Mkmodule_inclusion_info__item__mii_includes : module_inclusion_info  ->  FStar_Ident.lident Prims.list FStar_Pervasives_Native.option = (fun projectee -> (match (projectee) with
| {mii_exported_ids = __fname__mii_exported_ids; mii_trans_exported_ids = __fname__mii_trans_exported_ids; mii_includes = __fname__mii_includes} -> begin
__fname__mii_includes
end))


let default_mii : module_inclusion_info = {mii_exported_ids = FStar_Pervasives_Native.None; mii_trans_exported_ids = FStar_Pervasives_Native.None; mii_includes = FStar_Pervasives_Native.None}


let as_includes : 'Auu____11429 . 'Auu____11429 Prims.list FStar_Pervasives_Native.option  ->  'Auu____11429 Prims.list FStar_ST.ref = (fun uu___182_11441 -> (match (uu___182_11441) with
| FStar_Pervasives_Native.None -> begin
(FStar_Util.mk_ref [])
end
| FStar_Pervasives_Native.Some (l) -> begin
(FStar_Util.mk_ref l)
end))


let inclusion_info : env  ->  FStar_Ident.lident  ->  module_inclusion_info = (fun env l -> (

let mname = (FStar_Ident.string_of_lid l)
in (

let as_ids_opt = (fun m -> (

let uu____11476 = (FStar_Util.smap_try_find m mname)
in (FStar_Util.map_opt uu____11476 as_exported_ids)))
in (

let uu____11479 = (as_ids_opt env.exported_ids)
in (

let uu____11482 = (as_ids_opt env.trans_exported_ids)
in (

let uu____11485 = (

let uu____11490 = (FStar_Util.smap_try_find env.includes mname)
in (FStar_Util.map_opt uu____11490 (fun r -> (FStar_ST.op_Bang r))))
in {mii_exported_ids = uu____11479; mii_trans_exported_ids = uu____11482; mii_includes = uu____11485}))))))


let prepare_module_or_interface : Prims.bool  ->  Prims.bool  ->  env  ->  FStar_Ident.lident  ->  module_inclusion_info  ->  (env * Prims.bool) = (fun intf admitted env mname mii -> (

let prep = (fun env1 -> (

let filename = (FStar_Util.strcat (FStar_Ident.text_of_lid mname) ".fst")
in (

let auto_open = (FStar_Parser_Dep.hard_coded_dependencies filename)
in (

let auto_open1 = (

let convert_kind = (fun uu___183_11630 -> (match (uu___183_11630) with
| FStar_Parser_Dep.Open_namespace -> begin
Open_namespace
end
| FStar_Parser_Dep.Open_module -> begin
Open_module
end))
in (FStar_List.map (fun uu____11642 -> (match (uu____11642) with
| (lid, kind) -> begin
((lid), ((convert_kind kind)))
end)) auto_open))
in (

let namespace_of_module = (match (((FStar_List.length mname.FStar_Ident.ns) > (Prims.parse_int "0"))) with
| true -> begin
(

let uu____11666 = (

let uu____11671 = (FStar_Ident.lid_of_ids mname.FStar_Ident.ns)
in ((uu____11671), (Open_namespace)))
in (uu____11666)::[])
end
| uu____11680 -> begin
[]
end)
in (

let auto_open2 = (FStar_List.append namespace_of_module (FStar_List.rev auto_open1))
in ((

let uu____11701 = (as_exported_id_set mii.mii_exported_ids)
in (FStar_Util.smap_add env1.exported_ids mname.FStar_Ident.str uu____11701));
(match (()) with
| () -> begin
((

let uu____11717 = (as_exported_id_set mii.mii_trans_exported_ids)
in (FStar_Util.smap_add env1.trans_exported_ids mname.FStar_Ident.str uu____11717));
(match (()) with
| () -> begin
((

let uu____11733 = (as_includes mii.mii_includes)
in (FStar_Util.smap_add env1.includes mname.FStar_Ident.str uu____11733));
(match (()) with
| () -> begin
(

let env' = (

let uu___204_11757 = env1
in (

let uu____11758 = (FStar_List.map (fun x -> Open_module_or_namespace (x)) auto_open2)
in {curmodule = FStar_Pervasives_Native.Some (mname); curmonad = uu___204_11757.curmonad; modules = uu___204_11757.modules; scope_mods = uu____11758; exported_ids = uu___204_11757.exported_ids; trans_exported_ids = uu___204_11757.trans_exported_ids; includes = uu___204_11757.includes; sigaccum = uu___204_11757.sigaccum; sigmap = env1.sigmap; iface = intf; admitted_iface = admitted; expect_typ = uu___204_11757.expect_typ; docs = uu___204_11757.docs; remaining_iface_decls = uu___204_11757.remaining_iface_decls; syntax_only = uu___204_11757.syntax_only; ds_hooks = uu___204_11757.ds_hooks}))
in ((FStar_List.iter (fun op -> (env1.ds_hooks.ds_push_open_hook env' op)) (FStar_List.rev auto_open2));
env';
))
end);
)
end);
)
end);
)))))))
in (

let uu____11770 = (FStar_All.pipe_right env.modules (FStar_Util.find_opt (fun uu____11796 -> (match (uu____11796) with
| (l, uu____11802) -> begin
(FStar_Ident.lid_equals l mname)
end))))
in (match (uu____11770) with
| FStar_Pervasives_Native.None -> begin
(

let uu____11811 = (prep env)
in ((uu____11811), (false)))
end
| FStar_Pervasives_Native.Some (uu____11812, m) -> begin
((

let uu____11819 = ((

let uu____11822 = (FStar_Options.interactive ())
in (not (uu____11822))) && ((not (m.FStar_Syntax_Syntax.is_interface)) || intf))
in (match (uu____11819) with
| true -> begin
(

let uu____11823 = (

let uu____11824 = (

let uu____11829 = (FStar_Util.format1 "Duplicate module or interface name: %s" mname.FStar_Ident.str)
in ((uu____11829), ((FStar_Ident.range_of_lid mname))))
in FStar_Errors.Error (uu____11824))
in (FStar_Exn.raise uu____11823))
end
| uu____11830 -> begin
()
end));
(

let uu____11831 = (

let uu____11832 = (push env)
in (prep uu____11832))
in ((uu____11831), (true)));
)
end))))


let enter_monad_scope : env  ->  FStar_Ident.ident  ->  env = (fun env mname -> (match (env.curmonad) with
| FStar_Pervasives_Native.Some (mname') -> begin
(FStar_Exn.raise (FStar_Errors.Error ((((Prims.strcat "Trying to define monad " (Prims.strcat mname.FStar_Ident.idText (Prims.strcat ", but already in monad scope " mname'.FStar_Ident.idText)))), (mname.FStar_Ident.idRange)))))
end
| FStar_Pervasives_Native.None -> begin
(

let uu___205_11842 = env
in {curmodule = uu___205_11842.curmodule; curmonad = FStar_Pervasives_Native.Some (mname); modules = uu___205_11842.modules; scope_mods = uu___205_11842.scope_mods; exported_ids = uu___205_11842.exported_ids; trans_exported_ids = uu___205_11842.trans_exported_ids; includes = uu___205_11842.includes; sigaccum = uu___205_11842.sigaccum; sigmap = uu___205_11842.sigmap; iface = uu___205_11842.iface; admitted_iface = uu___205_11842.admitted_iface; expect_typ = uu___205_11842.expect_typ; docs = uu___205_11842.docs; remaining_iface_decls = uu___205_11842.remaining_iface_decls; syntax_only = uu___205_11842.syntax_only; ds_hooks = uu___205_11842.ds_hooks})
end))


let fail_or : 'a . env  ->  (FStar_Ident.lident  ->  'a FStar_Pervasives_Native.option)  ->  FStar_Ident.lident  ->  'a = (fun env lookup lid -> (

let uu____11873 = (lookup lid)
in (match (uu____11873) with
| FStar_Pervasives_Native.None -> begin
(

let opened_modules = (FStar_List.map (fun uu____11886 -> (match (uu____11886) with
| (lid1, uu____11892) -> begin
(FStar_Ident.text_of_lid lid1)
end)) env.modules)
in (

let msg = (FStar_Util.format1 "Identifier not found: [%s]" (FStar_Ident.text_of_lid lid))
in (

let msg1 = (match ((Prims.op_Equality (FStar_List.length lid.FStar_Ident.ns) (Prims.parse_int "0"))) with
| true -> begin
msg
end
| uu____11895 -> begin
(

let modul = (

let uu____11897 = (FStar_Ident.lid_of_ids lid.FStar_Ident.ns)
in (FStar_Ident.set_lid_range uu____11897 (FStar_Ident.range_of_lid lid)))
in (

let uu____11898 = (resolve_module_name env modul true)
in (match (uu____11898) with
| FStar_Pervasives_Native.None -> begin
(

let opened_modules1 = (FStar_String.concat ", " opened_modules)
in (FStar_Util.format3 "%s\nModule %s does not belong to the list of modules in scope, namely %s" msg modul.FStar_Ident.str opened_modules1))
end
| FStar_Pervasives_Native.Some (modul') when (not ((FStar_List.existsb (fun m -> (Prims.op_Equality m modul'.FStar_Ident.str)) opened_modules))) -> begin
(

let opened_modules1 = (FStar_String.concat ", " opened_modules)
in (FStar_Util.format4 "%s\nModule %s resolved into %s, which does not belong to the list of modules in scope, namely %s" msg modul.FStar_Ident.str modul'.FStar_Ident.str opened_modules1))
end
| FStar_Pervasives_Native.Some (modul') -> begin
(FStar_Util.format4 "%s\nModule %s resolved into %s, definition %s not found" msg modul.FStar_Ident.str modul'.FStar_Ident.str lid.FStar_Ident.ident.FStar_Ident.idText)
end)))
end)
in (FStar_Exn.raise (FStar_Errors.Error (((msg1), ((FStar_Ident.range_of_lid lid)))))))))
end
| FStar_Pervasives_Native.Some (r) -> begin
r
end)))


let fail_or2 : 'a . (FStar_Ident.ident  ->  'a FStar_Pervasives_Native.option)  ->  FStar_Ident.ident  ->  'a = (fun lookup id -> (

let uu____11932 = (lookup id)
in (match (uu____11932) with
| FStar_Pervasives_Native.None -> begin
(FStar_Exn.raise (FStar_Errors.Error ((((Prims.strcat "Identifier not found [" (Prims.strcat id.FStar_Ident.idText "]"))), (id.FStar_Ident.idRange)))))
end
| FStar_Pervasives_Native.Some (r) -> begin
r
end)))




