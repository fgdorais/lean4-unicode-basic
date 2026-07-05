/-
Copyright © 2026 François G. Dorais. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
import UnicodeBasicCommon.CharacterDatabase
public import Std.Data.HashMap

namespace Unicode

/-- Type for list of aliases -/
public structure Aliases where
  aliasMap : Std.HashMap String.Slice (Array String.Slice)
  nameMap : Std.HashMap String.Slice String.Slice
deriving Inhabited

/-- Raw string form `PropertyAliases.txt` -/
protected def PropertyAliases.txt := include_str "../../data-ucd/core/PropertyAliases.txt"

initialize PropertyAliases.data : Aliases ← do
  let stream := UCDStream.ofString PropertyAliases.txt
  let mut al := ⟨{}, {}⟩
  for record in stream do
    let key := record[1]!
    let val := #[key]
    let val := if record[0]! != key then val.push record[0]! else val
    let val := val ++ record[2:]
    al := {
      aliasMap := al.aliasMap.insert key val
      nameMap := al.nameMap.insertMany (val.map fun v => (v, key))
    }
  return al

/-- Get the long name of a property -/
@[inline]
public def PropertyAliases.getLongName? (prop : String.Slice) : Option String.Slice := do
  data.nameMap.get? prop

@[inline, inherit_doc PropertyAliases.getLongName?]
public def PropertyAliases.getLongName! (prop : String.Slice) : String.Slice :=
  getLongName? prop |>.get!

/-- Get all aliases of a property -/
@[inline]
public def PropertyAliases.getAliases? (prop : String.Slice) : Option (Array String.Slice) := do
  let prop ← getLongName? prop
  data.aliasMap.get? prop

@[inline, inherit_doc PropertyAliases.getAliases?]
public def PropertyAliases.getAliases! (prop : String.Slice) : Array String.Slice :=
  getAliases? prop |>.get!

/-- Get the short name of a property -/
public def PropertyAliases.getShortName? (prop : String.Slice) : Option String.Slice := do
  let a ← getAliases? prop
  a[1]? <|> a[0]?

@[inline, inherit_doc PropertyAliases.getShortName?]
public def PropertyAliases.getShortName! (prop : String.Slice) : String.Slice :=
  getShortName? prop |>.get!
