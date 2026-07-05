/-
Copyright © 2026 François G. Dorais. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import UnicodeData.Core.PropertyAliases
public import UnicodeBasicCommon.CharacterDatabase
public import Std.Data.HashMap

namespace Unicode

public def PropertyValueAliases.txt := include_str "../../data-ucd/core/PropertyValueAliases.txt"

initialize PropertyValueAliases.data : Std.HashMap String.Slice Aliases ← do
  let stream := UCDStream.ofString PropertyValueAliases.txt
  let mut map := {}
  for record in stream do
    let prop := PropertyAliases.getLongName! record[0]!
    let key := record[2]!
    let val := #[key]
    let val := if record[1]! != key then val.push record[1]! else val
    let val := val ++ record[3:]
    let al := match map.get? prop with
      | some l => l
      | none => ⟨{},{}⟩
    map := map.insert prop {
        aliasMap := al.aliasMap.insert key val
        nameMap := al.nameMap.insertMany (val.map fun v => (v, key))
      }
  return map

/-- Get the long name of a property value -/
@[inline]
public def PropertyValueAliases.getLongName? (prop val : String.Slice) : Option String.Slice := do
  let prop ← PropertyAliases.getLongName? prop
  let al ← data.get? prop
  al.nameMap.get? val

@[inline, inherit_doc PropertyValueAliases.getLongName?]
public def PropertyValueAliases.getLongName! (prop val : String.Slice) : String.Slice :=
  getLongName? prop val |>.get!

/-- Get all aliases of a property value -/
@[inline]
public def PropertyValueAliases.getAliases? (prop val : String.Slice) : Option (Array String.Slice) := do
  let prop ← PropertyAliases.getLongName? prop
  let val ← getLongName? prop val
  let al ← data.get? prop
  al.aliasMap.get? val

@[inline, inherit_doc PropertyAliases.getAliases?]
public def PropertyValueAliases.getAliases! (prop val : String.Slice) : Array String.Slice :=
  getAliases? prop val |>.get!

/-- Get the short name of a property value -/
@[inline]
public def PropertyValueAliases.getShortName? (prop val : String.Slice) : Option String.Slice := do
  let a ← getAliases? prop val
  a[1]? <|> a[0]?

@[inline, inherit_doc PropertyValueAliases.getShortName?]
public def PropertyValueAliases.getShortName! (prop val : String.Slice) : String.Slice :=
  getShortName? prop val |>.get!
