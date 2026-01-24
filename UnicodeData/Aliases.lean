/-
Copyright © 2026 François G. Dorais. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import Std.Data.HashMap
import UnicodeBasic.Types
import UnicodeBasic.CharacterDatabase

namespace Unicode

/-- Type for list of aliases -/
structure Aliases where
  aliasMap : Std.HashMap String.Slice (Array String.Slice)
  nameMap : Std.HashMap String.Slice String.Slice
deriving Inhabited

/-- Raw string form `PropertyAliases.txt` -/
protected def PropertyAliases.txt := include_str "../data/PropertyAliases.txt"

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
def PropertyAliases.getLongName? (prop : String.Slice) : Option String.Slice := do
  data.nameMap.get? prop

@[inline, inherit_doc PropertyAliases.getLongName?]
def PropertyAliases.getLongName! (prop : String.Slice) : String.Slice :=
  getLongName? prop |>.get!

/-- Get all aliases of a property -/
@[inline]
def PropertyAliases.getAliases? (prop : String.Slice) : Option (Array String.Slice) := do
  let prop ← getLongName? prop
  data.aliasMap.get? prop

@[inline, inherit_doc PropertyAliases.getAliases?]
def PropertyAliases.getAliases! (prop : String.Slice) : Array String.Slice :=
  getAliases? prop |>.get!

/-- Get the short name of a property -/
def PropertyAliases.getShortName? (prop : String.Slice) : Option String.Slice := do
  let a ← getAliases? prop
  a[1]? <|> a[0]?

@[inline, inherit_doc PropertyAliases.getShortName?]
def PropertyAliases.getShortName! (prop : String.Slice) : String.Slice :=
  getShortName? prop |>.get!

protected def PropertyValueAliases.txt := include_str "../data/PropertyValueAliases.txt"

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

/-- Get all values for a property -/
@[inline]
def PropertyAliases.getValues? (prop : String.Slice) : Option (Array String.Slice) := do
  let prop ← PropertyAliases.getLongName? prop
  let al ← PropertyValueAliases.data.get? prop
  return al.aliasMap.keysArray

@[inline, inherit_doc PropertyAliases.getValues?]
def PropertyAliases.getValues! (prop : String.Slice) : Array String.Slice :=
  getValues? prop |>.get!

/-- Get the long name of a property value -/
@[inline]
def PropertyValueAliases.getLongName? (prop val : String.Slice) : Option String.Slice := do
  let prop ← PropertyAliases.getLongName? prop
  let al ← data.get? prop
  al.nameMap.get? val

@[inline, inherit_doc PropertyValueAliases.getLongName?]
def PropertyValueAliases.getLongName! (prop val : String.Slice) : String.Slice :=
  getLongName? prop val |>.get!

/-- Get all aliases of a property value -/
@[inline]
def PropertyValueAliases.getAliases? (prop val : String.Slice) : Option (Array String.Slice) := do
  let prop ← PropertyAliases.getLongName? prop
  let val ← getLongName? prop val
  let al ← data.get? prop
  al.aliasMap.get? val

@[inline, inherit_doc PropertyAliases.getAliases?]
def PropertyValueAliases.getAliases! (prop val : String.Slice) : Array String.Slice :=
  getAliases? prop val |>.get!

/-- Get the short name of a property value -/
@[inline]
def PropertyValueAliases.getShortName? (prop val : String.Slice) : Option String.Slice := do
  let a ← getAliases? prop val
  a[1]? <|> a[0]?

@[inline, inherit_doc PropertyValueAliases.getShortName?]
def PropertyValueAliases.getShortName! (prop val : String.Slice) : String.Slice :=
  getShortName? prop val |>.get!

end Unicode
