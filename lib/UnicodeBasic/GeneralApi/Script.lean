/-
Copyright © 2023-2025 François G. Dorais. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import UnicodeBasic.TableLookup.Script
public import UnicodeBasic.Types.ScriptName.Basic
public import UnicodeBasic.Types.ScriptName.FromScript
public import UnicodeBasic.Types.ScriptName.ToFullName
public import UnicodeBasic.TableLookup.ScriptExtensions

/-!
  This file uses lookup tables:
  `Script`, `ScriptName`, `ScriptExtensions`.
-/

namespace Unicode

/-!
  ## Script ##
-/

/-- Get character script

  Unicode property: `Script`
-/
@[inline]
public def getScript (char : Char) : MaybeUnknownScript :=
  lookupScript char.val

/-- Get script name

  Returns `none` if the script code is unassigned.

  Unicode property: `Script`
-/
@[inline]
public def getScriptName? (s : Script) : String :=
  ScriptName.toFullName (ScriptName.fromScript s)

/-- Get character script extensions

  Unicode property: `Script_Extensions`
-/
@[inline]
public def getScriptExtensions (char : Char) : Array MaybeUnknownScript :=
  let scs := lookupScriptExtensions char.val
  if scs.isEmpty then #[lookupScript char.val] else scs.map MaybeUnknownScript.ofScript

/-- Check if character is part of a script

  This function checks the `Script` property of the character.
-/
@[inline]
public def isScript (sc : Script) (char : Char) : Bool :=
  if h : TableLookupTables.Script.BetweenOrEqStartEnd char.val then
    (TableLookupTables.Script.getInsideSparseRangeValueTable char.val h).elim false (fun sc' => sc' == sc)
  else
    false

@[inline]
public def isMaybeUnknownScript (sc : MaybeUnknownScript) (char : Char) : Bool :=
  lookupScript char.val == sc

/-- Check if character has a script extension

  This function checks the `Script_Extensions` property of the character.
  The `Script_Extensions` property includes the `Script` property.
-/
@[inline]
public def hasScript (sc : Script) (char : Char) : Bool :=
  getScriptExtensions char |>.contains (MaybeUnknownScript.ofScript sc)

end Unicode
