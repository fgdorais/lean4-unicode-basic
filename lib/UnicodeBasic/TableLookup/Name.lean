/-
Copyright © 2024-2025 François G. Dorais. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import UnicodeBasicCommon.Hangul
public import UnicodeBasicCommon.Types.Hex
public import UnicodeBasic.TableLookupCommon
public import UnicodeBasic.TableLookupTables.Name

namespace Unicode

/-- Get name of a code point using lookup table

  Unicode property: `Name` -/
public def lookupName (c : UInt32) : String :=
  if h : TableLookupTables.Name.BetweenOrEqStartEnd c then
    match TableLookupTables.Name.getInsideSparseRangeValueTable c h with
    | some d =>
      if "<".isPrefixOf d then
        if d == "<Control>" then
          s!"<control-{toHexStringRaw c}>"
        else if d == "<Private Use>" then
          s!"<private-use-{toHexStringRaw c}>"
        else if d == "<Reserved>" then
          s!"<reserved-{toHexStringRaw c}>"
        else if d == "<Surrogate>" then
          s!"<surrogate-{toHexStringRaw c}>"
        else if d == "<CJK Unified Ideograph>" then
          "CJK UNIFIED IDEOGRAPH-" ++ toHexStringRaw c
        else if d == "<CJK Compatibility Ideograph>" then
          "CJK COMPATIBILITY IDEOGRAPH-" ++ toHexStringRaw c
        else if d == "<Hangul Syllable>" then
          "HANGUL SYLLABLE " ++ (Hangul.getSyllable! c).getShortName -- can we also returh proof with return type?
        else if d == "<Khitan Small Script Character>" then
          "KHITAN SMALL SCRIPT CHARACTER-" ++ toHexStringRaw c
        else if d == "<Nushu Character>" then
          "NUSHU CHARACTER-" ++ toHexStringRaw c
        else if d == "<Tangut Component>" then
          let i := if c.toNat < 0x18B00 then
              -- Tangut Component
              toString <| c.toNat - 0x18800 + 1
            else
              -- Tangut Component Supplement
              toString <| c.toNat - 0x18D80 + 769
          let i :=
            if i.length == 1 then "00" ++ i
            else if i.length == 2 then "0" ++ i
            else i
          "TANGUT COMPONENT-" ++ i
        else if d == "<Tangut Ideograph>" then
          "TANGUT IDEOGRAPH-" ++ toHexStringRaw c
        else panic! s!"unknown name range {d}"
      else d
    | none => s!"<noncharacter-{toHexStringRaw c}>"
  else
    s!"<noncharacter-{toHexStringRaw c}>"
