/-
Copyright © 2026 François G. Dorais. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import UnicodeBasicCommon.Types.Hex
import UnicodeBasicCommon.CharacterDatabase

namespace Unicode

/-- Raw string from `DerivedNormalizationProps.txt` -/
def DerivedNormalizationProps.txt := include_str "../../data-ucd/core/DerivedNormalizationProps.txt"

/-- Trim ASCII whitespace from a string and materialize a `String`. -/
private def trimAsciiString (s : String) : String := (String.trimAscii s).copy

/-- Trim ASCII whitespace from a string slice and materialize a `String`. -/
private def trimAsciiSlice (s : String.Slice) : String := (String.Slice.trimAscii s).copy

/-- Strip trailing comments from a UCD line. -/
private def stripComment (s : String) : String :=
  trimAsciiSlice <| String.takeWhile s fun c => c != '#'

/-- Parse a hex range field. -/
private def parseRangeField (s : String) : UInt32 × UInt32 :=
  match (trimAsciiString s).splitOn ".." with
  | [c] => (ofHexString! c, ofHexString! c)
  | [c₀, c₁] => (ofHexString! c₀, ofHexString! c₁)
  | _ => panic! "invalid range in DerivedNormalizationProps.txt"

/-- Parse a code point sequence field. -/
private def parseMappingField (s : String) : Array UInt32 :=
  let s := trimAsciiString s
  if s.isEmpty || s == "<code point>" then
    #[]
  else
    let xs := s.splitOn " " |>.filter (· ≠ "")
    xs.map (fun x => ofHexString! x.toSlice) |>.toArray

/-- Parsed `DerivedNormalizationProps.txt` records. -/
public structure DerivedNormalizationProps where
  /-- `FC_NFKC_Closure` -/
  public fcNfkcClosure : Array (UInt32 × UInt32 × Array UInt32) := #[]
  /-- `Full_Composition_Exclusion` -/
  public fullCompositionExclusion : Array (UInt32 × UInt32) := #[]
  /-- `Expands_On_NFD` -/
  public expandsOnNfd : Array (UInt32 × UInt32) := #[]
  /-- `Expands_On_NFC` -/
  public expandsOnNfc : Array (UInt32 × UInt32) := #[]
  /-- `Expands_On_NFKD` -/
  public expandsOnNfkd : Array (UInt32 × UInt32) := #[]
  /-- `Expands_On_NFKC` -/
  public expandsOnNfkc : Array (UInt32 × UInt32) := #[]
  /-- `NFKC_Casefold` -/
  public nfkcCasefold : Array (UInt32 × UInt32 × Array UInt32) := #[]
  /-- `NFKC_Simple_Casefold` -/
  public nfkcSimpleCasefold : Array (UInt32 × UInt32 × Array UInt32) := #[]
  /-- `Changes_When_NFKC_Casefolded` -/
  public changesWhenNfkcCasefolded : Array (UInt32 × UInt32) := #[]
deriving Inhabited, Repr

/-- Parsed `DerivedNormalizationProps.txt` data. -/
public unsafe initialize DerivedNormalizationProps.data : DerivedNormalizationProps ←
  let mut props : DerivedNormalizationProps := {}
  let mut currentSection : String := ""
  for raw in DerivedNormalizationProps.txt.splitOn "\n" do
    let line := trimAsciiString raw
    if line.isEmpty then
      continue
    else if line.startsWith "# " then
      if line.startsWith "# Derived Property:" then
        currentSection := trimAsciiSlice <| line.drop "# Derived Property:".length
      continue
    else
      let line := stripComment line
      if line.isEmpty then
        continue
      let parts := line.splitOn ";"
      match parts with
      | [range, _prop, value] =>
        let (c₀, c₁) := parseRangeField range
        let _value := trimAsciiSlice value
        let seq :=
          if currentSection.startsWith "FC_NFKC_Closure" ||
             currentSection.startsWith "NFKC_Casefold" ||
             currentSection.startsWith "NFKC_Simple_Casefold" then
            parseMappingField value
          else
            #[]
        if currentSection.startsWith "FC_NFKC_Closure" then
          props := {props with fcNfkcClosure := props.fcNfkcClosure.push (c₀, c₁, seq)}
        else if currentSection == "Full_Composition_Exclusion" then
          props := {props with fullCompositionExclusion := props.fullCompositionExclusion.push (c₀, c₁)}
        else if currentSection.startsWith "Expands_On_NFD" then
          props := {props with expandsOnNfd := props.expandsOnNfd.push (c₀, c₁)}
        else if currentSection.startsWith "Expands_On_NFC" then
          props := {props with expandsOnNfc := props.expandsOnNfc.push (c₀, c₁)}
        else if currentSection.startsWith "Expands_On_NFKD" then
          props := {props with expandsOnNfkd := props.expandsOnNfkd.push (c₀, c₁)}
        else if currentSection.startsWith "Expands_On_NFKC" then
          props := {props with expandsOnNfkc := props.expandsOnNfkc.push (c₀, c₁)}
        else if currentSection.startsWith "NFKC_Casefold" then
          props := {props with nfkcCasefold := props.nfkcCasefold.push (c₀, c₁, seq)}
        else if currentSection.startsWith "NFKC_Simple_Casefold" then
          props := {props with nfkcSimpleCasefold := props.nfkcSimpleCasefold.push (c₀, c₁, seq)}
        else if currentSection.startsWith "Changes_When_NFKC_Casefolded" then
          props := {props with changesWhenNfkcCasefolded := props.changesWhenNfkcCasefolded.push (c₀, c₁)}
        else
          continue
      | _ => continue
  return props

private partial def findSet (code : UInt32) (data : Array (UInt32 × UInt32)) (lo hi : Nat) : Bool :=
  if _ : lo < hi then
    let mid := lo + (hi - lo) / 2
    let (c₀, c₁) := data[mid]!
    if code < c₀ then
      findSet code data lo mid
    else if c₁ < code then
      findSet code data (mid + 1) hi
    else
      true
  else
    false

private partial def findMap (code : UInt32) (data : Array (UInt32 × UInt32 × Array UInt32))
    (lo hi : Nat) : Option (Array UInt32) :=
  if _ : lo < hi then
    let mid := lo + (hi - lo) / 2
    let (c₀, c₁, v) := data[mid]!
    if code < c₀ then
      findMap code data lo mid
    else if c₁ < code then
      findMap code data (mid + 1) hi
    else
      some v
  else
    none

/-- Check whether a code point is in `Full_Composition_Exclusion`. -/
public def isFullCompositionExclusion (code : UInt32) : Bool :=
  findSet code DerivedNormalizationProps.data.fullCompositionExclusion 0
    DerivedNormalizationProps.data.fullCompositionExclusion.size

/-- Check whether a code point expands on NFD. -/
public def expandsOnNFD (code : UInt32) : Bool :=
  findSet code DerivedNormalizationProps.data.expandsOnNfd 0
    DerivedNormalizationProps.data.expandsOnNfd.size

/-- Check whether a code point expands on NFC. -/
public def expandsOnNFC (code : UInt32) : Bool :=
  findSet code DerivedNormalizationProps.data.expandsOnNfc 0
    DerivedNormalizationProps.data.expandsOnNfc.size

/-- Check whether a code point expands on NFKD. -/
public def expandsOnNFKD (code : UInt32) : Bool :=
  findSet code DerivedNormalizationProps.data.expandsOnNfkd 0
    DerivedNormalizationProps.data.expandsOnNfkd.size

/-- Check whether a code point expands on NFKC. -/
public def expandsOnNFKC (code : UInt32) : Bool :=
  findSet code DerivedNormalizationProps.data.expandsOnNfkc 0
    DerivedNormalizationProps.data.expandsOnNfkc.size

/-- Lookup the NFKC casefold mapping, if explicitly listed. -/
public def lookupNFKCCasefold? (code : UInt32) : Option (Array UInt32) :=
  findMap code DerivedNormalizationProps.data.nfkcCasefold 0
    DerivedNormalizationProps.data.nfkcCasefold.size

/-- Lookup the NFKC simple casefold mapping, if explicitly listed. -/
public def lookupNFKCSimpleCasefold? (code : UInt32) : Option (Array UInt32) :=
  findMap code DerivedNormalizationProps.data.nfkcSimpleCasefold 0
    DerivedNormalizationProps.data.nfkcSimpleCasefold.size

end Unicode
