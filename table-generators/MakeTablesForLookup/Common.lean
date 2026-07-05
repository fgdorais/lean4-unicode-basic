module
public import UnicodeBasicCommon.Types.Hex
public import UnicodeBasicCommon.Types.Script
public import UnicodeBasicCommon.CharacterDatabase

@[expose] public section

open Unicode

namespace MakeTablesForLookup

public inductive TableKind where
  | prop
  | simpleHex
  | hexList
  | caseFolding
  | rangeNat
  | rangeUInt32
  | caseMapping
  | bidiClass
  | bidiBracket
  | blockName
  | eastAsianWidth
  | verticalOrientation
  | decomposition
  | name
  | numericValue
  | script
  | scriptExtensions
  | graphemeBreak
  | wordBreak
  | sentenceBreak
  | lineBreak

public structure TableSpec where
  fileName : String
  moduleName : String
  imports : Array String := #[]
  type : String
  kind : TableKind

public def specs : Array TableSpec := #[
  ⟨"Alphabetic", "Alphabetic", #[], "Array (UInt32 × UInt32)", .prop⟩,
  ⟨"Bidi_Class", "BidiClass", #["UnicodeBasicCommon.Types.BidiClass"], "Array (UInt32 × UInt32 × BidiClass)", .bidiClass⟩,
  ⟨"Bidi_Mirroring_Glyph", "BidiMirroringGlyph", #[], "Array (UInt32 × UInt32)", .simpleHex⟩,
  ⟨"Bidi_Brackets", "BidiBrackets", #["UnicodeBasic.LookupTypes.BidiBracket", "UnicodeBasicCommon.Types.BidiBracketType"], "Array (UInt32 × BidiBracket)", .bidiBracket⟩,
  ⟨"Block_Name", "BlockName", #["UnicodeBasic.Types.BlockName"], "Array (UInt32 × UInt32 × BlockName)", .blockName⟩,
  ⟨"East_Asian_Width", "EastAsianWidth", #["UnicodeBasicCommon.Types.EastAsianWidth"], "Array (UInt32 × UInt32 × EastAsianWidth)", .eastAsianWidth⟩,
  ⟨"Vertical_Orientation", "VerticalOrientation", #["UnicodeBasicCommon.Types.VerticalOrientation"], "Array (UInt32 × UInt32 × VerticalOrientation)", .verticalOrientation⟩,
  ⟨"Canonical_Combining_Class", "CanonicalCombiningClass", #[], "Array (UInt32 × UInt32 × Nat)", .rangeNat⟩,
  ⟨"Canonical_Decomposition_Mapping", "CanonicalDecompositionMapping", #["UnicodeBasic.LookupTypes.CanonicalDecomposition"], "Array (UInt32 × CanonicalDecomposition)", .hexList⟩,
  ⟨"Case_Mapping", "CaseMapping", #[], "Array (UInt32 × UInt32 × UInt32 × UInt32 × UInt32)", .caseMapping⟩,
  ⟨"Cased", "Cased", #[], "Array (UInt32 × UInt32)", .prop⟩,
  ⟨"Decomposition_Mapping", "DecompositionMapping", #["UnicodeBasicCommon.Types.DecompositionMapping"], "Array (UInt32 × DecompositionMapping)", .decomposition⟩,
  ⟨"Name", "Name", #[], "Array (UInt32 × UInt32 × String)", .name⟩,
  ⟨"Numeric_Value", "NumericValue", #["UnicodeBasicCommon.Types.NumericType"], "Array (UInt32 × UInt32 × NumericType)", .numericValue⟩,
  ⟨"General_Category", "GeneralCategory", #[], "Array (UInt32 × UInt32 × UInt32)", .rangeUInt32⟩,
  ⟨"Lowercase", "Lowercase", #[], "Array (UInt32 × UInt32)", .prop⟩,
  ⟨"Math", "Math", #[], "Array (UInt32 × UInt32)", .prop⟩,
  ⟨"Other_Alphabetic", "OtherAlphabetic", #[], "Array (UInt32 × UInt32)", .prop⟩,
  ⟨"Other_Lowercase", "OtherLowercase", #[], "Array (UInt32 × UInt32)", .prop⟩,
  ⟨"Other_Math", "OtherMath", #[], "Array (UInt32 × UInt32)", .prop⟩,
  ⟨"Other_Uppercase", "OtherUppercase", #[], "Array (UInt32 × UInt32)", .prop⟩,
  ⟨"Bidi_Mirrored", "BidiMirrored", #[], "Array (UInt32 × UInt32)", .prop⟩,
  ⟨"Default_Ignorable_Code_Point", "DefaultIgnorableCodePoint", #[], "Array (UInt32 × UInt32)", .prop⟩,
  ⟨"White_Space", "WhiteSpace", #[], "Array (UInt32 × UInt32)", .prop⟩,
  ⟨"Script", "Script", #["UnicodeBasicCommon.Types.Script"], "Array (UInt32 × UInt32 × Script)", .script⟩,
  ⟨"Script_Extensions", "ScriptExtensions", #["UnicodeBasic.LookupTypes.ScriptExtensions", "UnicodeBasicCommon.Types.Script"], "Array (UInt32 × ScriptExtensionsEntry)", .scriptExtensions⟩,
  ⟨"ID_Start", "IdStart", #[], "Array (UInt32 × UInt32)", .prop⟩,
  ⟨"ID_Continue", "IdContinue", #[], "Array (UInt32 × UInt32)", .prop⟩,
  ⟨"XID_Start", "XidStart", #[], "Array (UInt32 × UInt32)", .prop⟩,
  ⟨"XID_Continue", "XidContinue", #[], "Array (UInt32 × UInt32)", .prop⟩,
  ⟨"Dash", "Dash", #[], "Array (UInt32 × UInt32)", .prop⟩,
  ⟨"Hyphen", "Hyphen", #[], "Array (UInt32 × UInt32)", .prop⟩,
  ⟨"Quotation_Mark", "QuotationMark", #[], "Array (UInt32 × UInt32)", .prop⟩,
  ⟨"Terminal_Punctuation", "TerminalPunctuation", #[], "Array (UInt32 × UInt32)", .prop⟩,
  ⟨"Extender", "Extender", #[], "Array (UInt32 × UInt32)", .prop⟩,
  ⟨"Regional_Indicator", "RegionalIndicator", #[], "Array (UInt32 × UInt32)", .prop⟩,
  ⟨"Case_Folding", "CaseFolding", #["UnicodeBasic.LookupTypes.CaseFolding"], "Array (UInt32 × CaseFolding)", .caseFolding⟩,
  ⟨"Simple_Case_Folding", "SimpleCaseFolding", #[], "Array (UInt32 × UInt32)", .simpleHex⟩,
  ⟨"Grapheme_Break", "GraphemeBreak", #["UnicodeBasic.Types.GraphemeClusterBreak"], "Array (UInt32 × UInt32 × GraphemeClusterBreak)", .graphemeBreak⟩,
  ⟨"Word_Break", "WordBreak", #["UnicodeBasic.Types.WordBreak"], "Array (UInt32 × UInt32 × WordBreak)", .wordBreak⟩,
  ⟨"Diacritic", "Diacritic", #[], "Array (UInt32 × UInt32)", .prop⟩,
  ⟨"Sentence_Terminal", "SentenceTerminal", #[], "Array (UInt32 × UInt32)", .prop⟩,
  ⟨"Pattern_Syntax", "PatternSyntax", #[], "Array (UInt32 × UInt32)", .prop⟩,
  ⟨"Pattern_White_Space", "PatternWhiteSpace", #[], "Array (UInt32 × UInt32)", .prop⟩,
  ⟨"Emoji", "Emoji", #[], "Array (UInt32 × UInt32)", .prop⟩,
  ⟨"Emoji_Presentation", "EmojiPresentation", #[], "Array (UInt32 × UInt32)", .prop⟩,
  ⟨"Emoji_Modifier", "EmojiModifier", #[], "Array (UInt32 × UInt32)", .prop⟩,
  ⟨"Emoji_Modifier_Base", "EmojiModifierBase", #[], "Array (UInt32 × UInt32)", .prop⟩,
  ⟨"Emoji_Component", "EmojiComponent", #[], "Array (UInt32 × UInt32)", .prop⟩,
  ⟨"Extended_Pictographic", "ExtendedPictographic", #[], "Array (UInt32 × UInt32)", .prop⟩,
  ⟨"Sentence_Break", "SentenceBreak", #["UnicodeBasic.Types.SentenceBreak"], "Array (UInt32 × UInt32 × SentenceBreak)", .sentenceBreak⟩,
  ⟨"Line_Break", "LineBreak", #["UnicodeBasicCommon.Types.LineBreak"], "Array (UInt32 × UInt32 × LineBreak)", .lineBreak⟩,
  ⟨"Grapheme_Base", "GraphemeBase", #[], "Array (UInt32 × UInt32)", .prop⟩,
  ⟨"Grapheme_Extend", "GraphemeExtend", #[], "Array (UInt32 × UInt32)", .prop⟩,
  ⟨"Uppercase", "Uppercase", #[], "Array (UInt32 × UInt32)", .prop⟩
]

def hex (c : UInt32) : String :=
  s!"(0x{toHexStringRaw c} : UInt32)"

def str (s : String) : String :=
  reprStr s

def rangeOfRecord (record : Array String.Slice) : UInt32 × UInt32 :=
  let start := ofHexString! record[0]!
  let stop := if record[1]!.isEmpty then start else ofHexString! record[1]!
  (start, stop)

def bidiClass (abbr : String.Slice) : String :=
  match abbr.copy with
  | "L" => "BidiClass.leftToRight" | "R" => "BidiClass.rightToLeft" | "AL" => "BidiClass.arabicLetter"
  | "EN" => "BidiClass.europeanNumber" | "ES" => "BidiClass.europeanSeparator" | "ET" => "BidiClass.europeanTerminator"
  | "AN" => "BidiClass.arabicNumber" | "CS" => "BidiClass.commonSeparator" | "NSM" => "BidiClass.nonspacingMark"
  | "BN" => "BidiClass.boundaryNeutral" | "B" => "BidiClass.paragraphSeparator" | "S" => "BidiClass.segmentSeparator"
  | "WS" => "BidiClass.whiteSpace" | "ON" => "BidiClass.otherNeutral" | "LRE" => "BidiClass.leftToRightEmbedding"
  | "LRO" => "BidiClass.leftToRightOverride" | "RLE" => "BidiClass.rightToLeftEmbeding" | "RLO" => "BidiClass.rightToLeftOverride"
  | "PDF" => "BidiClass.popDirectionalFormat" | "LRI" => "BidiClass.leftToRightIsolate" | "RLI" => "BidiClass.rightToLeftIsolate"
  | "FSI" => "BidiClass.firstStrongIsolate" | "PDI" => "BidiClass.popDirectionalIsolate"
  | s => panic! s!"invalid Bidi_Class {s}"

def bracketType (abbr : String.Slice) : String :=
  match abbr.copy with
  | "o" => "BidiBracketType.openBracket"
  | "c" => "BidiBracketType.closeBracket"
  | s => panic! s!"invalid Bidi_Paired_Bracket_Type {s}"

def eastAsianWidth (abbr : String.Slice) : String :=
  match abbr.copy with
  | "A" => "EastAsianWidth.ambiguous" | "F" => "EastAsianWidth.fullwidth" | "H" => "EastAsianWidth.halfwidth"
  | "N" => "EastAsianWidth.neutral" | "Na" => "EastAsianWidth.narrow" | "W" => "EastAsianWidth.wide"
  | s => panic! s!"invalid East_Asian_Width {s}"

def verticalOrientation (abbr : String.Slice) : String :=
  match abbr.copy with
  | "U" => "VerticalOrientation.upright" | "R" => "VerticalOrientation.rotated" | "Tu" => "VerticalOrientation.transformedUpright"
  | "Tr" => "VerticalOrientation.transformedRotated"
  | s => panic! s!"invalid Vertical_Orientation {s}"

def compatibilityTag (s : String.Slice) : String :=
  if s.isEmpty then "none" else
    "(some " ++ match s.copy with
      | "<font>" => "CompatibilityTag.font" | "<noBreak>" => "CompatibilityTag.noBreak" | "<initial>" => "CompatibilityTag.initial"
      | "<medial>" => "CompatibilityTag.medial" | "<final>" => "CompatibilityTag.final" | "<isolated>" => "CompatibilityTag.isolated"
      | "<circle>" => "CompatibilityTag.circle" | "<super>" => "CompatibilityTag.super" | "<sub>" => "CompatibilityTag.sub"
      | "<vertical>" => "CompatibilityTag.vertical" | "<wide>" => "CompatibilityTag.wide" | "<narrow>" => "CompatibilityTag.narrow"
      | "<small>" => "CompatibilityTag.small" | "<square>" => "CompatibilityTag.square" | "<fraction>" => "CompatibilityTag.fraction"
      | "<compat>" => "CompatibilityTag.compat"
      | s => panic! s!"invalid compatibility tag {s}"
    ++ ")"

def numericType (s : String.Slice) : String :=
  let s := s.copy
  if s == "decimal" then
    "NumericType.decimal 0"
  else if "digit".isPrefixOf s then
    let d := (String.Pos.Raw.get s ⟨6⟩).toNat
    let v := d - '0'.toNat
    if d < '0'.toNat || 10 ≤ v then
      panic! s!"invalid digit value {s}"
    else
      s!"NumericType.digit ⟨{v}, by decide⟩"
  else if "numeric".isPrefixOf s then
    match (s.drop 8).split "/" |>.toStringList with
    | [n] => s!"NumericType.numeric ({n} : Int) none"
    | [n, d] => s!"NumericType.numeric ({n} : Int) (some {d})"
    | _ => panic! "invalid numeric value"
  else
    panic! s!"invalid numeric type {s}"

def graphemeBreak (abbr : String.Slice) : String :=
  match abbr.copy with
  | "Other" => panic! "GraphemeClusterBreak.other is not supported" | "Control" => "GraphemeClusterBreak.control" | "CR" => "GraphemeClusterBreak.cr" | "Extend" => "GraphemeClusterBreak.extend"
  | "LF" => "GraphemeClusterBreak.lf" | "SpacingMark" => "GraphemeClusterBreak.spacingMark" | "Prepend" => "GraphemeClusterBreak.prepend"
  | "Regional_Indicator" => "GraphemeClusterBreak.regionalIndicator" | "L" => "GraphemeClusterBreak.l" | "V" => "GraphemeClusterBreak.v"
  | "T" => "GraphemeClusterBreak.t" | "LV" => "GraphemeClusterBreak.lv" | "LVT" => "GraphemeClusterBreak.lvt" | "ZWJ" => "GraphemeClusterBreak.zwj"
  | s => panic! s!"invalid Grapheme_Break {s}"

def wordBreak (abbr : String.Slice) : String :=
  match abbr.copy with
  | "Other" => "WordBreak.other" | "Double_Quote" => "WordBreak.doubleQuote" | "Single_Quote" => "WordBreak.singleQuote"
  | "Hebrew_Letter" => "WordBreak.hebrewLetter" | "CR" => "WordBreak.cr" | "LF" => "WordBreak.lf" | "Newline" => "WordBreak.newline"
  | "Extend" => "WordBreak.extend" | "Regional_Indicator" => "WordBreak.regionalIndicator" | "Katakana" => "WordBreak.katakana"
  | "ALetter" => "WordBreak.aLetter" | "MidLetter" => "WordBreak.midLetter" | "MidNum" => "WordBreak.midNum"
  | "MidNumLet" => "WordBreak.midNumLet" | "Numeric" => "WordBreak.numeric" | "ExtendNumLet" => "WordBreak.extendNumLet"
  | "WSegSpace" => "WordBreak.wSegSpace" | "ZWJ" => "WordBreak.zwj" | "Format" => "WordBreak.format"
  | s => panic! s!"invalid Word_Break {s}"

def sentenceBreak (abbr : String.Slice) : String :=
  match abbr.copy with
  | "Other" => panic! "SentenceBreak.other is not supported" | "ATerm" => "SentenceBreak.aTerm" | "CR" => "SentenceBreak.cr" | "Close" => "SentenceBreak.close"
  | "Extend" => "SentenceBreak.extend" | "Format" => "SentenceBreak.format" | "LF" => "SentenceBreak.lf" | "Lower" => "SentenceBreak.lower"
  | "Numeric" => "SentenceBreak.numeric" | "OLetter" => "SentenceBreak.oLetter" | "SContinue" => "SentenceBreak.sContinue"
  | "STerm" => "SentenceBreak.sTerm" | "Sep" => "SentenceBreak.sep" | "Sp" => "SentenceBreak.sp" | "Upper" => "SentenceBreak.upper"
  | s => panic! s!"invalid Sentence_Break {s}"

def lineBreak (abbr : String.Slice) : String :=
  match abbr.copy with
  | "XX" => "LineBreak.unknown" | "AI" => "LineBreak.ambiguous" | "AK" => "LineBreak.aksara" | "AP" => "LineBreak.aksaraPrebase"
  | "AS" => "LineBreak.aksaraStart" | "AL" => "LineBreak.alphabetic" | "BA" => "LineBreak.breakAfter" | "BB" => "LineBreak.breakBefore"
  | "B2" => "LineBreak.breakBoth" | "BK" => "LineBreak.mandatoryBreak" | "CR" => "LineBreak.carriageReturn" | "CB" => "LineBreak.contingentBreak"
  | "CP" => "LineBreak.closeParenthesis" | "CL" => "LineBreak.closePunctuation" | "CM" => "LineBreak.combiningMark"
  | "CJ" => "LineBreak.conditionalJapaneseStarter" | "EB" => "LineBreak.eBase" | "EM" => "LineBreak.eModifier" | "EX" => "LineBreak.exclamation"
  | "GL" => "LineBreak.glue" | "H2" => "LineBreak.h2" | "H3" => "LineBreak.h3" | "HY" => "LineBreak.hyphen" | "HH" => "LineBreak.unambiguousHyphen"
  | "HL" => "LineBreak.hebrewLetter" | "ID" => "LineBreak.ideographic" | "IN" => "LineBreak.inseparable" | "IS" => "LineBreak.infixNumeric"
  | "JL" => "LineBreak.jl" | "JT" => "LineBreak.jt" | "JV" => "LineBreak.jv" | "LF" => "LineBreak.lineFeed" | "NL" => "LineBreak.nextLine"
  | "NS" => "LineBreak.nonstarter" | "NU" => "LineBreak.numeric" | "OP" => "LineBreak.openPunctuation" | "PO" => "LineBreak.postfixNumeric"
  | "PR" => "LineBreak.prefixNumeric" | "QU" => "LineBreak.quotation" | "RI" => "LineBreak.regionalIndicator" | "SA" => "LineBreak.complexContext"
  | "SG" => "LineBreak.surrogate" | "SP" => "LineBreak.space" | "SY" => "LineBreak.breakSymbols" | "VF" => "LineBreak.viramaFinal"
  | "VI" => "LineBreak.virama" | "WJ" => "LineBreak.wordJoiner" | "ZW" => "LineBreak.zwSpace" | "ZWJ" => "LineBreak.zwj"
  | s => panic! s!"invalid Line_Break {s}"

def renderRows (kind : TableKind) (txt : String) : Array String := Id.run do
  let mut rows := #[]
  let mut stream := UCDStream.ofString txt
  for record in stream do
    let start := ofHexString! record[0]!
    let row ← match kind with
    | .prop =>
      let (stop, _) := (if record[1]!.isEmpty then (start, ()) else (ofHexString! record[1]!, ()))
      pure s!"  ({hex start}, {hex stop})"
    | .simpleHex =>
      pure s!"  ({hex start}, {hex <| ofHexString! record[1]!})"
    | .hexList =>
      let vals := String.intercalate ", " <| record[1:].toList.map fun c => hex <| ofHexString! c
      pure s!"  ({hex start}, CanonicalDecomposition.mk [{vals}])"
    | .caseFolding =>
      let vals := String.intercalate ", " <| record[1]!.split ";" |>.toList.map fun c => hex <| ofHexString! c
      pure s!"  ({hex start}, #[{vals}])"
    | .rangeNat =>
      let (start, stop) := rangeOfRecord record
      pure s!"  ({hex start}, {hex stop}, {record[2]!.copy})"
    | .rangeUInt32 =>
      let (start, stop) := rangeOfRecord record
      pure s!"  ({hex start}, {hex stop}, ({record[2]!.copy} : UInt32))"
    | .caseMapping =>
      let stop := if record[1]!.isEmpty then start else ofHexString! record[1]!
      let upper := if record[2]!.isEmpty then start else ofHexString! record[2]!
      let lower := if record[3]!.isEmpty then start else ofHexString! record[3]!
      let title := if record[4]!.isEmpty then upper else ofHexString! record[4]!
      pure s!"  ({hex start}, {hex stop}, {hex upper}, {hex lower}, {hex title})"
    | .bidiClass =>
      let (start, stop) := rangeOfRecord record
      pure s!"  ({hex start}, {hex stop}, {bidiClass record[2]!})"
    | .bidiBracket =>
      let paired := hex <| ofHexString! record[1]!
      let value := "BidiBracket.mk " ++ paired ++ " " ++ bracketType record[2]!
      pure s!"  ({hex start}, {value})"
    | .blockName =>
      let (start, stop) := rangeOfRecord record
      pure s!"  ({hex start}, {hex stop}, {str record[2]!.copy})"
    | .eastAsianWidth =>
      let (start, stop) := rangeOfRecord record
      pure s!"  ({hex start}, {hex stop}, {eastAsianWidth record[2]!})"
    | .verticalOrientation =>
      let (start, stop) := rangeOfRecord record
      pure s!"  ({hex start}, {hex stop}, {verticalOrientation record[2]!})"
    | .decomposition =>
      let vals := String.intercalate ", " <| record[2:].toList.map fun c => s!"Char.ofNat {ofHexString! c}"
      pure s!"  ({hex start}, DecompositionMapping.mk {compatibilityTag record[1]!} [{vals}])"
    | .name =>
      let (start, stop) := rangeOfRecord record
      pure s!"  ({hex start}, {hex stop}, {str record[2]!.copy})"
    | .numericValue =>
      let (start, stop) := rangeOfRecord record
      pure s!"  ({hex start}, {hex stop}, {numericType record[2]!})"
    | .script =>
      let (start, stop) := rangeOfRecord record
      let code := Script.ofAbbrev! record[2]!.copy |>.code
      pure s!"  ({hex start}, {hex stop}, Script.mk {hex code})"
    | .scriptExtensions =>
      let (start, stop) := rangeOfRecord record
      let vals := String.intercalate ", " <| record[2]!.split " " |>.toList.map fun sc =>
        Script.ofAbbrev! sc.copy |>.code |> hex
      pure s!"  ({hex start}, {hex stop}, #[{vals}])"
    | .graphemeBreak =>
      let (start, stop) := rangeOfRecord record
      pure s!"  ({hex start}, {hex stop}, {graphemeBreak record[2]!})"
    | .wordBreak =>
      let (start, stop) := rangeOfRecord record
      pure s!"  ({hex start}, {hex stop}, {wordBreak record[2]!})"
    | .sentenceBreak =>
      let (start, stop) := rangeOfRecord record
      pure s!"  ({hex start}, {hex stop}, {sentenceBreak record[2]!})"
    | .lineBreak =>
      let (start, stop) := rangeOfRecord record
      pure s!"  ({hex start}, {hex stop}, {lineBreak record[2]!})"
    rows := rows.push (start, row)
  return (rows.qsort fun a b => a.1 < b.1).map Prod.snd

def header (spec : TableSpec) : String :=
  let imports := spec.imports.map (fun imp =>
    if (spec.moduleName == "Script" || spec.moduleName == "ScriptExtensions")
        && imp == "UnicodeBasicCommon.Types.Script" then
      "public import " ++ imp ++ "\npublic meta import " ++ imp
    else
      "public import " ++ imp) |>.toList
  String.intercalate "\n" <| [
    "/- This file is generated by table-generators/makeTablesForLookup. -/",
    "module",
    ""
  ] ++ imports ++ (if imports.isEmpty then [] else [""]) ++ [
    "@[expose] public section",
    "",
    "namespace Unicode.TableLookupTables." ++ spec.moduleName,
    "",
  ]

def renderPublicTable (spec : TableSpec) (chunkCount : Nat) : String :=
  let appends := List.range chunkCount |>.map fun idx => s!"  t := t ++ table{idx}"
  String.intercalate "\n" <|
    [s!"\npublic def table : {spec.type} := Id.run do", "  let mut t := #[]"] ++
    appends ++
    ["  return t"]

def chunkRows (size : Nat) (rows : Array String) : Array (Array String) := Id.run do
  let mut chunks := #[]
  let mut chunk := #[]
  for row in rows do
    chunk := chunk.push row
    if chunk.size == size then
      chunks := chunks.push chunk
      chunk := #[]
  if !chunk.isEmpty then
    chunks := chunks.push chunk
  return chunks

def renderParentModuleFromSubmodules (spec : TableSpec) (chunkCount : Nat) : String :=
  let imports := List.range chunkCount |>.map fun idx =>
    s!"public import UnicodeBasic.TableLookupTables.{spec.moduleName}.Chunk{idx}"
  let appends := List.range chunkCount |>.map fun idx =>
    s!"  t := t ++ Chunk{idx}.table"
  String.intercalate "\n" <|
    ["/- This file is generated by table-generators/makeTablesForLookup. -/", "module"] ++
    imports ++
    [
    "",
    s!"namespace Unicode.TableLookupTables.{spec.moduleName}",
    "",
    s!"public def table : {spec.type} := Id.run do", "  let mut t := #[]"] ++
    appends ++
    ["  return t", "", s!"end Unicode.TableLookupTables.{spec.moduleName}", ""]

public def functionModuleHeader (spec : TableSpec) : String :=
  let imports := spec.imports.map (fun imp =>
    if (spec.moduleName == "Script" || spec.moduleName == "ScriptExtensions")
        && imp == "UnicodeBasicCommon.Types.Script" then
      "public import " ++ imp ++ "\nmeta import " ++ imp
    else
      "public import " ++ imp) |>.toList
  String.intercalate "\n" <| [
    "/- This file is generated by table-generators/makeTablesForLookup. -/",
    "module",
    "",
  ] ++ imports ++ (if imports.isEmpty then [] else [""]) ++ [
    "@[expose] public section",
    "",
    s!"namespace Unicode.TableLookupTables.{spec.moduleName}",
    "",
    ""
  ]

public def renderAggregate : String :=
  String.intercalate "\n" <|
    ["/- This file is generated by table-generators/makeTablesForLookup. -/", "module"] ++
    (specs.toList.map fun spec => "public import UnicodeBasic.TableLookupTables." ++ spec.moduleName) ++
    [""]

end MakeTablesForLookup
