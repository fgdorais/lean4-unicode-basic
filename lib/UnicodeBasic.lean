/-
Copyright © 2023-2025 François G. Dorais. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
prelude
public import UnicodeBasicCommon.Types.BidiBracketType
public import UnicodeBasicCommon.Types.BidiClass
public import UnicodeBasicCommon.Types.Bounds
public import UnicodeBasicCommon.Types.DecompositionMapping
public import UnicodeBasicCommon.Types.EastAsianWidth
public import UnicodeBasicCommon.Types.GeneralCategory
public import UnicodeBasicCommon.Types.Hex
public import UnicodeBasicCommon.Types.LineBreak
public import UnicodeBasicCommon.Types.MaybeUnknownScript
public import UnicodeBasicCommon.Types.NumericType
public import UnicodeBasicCommon.Types.Script
public import UnicodeBasicCommon.Types.VerticalOrientation

public import UnicodeBasic.Types.GraphemeClusterBreak
public import UnicodeBasic.Types.SentenceBreak
public import UnicodeBasic.Types.WordBreak

-- backward compat
public import UnicodeBasic.Hangul
public import UnicodeBasic.CharacterDatabase
-- backward compat END

public import UnicodeBasic.Bidi
public import UnicodeBasic.Segmentation

public import UnicodeBasic.Lookup.NoncharacterCodePoint
public import UnicodeBasic.Lookup.Other
public import UnicodeBasic.Lookup.Titlecase

public import UnicodeBasic.TableLookup.Alphabetic
public import UnicodeBasic.TableLookup.BidiBrackets
public import UnicodeBasic.TableLookup.BidiClass
public import UnicodeBasic.TableLookup.BidiMirrored
public import UnicodeBasic.TableLookup.BidiMirroringGlyph
public import UnicodeBasic.TableLookup.BlockName
public import UnicodeBasic.TableLookup.CanonicalCombiningClass
public import UnicodeBasic.TableLookup.CanonicalDecompositionMapping
public import UnicodeBasic.TableLookup.CaseFolding
public import UnicodeBasic.TableLookup.CaseMapping
public import UnicodeBasic.TableLookup.Cased
public import UnicodeBasic.TableLookup.Dash
public import UnicodeBasic.TableLookup.DecompositionMapping
public import UnicodeBasic.TableLookup.DefaultIgnorableCodePoint
public import UnicodeBasic.TableLookup.Diacritic
public import UnicodeBasic.TableLookup.EastAsianWidth
public import UnicodeBasic.TableLookup.Emoji
public import UnicodeBasic.TableLookup.EmojiComponent
public import UnicodeBasic.TableLookup.EmojiModifier
public import UnicodeBasic.TableLookup.EmojiModifierBase
public import UnicodeBasic.TableLookup.EmojiPresentation
public import UnicodeBasic.TableLookup.ExtendedPictographic
public import UnicodeBasic.TableLookup.Extender
public import UnicodeBasic.TableLookup.GeneralCategory
public import UnicodeBasic.TableLookup.GraphemeBase
public import UnicodeBasic.TableLookup.GraphemeBreak
public import UnicodeBasic.TableLookup.GraphemeExtend
public import UnicodeBasic.TableLookup.Hyphen
public import UnicodeBasic.TableLookup.IdContinue
public import UnicodeBasic.TableLookup.IdStart
public import UnicodeBasic.TableLookup.LineBreak
public import UnicodeBasic.TableLookup.Lowercase
public import UnicodeBasic.TableLookup.Math
public import UnicodeBasic.TableLookup.Name
public import UnicodeBasic.TableLookup.NumericValue
public import UnicodeBasic.TableLookup.OtherAlphabetic
public import UnicodeBasic.TableLookup.OtherLowercase
public import UnicodeBasic.TableLookup.OtherMath
public import UnicodeBasic.TableLookup.OtherUppercase
public import UnicodeBasic.TableLookup.PatternSyntax
public import UnicodeBasic.TableLookup.PatternWhiteSpace
public import UnicodeBasic.TableLookup.QuotationMark
public import UnicodeBasic.TableLookup.RegionalIndicator
public import UnicodeBasic.TableLookup.Script
public import UnicodeBasic.TableLookup.ScriptExtensions
public import UnicodeBasic.TableLookup.SentenceBreak
public import UnicodeBasic.TableLookup.SentenceTerminal
public import UnicodeBasic.TableLookup.SimpleCaseFolding
public import UnicodeBasic.TableLookup.TerminalPunctuation
public import UnicodeBasic.TableLookup.Uppercase
public import UnicodeBasic.TableLookup.VerticalOrientation
public import UnicodeBasic.TableLookup.WhiteSpace
public import UnicodeBasic.TableLookup.WordBreak
public import UnicodeBasic.TableLookup.XidContinue
public import UnicodeBasic.TableLookup.XidStart

public import UnicodeBasic.GeneralApi.Core
public import UnicodeBasic.GeneralApi.Script
public import UnicodeBasic.GeneralApi.ScriptPredicates
public import UnicodeBasic.GeneralApi.Bidi
public import UnicodeBasic.GeneralApi.GeneralCategory
public import UnicodeBasic.GeneralApi.Case
public import UnicodeBasic.GeneralApi.Decomposition
public import UnicodeBasic.GeneralApi.Numeric
public import UnicodeBasic.GeneralApi.BinaryProperties
public import UnicodeBasic.GeneralApi.Emoji
public import UnicodeBasic.GeneralApi.DerivedProperties


/-!
  # General API #

  As a general rule, for a given a Unicode property called `Unicode_Property`,
  for example:

  - If the property is boolean valued then the implementation is called
    `Unicode.isUnicodeProperty`.

  - Otherwise, the implementation is called `Unicode.getUnicodeProperty`.

  - If the value is not of standard type (`Bool`, `Char`, `Nat`, `Int`, etc.)
    or a combination thereof (e.g. `Bool × Option Nat`) then the value type is
    defined in `UnicodeBasic.Types`.

  - If the input type needs disambiguation (e.g. `Char` vs `String`) the type
    name may be appended to the name as in `Unicode.isUnicodePropertyChar` or
    in `Unicode.getUnicodePropertyString`.

  - If the output type is `Option _` then the suffix `?` may be appended to
    indicate that this is a partial function. In this case, a companion
    function with the suffix `!` may be implemented. This function will
    perform the same calculation as the original but it assumes the user has
    checked that the input is in the domain, the function may panic if this
    is not the case.

  Unicode general categories are encoded using the type `GC`. This type has
  a boolean algebra structure with inclusion `⊆`, meet/intersection `&&&`,
  join/union `|||` and complement `~~~`. The relation `∈` is provided to
  check whether a character belongs to a given category. For example,
  `c ∈ (GC.L &&& ~~~GC.Lt) ||| GC.Z` checks whether `c` is a either a
  non-titlecase letter or a separator.
-/
