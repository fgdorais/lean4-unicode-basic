/-
Copyright © 2024-2025 François G. Dorais. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import UnicodeBasic.TableLookupCommon
public import UnicodeBasic.TableLookupTables.QuotationMark

namespace Unicode

/-- Check if code point has Quotation_Mark property using lookup table -/
public abbrev lookupQuotationMark (c : UInt32) : Prop :=
  if h : Unicode.TableLookupTables.QuotationMark.BetweenOrEqStartEnd c then
    Unicode.TableLookupTables.QuotationMark.IsInsideSparseRangeTable c h
  else
    False
