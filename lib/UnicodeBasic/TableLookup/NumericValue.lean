/-
Copyright © 2024-2025 François G. Dorais. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import UnicodeBasicCommon.Types.NumericType
public import UnicodeBasic.TableLookupCommon
public import UnicodeBasic.TableLookupTables.NumericValue

namespace Unicode

/-- Get numeric value of a code point using lookup table.

  Keep this definition in sync with the generated
  `UnicodeBasic.TableLookupTables.NumericValue` module.

  Unicode properties:
    `Numeric_Type`
    `Numeric_Value` -/
public def lookupNumericValue (c : UInt32) : Option NumericType :=
  if h : TableLookupTables.NumericValue.BetweenOrEqStartEnd c then
    TableLookupTables.NumericValue.getInsideSparseRangeValueTable c h
  else
    none
