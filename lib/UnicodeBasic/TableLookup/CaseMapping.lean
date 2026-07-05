/-
Copyright © 2024-2025 François G. Dorais. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import UnicodeBasic.TableLookupCommon
public import UnicodeBasic.TableLookupTables.CaseMapping

namespace Unicode

/-- Get simple case mappings of a code point using lookup table

  Unicode properties:
    `Simple_Lowercase_Mapping`
    `Simple_Uppercase_Mapping`
    `Simple_Titlecase_Mapping` -/
public def lookupCaseMapping (c : UInt32) : UInt32 × UInt32 × UInt32 :=
  if h : TableLookupTables.CaseMapping.BetweenOrEqStartEnd c then
    (TableLookupTables.CaseMapping.getInsideSparseRangeValueTable c h).getD (c, c, c)
  else
    (c, c, c)
