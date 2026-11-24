/- THIS IS A GENERATED FILE - DO NOT EDIT -/
module
public import UnicodeBasic.Internal.BTree

/-! # Kernel copy of the `default_ignorable` table

This module holds the same table as `UnicodeCLib/default_ignorable.c` as a B-tree, for the kernel
to read. It is internal and may change at any time.
-/

namespace Unicode.Internal

-- The block of each leaf holds the `default_ignorable.c` data of its ranges, 1 bit each.
--
-- This must stay `noncomputable`: compiled code uses the C table, and a computable definition
-- would build this tree when a program starts.
/-- The `default_ignorable` table (internal use only) -/
@[expose] public noncomputable def defaultIgnorableTree : BTree Nat :=
  .leaf 0 17
    (nat_lit 0x1C1FFEE00000E8BD0745CC379461BCA007FFC03FFC01FF400FFA007F7F83FBFC1FC1E0FE00018B200C590040DE02060010170080A80401E0200B00C0780602C02F6A017B4008B000457C00C380061C001A7800D3C0015A000AD)
    (nat_lit 0x1FFFF)
