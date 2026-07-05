# Pure Lean UAX #9 Bidi Engine

## Summary

Replace the vendored Unicode BidiReferenceC bridge with a pure Lean implementation of UAX #9. The native bidi files, downloader, extern bindings, context/init API, and string-parsing bridge are removed. The public API becomes deterministic pure Lean functions over code points or bidi classes, validated against `BidiCharacterTest.txt` and `BidiTest.txt`.

Chosen API direction: break API cleanly.

## Public API Changes

- Keep:
  - `Unicode.BidiParagraphDirection`
  - `Unicode.BidiResolution`
  - `Unicode.resolveBidiText`
  - `Unicode.resolveBidiClasses`

- Change signatures:
  ```lean
  public def resolveBidiText
      (text : Array UInt32)
      (paragraphDirection : BidiParagraphDirection) :
      BidiResolution

  public def resolveBidiClasses
      (classes : Array BidiClass)
      (paragraphDirection : BidiParagraphDirection) :
      BidiResolution
  ```

- Removed the old context/init bridge API and all bidi-specific extern declarations.

## Implementation Changes

- Rework `UnicodeBasic.Bidi` as a pure Lean UAX #9 engine.
- Internal representation should track each original input item with:
  - original index
  - optional code point
  - original bidi class
  - mutable/resolved bidi class
  - embedding level, using `Option Nat` so ignored/deleted entries become `none`
  - isolate/format status needed by X rules and L1
- Implement UAX #9 rule groups in order:
  - P1-P3 paragraph embedding level resolution
  - X1-X10 explicit embeddings, overrides, isolates, overflow handling, and isolating run sequence setup
  - W1-W7 weak type resolution
  - N0 paired bracket resolution using existing `lookupBidiPairedBracket?` and `lookupBidiPairedBracketType?`
  - N1-N2 neutral resolution
  - I1-I2 implicit level resolution
  - L1 whitespace/separator reset
  - L2 visual order generation
- Use UAX max explicit depth/level limit `125`.
- For `resolveBidiClasses`, do not run bracket-pair matching from code point data because class-only input has no bracket code points. It should still run the rest of the UAX #9 class-based behavior.
- For `resolveBidiText`, derive classes through existing `lookupBidiClass` and bracket data through existing Unicode data helpers.

## Native Dependency Removal

- The bidi-specific native bridge, vendored reference sources, downloader, and
  downloader recipe have been removed.
- `UnicodeCLib` has been removed; lookup tables are generated as Lean modules.
- Documentation and comments should describe the pure Lean resolver.

## Test Plan

- Update `UnicodeDataTest.Conformance.Bidi` to call pure functions directly with no context/init.
- `lake exe testConformance` must pass:
  - `BidiCharacterTest.txt`
  - `BidiTest.txt`
  - existing normalization and break tests
- Add focused regression tests or small conformance cases for:
  - empty input
  - simple LTR and RTL text
  - automatic paragraph direction with no strong character
  - explicit embedding and override controls
  - isolate controls
  - weak number resolution
  - neutral resolution
  - bracket-pair resolution
  - trailing whitespace reset
  - visual reordering for mixed L/R runs
- Run:
  - `lake build UnicodeBasic UnicodeData`
  - `lake exe testConformance`
  - `lake exe testTables`

## Assumptions

- Target the Unicode data version already checked into `data/ucd`, currently managed by `scripts/download_unicode_data.ts`.
- The pure Lean implementation should match the conformance fixtures, not preserve quirks of the C reference bridge.
- No compatibility shim is required for the previous context/init API.

Reimplement everything in Lean. Most of the ingredients already exist in the repo:

- bidi class lookup
- bidi control / mirrored / bracket helpers
- property tables and character data
- test fixtures and conformance harnesses

Write actual UAX #9 engine:

- paragraph direction resolution
- explicit embedding / isolate processing
- weak type resolution
- neutral resolution
- paired bracket resolution
- implicit level resolution
- reordering / visual order generation
