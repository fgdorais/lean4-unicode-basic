# Assumptions

The repo currently targets Unicode 17.0.0 in `scripts/download_unicode_data.ts` and checked-in `data/ucd/*` files. I’ll treat “UCD 7.0” as “full support for the current UCD set” unless you explicitly mean Unicode 7.0.0.

There is also an uncommitted change already present:
`UnicodeData/EastAsianWidth.lean` now uses `DerivedEastAsianWidth.txt`.
I would commit that first after one final `lake build UnicodeBasic UnicodeData && lake exe testTables`.

# Overall Strategy

Finish in layers:

1. Make every semantically useful UCD file represented by a `UnicodeData.*` parser module.
2. Prefer existing public APIs and table generation paths when a file backs an existing property.
3. Add `UnicodeBasic` wrappers only for stable, user-facing properties.
4. Add raw parser modules for obscure source/reference files so the repo truthfully “uses” them without pretending every file deserves a high-level API.
5. Use conformance files as tests, not as library data.
6. Automate the repetitive parser modules.

# Recommended Port Order

| Order | Files | Ease | Why now | Main Problems | Solution |
| :--- | :--- | :--- | :--- | :--- | :--- |
| 0 | `DerivedEastAsianWidth.txt` | done/easy | Already mostly done | Derived file order differs from binary search assumptions | Sort parsed ranges before lookup |
| 1 | `DerivedBidiClass.txt` | medium | Replaces `UnicodeData.txt`-derived Bidi_Class table with authoritative extracted file | `@missing` defaults matter for unassigned RTL ranges | Add raw-line parser for `@missing`, explicit ranges override defaults |
| 2 | `DerivedGeneralCategory.txt` | medium | Existing GC lookup is core; extracted file is authoritative | Existing compression has special bit packing for paired categories | Parse derived GC, then preserve current compression encoding |
| 3 | `DerivedCombiningClass.txt` | easy | Existing canonical combining class table maps directly to numeric property values, default 0 | Numeric property values, default 0 | Generic range data parser with numeric values |
| 4 | `DerivedLineBreak.txt` | medium | Existing line break lookup already exists | Derived file order and missing defaults | Same generic range parser plus defaults |
| 5 | `DerivedNumericType.txt`, `DerivedNumericValues.txt` | medium | Existing numeric lookup currently depends on `UnicodeData.txt` only | Need merge of type and value files; fractional values | New numeric module that joins by code range and preserves `NumericType` representation |
| 6 | `DerivedDecompositionType.txt` | medium | Complements decomposition mapping and normalization work | Must reconcile with tags in `UnicodeData.txt` | Parse as independent lookup first, then use to validate/generate table |
| 7 | `DerivedBinaryProperties.txt` | easy | Small, pure binary property ranges | It duplicates some existing `PropList`/`UnicodeData`-derived data | Add module and either validate existing `Bidi_Mirrored` or expose lookup |
| 8 | `DerivedAge.txt` | easy | Simple property value per range | Need `Age` type | Generate enum/value type from values in file |
| 9 | `HangulSyllableType.txt`, `Jamo.txt` | easy | Clean Korean/Hangul properties | Existing Hangul logic may cover some behavior but not these properties | Add data modules and optional `getHangulSyllableType`, `getJamoShortName`? |
| 10 | `ArabicShaping.txt`, `DerivedJoiningType.txt`, `DerivedJoiningGroup.txt` | medium | They naturally belong together | Multiple related value domains; joining group names need normalization | Generate `JoiningType`, `JoiningGroup`, and shaping record parser |
| 10 | `ArabicShaping.txt`, `DerivedJoiningType.txt`, `DerivedJoiningGroup.txt` | medium | They naturally belong together | Multiple related value domains; joining group names need normalization | Generate `JoiningType`, `JoiningGroup`, and shaping record parser |
| 11 | `IndicPositionalCategory.txt`, `IndicSyllabicCategory.txt` | medium | Straight enum range properties | Many enum values | Generate enum inductives from data values |
| 12 | `CompositionExclusions.txt`, `DerivedNormalizationProps.txt`, `NormalizationCorrections.txt` | hard | Real normalization support depends on these | Normalization is algorithmic, not just lookup tables | First parse and expose raw properties; later implement normalization with conformance tests |
| 13 | `NameAliases.txt`, `NamedSequences.txt`, `NamedSequencesProv.txt` | medium | Useful name lookup extensions | Name lookup currently returns basic names only | Add lookup tables and decide API names carefully |
| 14 | `SpecialCasing.txt`, `CaseFolding.txt` already partially used | hard | Full casing needs conditions/locales | Context-sensitive rules are not simple lookups | Parse full records first; expose unconditional mappings first; defer conditional API |
| 15 | `StandardizedVariants.txt`, `emoji-variation-sequences.txt` | medium | Similar variant sequence data | Sequence keys, standardized descriptions | Generic sequence parser keyed by `Array UInt32` |
| 16 | `CJKRadicals.txt`, `EquivalentUnifiedIdeograph.txt` | medium | Small structured CJK metadata | Specialized API choices | Raw module first, wrappers later |
| 17 | `EmojiSources.txt` | medium | Legacy emoji source mappings | Low practical value | Raw module only unless a clear wrapper emerges |
| 18 | `TangutSources.txt`, `NushuSources.txt`, `Unikemet.txt`, `USourceData.txt` | hard/low priority | Large specialized source metadata | Heterogeneous schemas | Generate raw structured records, skip high-level API initially |
| 19 | Unihan files | hard | Huge, tab-separated, many fields | Scale, memory, schema diversity | Generate per-file modules with field-indexed records; maybe do not import by default |
| 20 | `GraphemeBreakTest.txt`, `WordBreakTest.txt`, `SentenceBreakTest.txt`, `LineBreakTest.txt` | medium-hard | They are conformance tests | Need segmenter algorithms to make them meaningful | Add as test fixtures when segment algorithms exist |
| 21 | `BidiCharacterTest.txt`, `BidiTest.txt` | hard | Requires bidi algorithm support | Full UAX #9 implementation | Keep as future conformance gate after bidi algorithm work |
| 22 | `NormalizationTest.txt` | hard | Requires normalization implementation | Full NFC/NFD/NFKC/NFKD pipeline | Use after normalization properties are parsed |

**Automation Plan**
Yes, a lot of this should be automated.

I would add scripts under `scripts/ucd_codegen/` or similar:

1. `analyze_ucd_file.ts`
Reads a UCD txt file and reports schema:
`range ; value`, `code ; value`, `code ; code ; type`, tab-separated Unihan, sequence fields, `@missing` directives.

2. `generate_range_module.ts`
Generates Lean modules like:
`UnicodeData.DerivedBidiClass`
`UnicodeData.DerivedCombiningClass`
`UnicodeData.DerivedLineBreak`

Common output:
```lean
def X.txt := include_str "../data/ucd/..."
public def X.data : Array (UInt32 × UInt32 × ValueType) := ...
public def lookupX? ...
public def lookupX ...
```

3. `generate_enum_type.ts`
For files with many property values:
`Age`, `JoiningType`, `JoiningGroup`, `IndicSyllabicCategory`, `IndicPositionalCategory`, `HangulSyllableType`.

It should generate:
`toAbbrev`, `ofAbbrev?`, `ofAbbrev!`, `ToString`, `Repr`.

4. `generate_provenance.ts` improvements
Current provenance script misses source use through newer parser modules unless regexes are updated. It should understand `UnicodeData.X.data` and map it back to the underlying `include_str`.

5. `generate_smoke_tests.ts`
For every generated lookup module:
sample first, middle, last range records and assert lookup returns expected value.
Also test one default/missing value when applicable.

**Generic Parser Pieces To Add In Lean**
The repo needs a small shared parser layer before doing many more files:

- `parseCodeOrRange : String.Slice -> UInt32 × UInt32`
- `parseRangeValueTable`
- `parseBinaryPropertyTable`
- `parseMissingDirectives` from raw lines, because `UCDStream` strips comments and `@missing` lives in comments
- `sortAndCompressData`
- `lookupRange?` / `lookupRangeWithDefault`

This avoids copying the East Asian width pattern twenty times.

**Foreseen Problems**
The biggest problem is `@missing`. Several derived files encode defaults in comments, and current `UCDStream` intentionally strips comments. Solution: keep `UCDStream` for ordinary records, but add a separate raw-line scanner for `# @missing:`.

The second problem is public API sprawl. Not every UCD source deserves a top-level `UnicodeBasic` function. Solution: separate `UnicodeData.*` raw/structured support from `UnicodeBasic` convenience APIs.

The third problem is generated Lean compile cost. Some files are huge, especially `DerivedName.txt` and Unihan. Solution: keep large modules out of root imports unless needed, use generated compressed tables, and benchmark `lake build`.

The fourth problem is conformance files. They should not be counted as “library data” in the same way as property files. Solution: move them into test harnesses and update the usage report to distinguish `used by library` from `used by tests`.

**Commit Plan**
Use small commits by tier:

1. Commit current `DerivedEastAsianWidth` change.
2. Commit shared parser helpers and report script improvements.
3. Commit extracted core property ports in small batches.
4. Commit enum-property generated modules.
5. Commit normalization/casing data parsers.
6. Commit source/metadata raw modules.
7. Commit conformance fixture harnesses.

Each commit should pass:
`lake build UnicodeData UnicodeBasic testTables`
and when tables change:
`lake exe makeTablesForLookup`
`lake exe testTables`
`just ucd-usage-status`
`just table-provenance`
