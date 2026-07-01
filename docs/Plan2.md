Plan:

1. Classify UCD txt files by role
Identify property/source files versus conformance/test files versus intentionally skipped prose files. Keep `DoNotEmit.txt` and `NamesList.txt` in the skipped/prose bucket.

2. Update `scripts/ucd_txt_usage.ts`
Add a third usage class for conformance fixtures, separate from `used` and `unused`. The report should show these files as `test fixture pending` or similar, not simply `unused`.

3. Add parser support for break test fixtures
Create a small parser for the UAX break test format:
`÷ 0061 × 0308 ÷ 0062 ÷ # comment`
It should return:
- code point sequence
- expected boundary indexes
- source line number
- optional comment

4. Start with one harness
Implement `GraphemeBreakTest.txt` first because grapheme segmentation is the most natural first conformance target. Wire it as a Lean executable or test helper depending on the repo’s current test pattern.

5. Decide expected failure policy
If the algorithm is incomplete or missing, don’t wire a failing full conformance test into the default test target yet. Add either:
- parser smoke tests only, or
- an opt-in executable like `lake exe testGraphemeBreak`, or
- a skipped/pending report entry.

6. Extend to other break tests
After the first harness pattern is proven, add:
- `WordBreakTest.txt`
- `SentenceBreakTest.txt`
- `LineBreakTest.txt`

Each should reuse the same fixture parser where possible.

7. Finish bidi and normalization conformance
The public API exposes bidi property helpers in `UnicodeBasic` (`getBidiClass`, `isBidiControl`, bracket and mirroring lookups). The bidi conformance harness now runs `BidiCharacterTest.txt` and `BidiTest.txt` through the Unicode reference implementation, and normalization conformance is covered by the existing Lean runner.

8. Regenerate reports and verify
Run:
- `node scripts/ucd_txt_usage.ts`
- `lake build UnicodeData UnicodeBasic`
- existing test executables
- any new fixture parser tests

End state:
- usage report no longer calls conformance files simply `unused`
- break test files have a reusable parser and at least one harness path
- bidi/normalization files are covered by conformance tests instead of being left as pending fixtures.


**Expanded Plan**
Use conformance files as executable specifications for algorithms, not as imported `UnicodeData.*` library tables. Each test file gives input sequences plus expected algorithm output. The harness should parse the file, run the corresponding implementation, and compare against expected results with line-numbered failures.

**Common Fixture Layer**
Add a shared test parser, likely under `Test/UnicodeConformance.lean` or `UnicodeData/ConformanceTest.lean` if the repo prefers library-visible helpers.

Tentative Lean shape:

```lean
structure BreakTestCase where
  line : Nat
  codepoints : Array UInt32
  boundaries : Array Nat
  comment : String
deriving Repr, Inhabited

def parseBreakTestLine? (lineNo : Nat) (line : String) : Option BreakTestCase := ...
def parseBreakTestFile (txt : String) : Array BreakTestCase := ...
```

For a line like:

```text
÷ 0061 × 0308 ÷ 0062 ÷ # ...
```

parse to:

```lean
{
  codepoints := #[0x0061, 0x0308, 0x0062],
  boundaries := #[0, 2, 3],
  line := lineNo,
  comment := ...
}
```

Meaning:
- `÷` means a boundary before the next code point.
- `×` means no boundary.
- boundary indexes are positions between code points.
- index `0` is before the first code point.
- index `codepoints.size` is after the last code point.

The generic runner:

```lean
structure ConformanceFailure where
  file : String
  line : Nat
  input : Array UInt32
  expected : Array Nat
  actual : Array Nat
  comment : String
deriving Repr

def runBreakConformance
    (file : String)
    (cases : Array BreakTestCase)
    (segment : Array UInt32 -> Array Nat) :
    Array ConformanceFailure :=
  cases.filterMap fun tc =>
    let actual := segment tc.codepoints
    if actual == tc.boundaries then
      none
    else
      some {
        file := file
        line := tc.line
        input := tc.codepoints
        expected := tc.boundaries
        actual := actual
        comment := tc.comment
      }
```

**GraphemeBreakTest.txt**
Used to test extended grapheme cluster boundaries.

Tentative usage:

```lean
def graphemeBoundaries (xs : Array UInt32) : Array Nat :=
  Unicode.segmentGraphemeClusters xs

def testGraphemeBreak : IO UInt32 := do
  let txt := include_str "../data/ucd/auxiliary/GraphemeBreakTest.txt"
  let cases := parseBreakTestFile txt
  let failures := runBreakConformance "GraphemeBreakTest.txt" cases graphemeBoundaries
  reportFailures failures
```

What this validates:
- CR/LF/control handling
- combining marks
- Hangul syllable sequences
- emoji modifier sequences
- ZWJ emoji sequences
- regional indicators
- extended pictographic cases

This should become a default test once `segmentGraphemeClusters` is implemented.

**WordBreakTest.txt**
Used to test Unicode word boundary detection.

Tentative usage:

```lean
def wordBoundaries (xs : Array UInt32) : Array Nat :=
  Unicode.segmentWords xs

def testWordBreak : IO UInt32 := do
  let txt := include_str "../data/ucd/auxiliary/WordBreakTest.txt"
  let cases := parseBreakTestFile txt
  let failures := runBreakConformance "WordBreakTest.txt" cases wordBoundaries
  reportFailures failures
```

What this validates:
- ALetter and Numeric rules
- Hebrew letter rules
- apostrophes and mid-letter punctuation
- Katakana sequences
- Extend/Format/ZWJ ignoring behavior
- regional indicator pairs
- emoji ZWJ behavior

This depends on a real word segmentation implementation.

**SentenceBreakTest.txt**
Used to test sentence boundary detection.

Tentative usage:

```lean
def sentenceBoundaries (xs : Array UInt32) : Array Nat :=
  Unicode.segmentSentences xs

def testSentenceBreak : IO UInt32 := do
  let txt := include_str "../data/ucd/auxiliary/SentenceBreakTest.txt"
  let cases := parseBreakTestFile txt
  let failures := runBreakConformance "SentenceBreakTest.txt" cases sentenceBoundaries
  reportFailures failures
```

What this validates:
- abbreviations and periods
- Close/Sp/Format handling
- lowercase-after-period suppression
- paragraph and separator behavior
- numeric punctuation cases

This should remain pending until sentence segmentation exists.

**LineBreakTest.txt**
Used to test line break opportunities.

Tentative usage:

```lean
def lineBreakOpportunities (xs : Array UInt32) : Array Nat :=
  Unicode.lineBreakOpportunities xs

def testLineBreak : IO UInt32 := do
  let txt := include_str "../data/ucd/auxiliary/LineBreakTest.txt"
  let cases := parseBreakTestFile txt
  let failures := runBreakConformance "LineBreakTest.txt" cases lineBreakOpportunities
  reportFailures failures
```

What this validates:
- mandatory breaks
- combining marks
- spaces and break-after behavior
- East Asian classes
- emoji line-break rules
- pair-table behavior from UAX #14

This depends on a UAX #14 implementation, not just the current line-break property lookup.

**NormalizationTest.txt**
Different format. It does not use `÷` and `×`; it provides columns for canonical and compatibility normalization.

Typical shape:

```text
source; NFC; NFD; NFKC; NFKD; # comment
```

Parser shape:

```lean
structure NormalizationTestCase where
  line : Nat
  source : Array UInt32
  nfc : Array UInt32
  nfd : Array UInt32
  nfkc : Array UInt32
  nfkd : Array UInt32
  comment : String
deriving Repr, Inhabited
```

Tentative runner:

```lean
def runNormalizationConformance
    (cases : Array NormalizationTestCase) :
    Array ConformanceFailure := ...
```

Checks per row:

```lean
Unicode.normalizeNFC source == nfc
Unicode.normalizeNFD source == nfd
Unicode.normalizeNFKC source == nfkc
Unicode.normalizeNFKD source == nfkd
Unicode.normalizeNFC nfc == nfc
Unicode.normalizeNFD nfd == nfd
Unicode.normalizeNFKC nfkc == nfkc
Unicode.normalizeNFKD nfkd == nfkd
```

What this validates:
- canonical decomposition
- canonical ordering by combining class
- canonical composition exclusions
- compatibility decomposition
- idempotence of all normalization forms

Normalization conformance is now wired through the Lean runner.

**BidiCharacterTest.txt**
This tests UAX #9 bidi resolution for specific character sequences.

Likely parser shape:

```lean
structure BidiCharacterTestCase where
  line : Nat
  input : Array UInt32
  paragraphDirection : BidiParagraphDirection
  resolvedLevels : Array (Option Nat)
  visualOrder : Array Nat
  comment : String
deriving Repr, Inhabited
```

Tentative runner:

```lean
def testBidiCharacter : IO UInt32 := do
  let txt := include_str "../data/ucd/conformance/BidiCharacterTest.txt"
  let cases := parseBidiCharacterTests txt
  let failures := cases.filterMap fun tc =>
    let result := Unicode.resolveBidi tc.paragraphDirection tc.input
    if result.levels == tc.resolvedLevels && result.visualOrder == tc.visualOrder then
      none
    else
      some ...
  reportFailures failures
```

What this validates:
- explicit embeddings and isolates
- weak type resolution
- neutral resolution
- bracket pair handling
- implicit level resolution
- visual reordering

This is now wired through the public `UnicodeBasic.Bidi` API and the Unicode reference implementation.

**BidiTest.txt**
This is broader and more synthetic than `BidiCharacterTest.txt`. It tests bidi classes directly rather than actual characters.

Parser shape:

```lean
structure BidiClassTestCase where
  line : Nat
  classes : Array BidiClass
  paragraphLevels : Array Nat
  expectedLevels : Array (Option Nat)
  expectedOrder : Array Nat
  comment : String
deriving Repr, Inhabited
```

Tentative usage:

```lean
def testBidiClasses : IO UInt32 := do
  let txt := include_str "../data/ucd/conformance/BidiTest.txt"
  let cases := parseBidiClassTests txt
  let failures := cases.filterMap fun tc =>
    let result := Unicode.resolveBidiClasses tc.paragraphLevel tc.classes
    if result.levels == tc.expectedLevels && result.visualOrder == tc.expectedOrder then
      none
    else
      some ...
  reportFailures failures
```

What this validates:
- algorithm behavior independent of character table lookup
- full class-level rule coverage
- paragraph direction variants

This remains useful for debugging because it isolates algorithm logic from code point properties, but it is now a public library feature rather than a test-only hook.

**Usage Report Update**
`ucd_txt_usage.ts` should distinguish these states:

```text
used by library
used by tests
skipped non-machine-readable
unused
```

Initial report classification:

```text
GraphemeBreakTest.txt      used by tests
WordBreakTest.txt          used by tests
SentenceBreakTest.txt      used by tests
LineBreakTest.txt          used by tests
BidiCharacterTest.txt      used by tests
BidiTest.txt               used by tests
NormalizationTest.txt      used by tests
```

After a parser harness exists but no algorithm exists:

```text
used by tests
```

After the algorithm exists and the test is wired into default tests:

```text
used by tests
```

**Implementation Order**
1. Update `ucd_txt_usage.ts` classification first so these files stop appearing as plain `unused`.
2. Add shared break-test parser and smoke tests.
3. Add `testGraphemeBreak` as the first real conformance executable when grapheme segmentation exists.
4. Wire bidi conformance through the reference implementation and keep normalization covered by the Lean runner.
