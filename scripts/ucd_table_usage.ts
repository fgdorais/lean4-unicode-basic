#!/usr/bin/env node

import * as path from 'node:path';
import { repoRoot, relPosix, readText, walkFiles, writeText } from './lib/ucd_report_lib.ts';

type DirectUsage = {
  file: string;
  lookup: string;
};

type BackendUsage = {
  lookup: string;
  backend: string;
  note: string;
};

function extractDefBodies(src: string): Map<string, string> {
  const out = new Map<string, string>();
  const lines = src.split(/\r?\n/);
  let currentName: string | null = null;
  let bodyLines: string[] = [];

  const flush = () => {
    if (!currentName) return;
    out.set(currentName, bodyLines.join('\n'));
  };

  for (const line of lines) {
    const match = line.match(/^(?:@[^\n]+\s*)*(?:public\s+|private\s+)?(?:partial\s+)?def\s+([A-Za-z0-9_?]+)\b/);
    if (match) {
      flush();
      currentName = match[1];
      bodyLines = [line];
      continue;
    }
    if (currentName) {
      bodyLines.push(line);
    }
  }
  flush();
  return out;
}

const tableLookupSrc = readText(path.join(repoRoot, 'UnicodeBasic', 'TableLookup.lean'));
const defBodies = extractDefBodies(tableLookupSrc);

const directUsages: DirectUsage[] = [];
for (const [name, body] of defBodies.entries()) {
  for (const match of body.matchAll(/include_str\s+"\.\.\/data\/table\/([^"]+)"/g)) {
    directUsages.push({
      file: `data/table/${match[1]}`,
      lookup: name
    });
  }
}
directUsages.sort((a, b) => a.file.localeCompare(b.file));

const directFiles = new Set(directUsages.map((r) => r.file));
const allTableFiles = walkFiles(path.join(repoRoot, 'data', 'table'), (p) => p.endsWith('.txt'))
  .map((absolutePath) => relPosix(absolutePath))
  .sort();
const unusedTables = allTableFiles.filter((file) => !directFiles.has(file));

const ffiBackedLookups: BackendUsage[] = [
  {
    lookup: 'lookupAlphabetic',
    backend: 'UnicodeCLib.lookupProp',
    note: 'Uses the bitset produced by `UnicodeCLib/prop.c`; the generated `data/table/Alphabetic.txt` file is not read directly by Lean.'
  },
  {
    lookup: 'lookupCaseMapping',
    backend: 'UnicodeCLib.lookupCase',
    note: 'Uses the packed case-mapping table produced by `UnicodeCLib/case.c`; the generated `data/table/Case_Mapping.txt` file is not read directly by Lean.'
  },
  {
    lookup: 'lookupCased',
    backend: 'UnicodeCLib.lookupProp',
    note: 'Uses the bitset produced by `UnicodeCLib/prop.c`; the generated `data/table/Cased.txt` file is not read directly by Lean.'
  },
  {
    lookup: 'lookupLowercase',
    backend: 'UnicodeCLib.lookupProp',
    note: 'Uses the bitset produced by `UnicodeCLib/prop.c`; the generated `data/table/Lowercase.txt` file is not read directly by Lean.'
  },
  {
    lookup: 'lookupMath',
    backend: 'UnicodeCLib.lookupProp',
    note: 'Uses the bitset produced by `UnicodeCLib/prop.c`; the generated `data/table/Math.txt` file is not read directly by Lean.'
  },
  {
    lookup: 'lookupOther',
    backend: 'UnicodeCLib.lookupProp',
    note: 'Extracts the auxiliary property bits from `UnicodeCLib/prop.c`; the generated `data/table/Other*.txt` files are not read directly by Lean.'
  },
  {
    lookup: 'lookupScript',
    backend: 'UnicodeCLib.lookupScript',
    note: 'Uses the script table produced by `UnicodeCLib/script.c`; no `data/table` file is read for this lookup.'
  },
  {
    lookup: 'lookupUppercase',
    backend: 'UnicodeCLib.lookupProp',
    note: 'Uses the bitset produced by `UnicodeCLib/prop.c`; the generated `data/table/Uppercase.txt` file is not read directly by Lean.'
  }
];

const unicodeDataBackedLookups: BackendUsage[] = [
  {
    lookup: 'lookupBidiClass',
    backend: 'UnicodeData.Extracted.DerivedBidiClass',
    note: 'The lookup is implemented from `UnicodeData.Extracted.DerivedBidiClass`; the generated `data/table/Bidi_Class.txt` file is not read directly by Lean.'
  },
  {
    lookup: 'lookupBidiMirrored',
    backend: 'UnicodeData.Extracted.DerivedBinaryProperties',
    note: 'The lookup is implemented from `UnicodeData.Extracted.DerivedBinaryProperties`; the generated `data/table/Bidi_Mirrored.txt` file is not read directly by Lean.'
  },
  {
    lookup: 'lookupCanonicalCombiningClass',
    backend: 'UnicodeData.Extracted.DerivedCombiningClass',
    note: 'The lookup is implemented from `UnicodeData.Extracted.DerivedCombiningClass`; the generated `data/table/Canonical_Combining_Class.txt` file is not read directly by Lean.'
  },
  {
    lookup: 'lookupGC',
    backend: 'UnicodeData.Extracted.DerivedGeneralCategory',
    note: 'The lookup is implemented from `UnicodeData.Extracted.DerivedGeneralCategory`; the generated `data/table/General_Category.txt` file is not read directly by Lean.'
  },
  {
    lookup: 'lookupLineBreak',
    backend: 'UnicodeData.Extracted.DerivedLineBreak',
    note: 'The lookup is implemented from `UnicodeData.Extracted.DerivedLineBreak`; the generated `data/table/Line_Break.txt` file is not read directly by Lean.'
  },
  {
    lookup: 'lookupNumericValue',
    backend: 'UnicodeData.Basic + UnicodeData.Extracted.DerivedNumericValues',
    note: 'The lookup is assembled from `UnicodeData.Basic` and `UnicodeData.Extracted.DerivedNumericValues`; the generated `data/table/Numeric_Value.txt` file is not read directly by Lean.'
  },
  {
    lookup: 'lookupTitlecase',
    backend: 'UnicodeBasic.TableLookup.lookupGC',
    note: 'This lookup is derived from `lookupGC`; the generated `data/table/Titlecase.txt` file is not read directly by Lean.'
  }
];

const unusedNotes: Record<string, string> = {
  'Alphabetic.txt': 'Equivalent lookup is provided by `UnicodeCLib.lookupProp` via `lookupAlphabetic`.',
  'Bidi_Class.txt': 'Equivalent lookup is provided by `UnicodeData.Extracted.DerivedBidiClass` via `lookupBidiClass`.',
  'Bidi_Mirrored.txt': 'Equivalent lookup is provided by `UnicodeData.Extracted.DerivedBinaryProperties` via `lookupBidiMirrored`.',
  'Canonical_Combining_Class.txt': 'Equivalent lookup is provided by `UnicodeData.Extracted.DerivedCombiningClass` via `lookupCanonicalCombiningClass`.',
  'Case_Mapping.txt': 'Equivalent lookup is provided by `UnicodeCLib.lookupCase` via `lookupCaseMapping`.',
  'Cased.txt': 'Equivalent lookup is provided by `UnicodeCLib.lookupProp` via `lookupCased`.',
  'General_Category.txt': 'Equivalent lookup is provided by `UnicodeData.Extracted.DerivedGeneralCategory` via `lookupGC`.',
  'Line_Break.txt': 'Equivalent lookup is provided by `UnicodeData.Extracted.DerivedLineBreak` via `lookupLineBreak`.',
  'Lowercase.txt': 'Equivalent lookup is provided by `UnicodeCLib.lookupProp` via `lookupLowercase`.',
  'Math.txt': 'Equivalent lookup is provided by `UnicodeCLib.lookupProp` via `lookupMath`.',
  'Noncharacter_Code_Point.txt': 'This is computed directly in Lean by a range check; the generated table is not read directly.',
  'Numeric_Value.txt': 'Equivalent lookup is assembled from `UnicodeData.Basic` and `UnicodeData.Extracted.DerivedNumericValues` via `lookupNumericValue`.',
  'Other.txt': 'Equivalent lookup is provided by `UnicodeCLib.lookupProp` via `lookupOther`.',
  'Other_Alphabetic.txt': 'Equivalent lookup is provided by `UnicodeCLib.lookupProp` via `lookupAlphabetic`.',
  'Other_Default_Ignorable_Code_Point.txt': 'No current `UnicodeBasic.TableLookup` consumer reads this table directly.',
  'Other_Lowercase.txt': 'Equivalent lookup is provided by `UnicodeCLib.lookupProp` via `lookupLowercase`.',
  'Other_Math.txt': 'Equivalent lookup is provided by `UnicodeCLib.lookupProp` via `lookupMath`.',
  'Other_Uppercase.txt': 'Equivalent lookup is provided by `UnicodeCLib.lookupProp` via `lookupUppercase`.',
  'Prepended_Concatenation_Mark.txt': 'This property is only used as an exclusion inside `lookupDefaultIgnorableCodePoint`; the generated table is not read directly.',
  'Titlecase.txt': 'Equivalent lookup is derived from `lookupGC` via `lookupTitlecase`.',
  'Uppercase.txt': 'Equivalent lookup is provided by `UnicodeCLib.lookupProp` via `lookupUppercase`.',
  'Variation_Selector.txt': 'This property is only used as part of the `lookupDefaultIgnorableCodePoint` logic; the generated table is not read directly.'
};

function groupByDir(files: string[]): Map<string, string[]> {
  const out = new Map<string, string[]>();
  for (const file of files) {
    const group = file.split('/')[2] ?? 'root';
    const bucket = out.get(group) ?? [];
    bucket.push(file);
    out.set(group, bucket);
  }
  for (const bucket of out.values()) {
    bucket.sort((a, b) => a.localeCompare(b));
  }
  return out;
}

let markdown = '';
markdown += `# Data Table Usage\n\n`;
markdown += `Generated from \`UnicodeBasic/TableLookup.lean\`.\n\n`;
markdown += `## Directly Read By \`UnicodeBasic.TableLookup\`\n\n`;
markdown += `| data/table file | lookup | path |\n`;
markdown += `| --- | --- | --- |\n`;
for (const row of directUsages) {
  markdown += `| \`${row.file}\` | \`${row.lookup}\` | Lean reads \`${row.file}\` with \`include_str\` |\n`;
}

markdown += `\n## Backed By \`UnicodeCLib\`\n\n`;
markdown += `These lookups are exposed from Lean through externs in \`UnicodeBasic.TableLookup\`, but the implementation lives in generated C code under \`UnicodeCLib/\`.\n\n`;
markdown += `| lookup | backend | note |\n`;
markdown += `| --- | --- | --- |\n`;
for (const row of ffiBackedLookups) {
  markdown += `| \`${row.lookup}\` | \`${row.backend}\` | ${row.note} |\n`;
}

markdown += `\n## Backed By \`UnicodeData\`\n\n`;
markdown += `These lookups are implemented from \`UnicodeData\` modules rather than by reading a \`data/table/*.txt\` file in Lean.\n\n`;
markdown += `| lookup | backend | note |\n`;
markdown += `| --- | --- | --- |\n`;
for (const row of unicodeDataBackedLookups) {
  markdown += `| \`${row.lookup}\` | \`${row.backend}\` | ${row.note} |\n`;
}

markdown += `\n## Generated But Not Directly Read By \`UnicodeBasic.TableLookup\`\n\n`;
markdown += `These tables are generated by \`makeTables.lean\`, but current Lean code does not \`include_str\` them directly.\n\n`;
for (const [group, files] of groupByDir(unusedTables)) {
  markdown += `### ${group}\n\n`;
  for (const file of files) {
    const basename = file.slice(file.lastIndexOf('/') + 1);
    const noteText = unusedNotes[basename];
    const note = noteText ? ` - ${noteText}` : '';
    markdown += `- \`${file}\`${note}\n`;
  }
  markdown += `\n`;
}

writeText(path.join(repoRoot, 'docs', 'status', 'data-table-usage.md'), markdown);
console.log(`Wrote docs/status/data-table-usage.md for ${directUsages.length} direct tables and ${unusedTables.length} non-direct tables.`);
