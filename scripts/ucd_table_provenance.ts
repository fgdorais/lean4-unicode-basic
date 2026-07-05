#!/usr/bin/env node

import * as path from 'node:path';
import { repoRoot, relPosix, walkFiles, writeText } from './lib/ucd_report_lib.ts';

const generatedModules = walkFiles(path.join(repoRoot, 'lib', 'UnicodeBasic', 'TableLookupTables'), (p) => p.endsWith('.lean'))
  .map((absolutePath) => relPosix(absolutePath))
  .sort();

let markdown = '';
markdown += `# Data Table Provenance\n\n`;
markdown += `Generated from \`table-generators/makeTablesForLookup.lean\` and \`table-generators/MakeTablesForLookup/Common.lean\`.\n\n`;
markdown += `The lookup tables consumed by \`UnicodeBasic.TableLookup\` are pre-generated Lean modules under \`lib/UnicodeBasic/TableLookupTables\`. The generator constructs table data from \`UnicodeData\` and UCD parser modules directly, then renders Lean table modules in one step.\n\n`;
markdown += `| generated module |\n`;
markdown += `| --- |\n`;
for (const file of generatedModules) {
  markdown += `| \`${file}\` |\n`;
}

writeText(path.join(repoRoot, 'docs', 'status', 'data-table-provenance.md'), markdown);
console.log(`Wrote docs/status/data-table-provenance.md for ${generatedModules.length} generated modules.`);
