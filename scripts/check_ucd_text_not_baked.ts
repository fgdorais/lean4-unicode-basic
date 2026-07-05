#!/usr/bin/env node

import * as fs from 'node:fs';
import * as path from 'node:path';
import { repoRoot } from './lib/ucd_report_lib.ts';

type Check = {
  name: string;
  snippets: string[];
};

const checks: Check[] = [
  {
    name: 'DoNotEmit.txt',
    snippets: [
      [
        '# DoNotEmit-17.0.0.txt',
        '# Date: 2025-08-14',
        '# © 2025 Unicode®, Inc.',
        '# Unicode and the Unicode Logo are registered trademarks of Unicode, Inc. in the U.S. and other countries.',
        '# For terms of use and license, see https://www.unicode.org/terms_of_use.html',
        '#',
        '# For documentation, see UAX #44: Unicode Character Database,'
      ].join('\n'),
      [
        '# Do_Not_Emit',
        '#',
        '# This file is part of the Unicode Character Database. It does not define',
        '# any properties, but rather provides additional information about',
        '# characters or character sequences that should not be emitted or generated',
        '# in newly authored text.'
      ].join('\n')
    ]
  },
  {
    name: 'NamesList.txt',
    snippets: [
      [
        '; charset=UTF-8',
        '@@@\tThe Unicode Standard 17.0.0',
        '@@@+\tNamesList-17.0.0.txt',
        '@+\tGeneration Date: 2025-07-30, 17:12:45 GMT',
        '\tUnicode 17.0.0 final names list.',
        '\tThis file is semi-automatically derived from UnicodeData.txt and',
        '\ta set of manually created annotations using a script to select'
      ].join('\n'),
      [
        '@@\t0000\tC0 Controls and Basic Latin (Basic Latin)\t007F',
        '@@+',
        '@\t\tC0 controls',
        '@+\t\tAlias names are those for ISO/IEC 6429:1992. Commonly used alternative aliases are also shown.',
        '0000\t<control>',
        '\t= NULL',
        '0001\t<control>'
      ].join('\n')
    ]
  }
];

function walkFiles(dir: string): string[] {
  const out: string[] = [];
  for (const entry of fs.readdirSync(dir, { withFileTypes: true })) {
    const full = path.join(dir, entry.name);
    if (entry.isDirectory()) {
      out.push(...walkFiles(full));
    } else if (entry.isFile()) {
      out.push(full);
    }
  }
  return out;
}

const buildDir = path.join(repoRoot, '.lake', 'build');
if (!fs.existsSync(buildDir)) {
  throw new Error(`build directory not found: ${buildDir}`);
}

const artifacts = walkFiles(buildDir).filter((file) =>
  file.endsWith('.olean') || file.endsWith('.so') || file.endsWith('.o') || file.endsWith('.c')
);

const hits: Array<{ check: string; needle: string; artifact: string }> = [];
for (const check of checks) {
  for (const needle of check.snippets) {
    for (const artifact of artifacts) {
      const contents = fs.readFileSync(artifact);
      if (contents.includes(Buffer.from(needle, 'utf8'))) {
        hits.push({ check: check.name, needle, artifact: path.relative(repoRoot, artifact) });
      }
    }
  }
}

if (hits.length > 0) {
  const lines = hits
    .map((hit) => `${hit.check}: found baked text snippet in ${hit.artifact}`)
    .join('\n');
  throw new Error(`UCD text was baked into build artifacts:\n${lines}`);
}

console.log(`Checked ${artifacts.length} artifacts; no baked DoNotEmit/NamesList text found.`);
