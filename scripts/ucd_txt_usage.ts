#!/usr/bin/env node

import * as fs from 'node:fs';
import * as path from 'node:path';
import { repoRoot, relPosix, walkFiles, walkFilesSkipping, writeText } from './lib/ucd_report_lib.ts';

type MatchKind = 'direct';

type Match = {
  file: string;
  line: number;
  text: string;
  kind: MatchKind;
};

type FileReport = {
  absolutePath: string;
  relativePath: string;
  group: string;
  matches: Match[];
};

type Target = {
  absolutePath: string;
  relativePath: string;
  basename: string;
  patterns: string[];
};

function groupOf(relativePath: string): string {
  const parts = relativePath.split('/');
  return parts.length >= 3 ? parts[2] : 'root';
}

function usageProfile(matches: Match[]): string {
  return matches.length > 0 ? 'used' : 'unused';
}

function formatPlaces(matches: Match[]): string {
  if (matches.length === 0) {
    return '';
  }
  const sample = matches.slice(0, 4).map((m) => `${m.file}:${m.line} [${m.kind}]`).join(', ');
  return matches.length > 4 ? `${sample}, ... (${matches.length} matches)` : `${sample} (${matches.length} matches)`;
}

function renderTable(rows: FileReport[]): string {
  let out = '';
  out += `| File | Usage | Places |\n`;
  out += `| --- | --- | --- |\n`;
  for (const row of rows) {
    out += `| \`${row.relativePath}\` | ${usageProfile(row.matches)} | ${formatPlaces(row.matches)} |\n`;
  }
  return out;
}

const scanFiles = walkFilesSkipping(repoRoot, {
  skipDir: (absolutePath) => {
    const relativePath = relPosix(absolutePath);
    return (
      relativePath === '.git' ||
      relativePath === '.lake' ||
      relativePath === 'data/ucd' ||
      relativePath === 'data/table' ||
      relativePath === 'docs/status' ||
      relativePath.startsWith('.git/') ||
      relativePath.startsWith('.lake/') ||
      relativePath.startsWith('data/ucd/') ||
      relativePath.startsWith('data/table/') ||
      relativePath.startsWith('docs/status/')
    );
  },
  includeFile: (absolutePath) => {
    const relativePath = relPosix(absolutePath);
    return (
      relativePath === 'UnicodeBasic.lean' ||
      relativePath === 'UnicodeData.lean' ||
      relativePath.startsWith('UnicodeBasic/') ||
      relativePath.startsWith('UnicodeData/')
    );
  }
});

const scanContents = new Map<string, string>();
for (const absolutePath of scanFiles) {
  scanContents.set(absolutePath, fs.readFileSync(absolutePath, 'utf8'));
}

const targets: Target[] = walkFiles(path.join(repoRoot, 'data', 'ucd'), (p) => p.endsWith('.txt')).map((absolutePath) => {
  const relativePath = relPosix(absolutePath);
  const basename = path.basename(absolutePath);
  return {
    absolutePath,
    relativePath,
    basename,
    patterns: [relativePath, `../${relativePath}`, basename]
  };
});

const reports: FileReport[] = targets.map((target) => {
  const matches: Match[] = [];
  for (const [scanPath, contents] of scanContents.entries()) {
    const file = relPosix(scanPath);
    if (!target.patterns.some((pattern) => contents.includes(pattern))) {
      continue;
    }
    const lines = contents.split(/\r?\n/);
    for (let lineNo = 0; lineNo < lines.length; lineNo += 1) {
      const text = lines[lineNo];
      for (const pattern of target.patterns) {
        if (text.includes(pattern)) {
          matches.push({ file, line: lineNo + 1, text, kind: 'direct' });
          break;
        }
      }
    }
  }
  matches.sort((a, b) => (a.file === b.file ? a.line - b.line : a.file.localeCompare(b.file)));
  return {
    absolutePath: target.absolutePath,
    relativePath: target.relativePath,
    group: groupOf(target.relativePath),
    matches
  };
});

const byGroup = new Map<string, FileReport[]>();
for (const report of reports) {
  const bucket = byGroup.get(report.group) ?? [];
  bucket.push(report);
  byGroup.set(report.group, bucket);
}

const usedCount = reports.filter((r) => r.matches.length > 0).length;
const unusedCount = reports.filter((r) => r.matches.length === 0).length;

let markdown = '';
markdown += `# UCD TXT Usage\n\n`;
markdown += `Generated from a repo scan of \`data/ucd/**/*.txt\` against Lean library files in \`UnicodeBasic/\` and \`UnicodeData/\`.\n\n`;
markdown += `## Summary\n\n`;
markdown += `- Total txt files: ${reports.length}\n`;
markdown += `- Used by Lean library: ${usedCount}\n`;
markdown += `- Unused: ${unusedCount}\n\n`;

for (const group of [...byGroup.keys()].sort()) {
  markdown += `## ${group}\n\n`;
  markdown += renderTable(byGroup.get(group)!.sort((a, b) => a.relativePath.localeCompare(b.relativePath)));
  markdown += `\n`;
}

writeText(path.join(repoRoot, 'docs', 'status', 'ucd-txt-usage.md'), markdown);
console.log(`Wrote docs/status/ucd-txt-usage.md for ${reports.length} files.`);
