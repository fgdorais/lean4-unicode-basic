#!/usr/bin/env node

import * as path from 'node:path';
import { repoRoot, relPosix, readText, uniqueSorted, walkFiles, writeText } from './lib/ucd_report_lib.ts';

type FnInfo = {
  body: string;
  directSources: string[];
  directCalls: string[];
};

const sourceMap: Array<[RegExp, string[]]> = [
  [/UnicodeData\.data/g, ['data/ucd/core/UnicodeData.txt']],
  [/PropList\.data\.[A-Za-z_]+/g, ['data/ucd/core/PropList.txt']],
  [/PropList\.is[A-Za-z_]+/g, ['data/ucd/core/PropList.txt']],
  [/DerivedCoreProperties\.data/g, ['data/ucd/core/DerivedCoreProperties.txt']],
  [/CaseFolding\.data/g, ['data/ucd/core/CaseFolding.txt']],
  [/EmojiData\.data/g, ['data/ucd/emoji/emoji-data.txt']],
  [/BreakProperties\.data\.graphemeBreak/g, ['data/ucd/auxiliary/GraphemeBreakProperty.txt']],
  [/BreakProperties\.data\.wordBreak/g, ['data/ucd/auxiliary/WordBreakProperty.txt']],
  [/BreakProperties\.data\.sentenceBreak/g, ['data/ucd/auxiliary/SentenceBreakProperty.txt']],
  [/BreakProperties\.data\.lineBreak/g, ['data/ucd/core/LineBreak.txt']],
  [/PropertyAliases\./g, ['data/ucd/core/PropertyAliases.txt']],
  [/PropertyValueAliases\./g, ['data/ucd/core/PropertyValueAliases.txt']]
];

function extractFunctions(src: string): Map<string, FnInfo> {
  const out = new Map<string, FnInfo>();
  const lines = src.split(/\r?\n/);
  let currentName: string | null = null;
  let bodyLines: string[] = [];

  const flush = () => {
    if (!currentName) {
      return;
    }
    const body = bodyLines.join('\n');
    const directSources = uniqueSorted(
      [...body.matchAll(/include_str\s+"([^"]+)"/g)]
        .map((m) => path.posix.normalize(m[1].replace(/^\.\.\//, '')))
        .filter((p) => p.startsWith('data/ucd/'))
    );
    for (const [pattern, files] of sourceMap) {
      if (pattern.test(body)) {
        directSources.push(...files);
      }
      pattern.lastIndex = 0;
    }
    const directCalls = uniqueSorted(
      [...body.matchAll(/\b(mk[A-Z][A-Za-z0-9_]*)\b/g)]
        .map((m) => m[1])
        .filter((fn) => fn !== currentName)
    );
    out.set(currentName, {
      body,
      directSources: uniqueSorted(directSources),
      directCalls
    });
  };

  for (const line of lines) {
    const match = line.match(/^(?:partial\s+)?def\s+(mk[A-Za-z0-9_]+)\b/);
    if (match) {
      flush();
      currentName = match[1];
      bodyLines = [line];
      continue;
    }
    if (currentName) {
      if (line.startsWith('public def main')) {
        flush();
        currentName = null;
        bodyLines = [];
        break;
      }
      bodyLines.push(line);
    }
  }
  flush();
  return out;
}

function extractBranches(src: string): Array<{ table: string; entry: string }> {
  const branches: Array<{ table: string; entry: string }> = [];
  const lines = src.split(/\r?\n/);
  let currentTable: string | null = null;
  let bodyLines: string[] = [];

  const flush = () => {
    if (!currentTable) {
      return;
    }
    const body = bodyLines.join('\n');
    const entry = body.match(/\b(mk[A-Z][A-Za-z0-9_]*)\b/)?.[1];
    if (entry) {
      branches.push({ table: currentTable, entry });
    }
  };

  for (const line of lines) {
    const match = line.match(/^    \| "([^"]+)" =>/);
    if (match) {
      flush();
      currentTable = match[1];
      bodyLines = [line];
      continue;
    }
    if (currentTable) {
      bodyLines.push(line);
    }
  }
  flush();
  return branches;
}

function resolveSources(
  fn: string,
  infos: Map<string, FnInfo>,
  memo: Map<string, Set<string>>,
  visiting: Set<string>
): Set<string> {
  const cached = memo.get(fn);
  if (cached) {
    return new Set(cached);
  }
  if (visiting.has(fn)) {
    return new Set();
  }
  visiting.add(fn);
  const info = infos.get(fn);
  const sources = new Set<string>();
  if (info) {
    for (const src of info.directSources) {
      sources.add(src);
    }
    for (const call of info.directCalls) {
      for (const src of resolveSources(call, infos, memo, visiting)) {
        sources.add(src);
      }
    }
  }
  visiting.delete(fn);
  memo.set(fn, sources);
  return new Set(sources);
}

const src = readText(path.join(repoRoot, 'makeTables.lean'));
const infos = extractFunctions(src);
const branches = extractBranches(src);
const memo = new Map<string, Set<string>>();
const allUcdTxtFiles = walkFiles(path.join(repoRoot, 'data', 'ucd'), (p) => p.endsWith('.txt'))
  .map((absolutePath) => relPosix(absolutePath))
  .sort();

const rows = branches.map(({ table, entry }) => {
  const sources = [...resolveSources(entry, infos, memo, new Set())].sort();
  return { table, entry, sources };
}).sort((a, b) => a.table.localeCompare(b.table));

const tableSources = new Set<string>();
for (const row of rows) {
  for (const source of row.sources) {
    tableSources.add(source);
  }
}

const nonTableSources = allUcdTxtFiles.filter((file) => !tableSources.has(file));

function groupByDir(files: string[]): Map<string, string[]> {
  const out = new Map<string, string[]>();
  for (const file of files) {
    const group = file.split('/')[2] ?? 'root';
    const bucket = out.get(group) ?? [];
    bucket.push(file);
    out.set(group, bucket);
  }
  for (const [group, bucket] of out.entries()) {
    bucket.sort((a, b) => a.localeCompare(b));
    out.set(group, bucket);
  }
  return out;
}

let markdown = '';
markdown += `# Data Table Provenance\n\n`;
markdown += `Generated from \`makeTables.lean\`.\n\n`;
markdown += `## Used To Construct \`data/table\`\n\n`;
markdown += `| data/table file | generator | UCD sources |\n`;
markdown += `| --- | --- | --- |\n`;
for (const row of rows) {
  markdown += `| \`data/table/${row.table}.txt\` | \`${row.entry}\` | ${row.sources.map((s) => `\`${s}\``).join(', ')} |\n`;
}

markdown += `\n## Not Used To Construct \`data/table\`\n\n`;
markdown += `These UCD text files are present in the repository but are not referenced by \`makeTables.lean\`.\n\n`;
for (const [group, files] of groupByDir(nonTableSources)) {
  markdown += `### ${group}\n\n`;
  for (const file of files) {
    markdown += `- \`${file}\`\n`;
  }
  markdown += `\n`;
}

writeText(path.join(repoRoot, 'docs', 'status', 'data-table-provenance.md'), markdown);
console.log(`Wrote docs/status/data-table-provenance.md for ${rows.length} tables.`);
