#!/usr/bin/env node

import * as path from 'node:path';
import { repoRoot, readText, writeText } from './lib/ucd_report_lib.ts';

type NamesListTarget =
  | { kind: 'code'; code: number }
  | { kind: 'range'; start: number; end: number };

type NamesListAnnotation =
  | { kind: 'alias'; text: string }
  | { kind: 'note'; text: string }
  | { kind: 'crossRef'; text: string; target: NamesListTarget | null };

type NamesListEntry = {
  code: number;
  name: string;
  annotations: NamesListAnnotation[];
};

type NamesListSection = {
  comments: string[];
  start: number;
  title: string;
  end: number | null;
  entries: NamesListEntry[];
};

function leanString(text: string): string {
  return JSON.stringify(text);
}

function parseHexField(text: string): number {
  const v = Number.parseInt(text, 16);
  if (!Number.isFinite(v)) {
    throw new Error(`invalid hex value: ${text}`);
  }
  return v;
}

function parseTarget(text: string): NamesListTarget | null {
  const trimmed = text.trim();
  let m = trimmed.match(/^([0-9A-F]{4,6})-([0-9A-F]{4,6})$/i);
  if (m) {
    return { kind: 'range', start: parseHexField(m[1]), end: parseHexField(m[2]) };
  }
  m = trimmed.match(/^([0-9A-F]{4,6})$/i);
  if (m) {
    return { kind: 'code', code: parseHexField(m[1]) };
  }
  return null;
}

function parseCrossRef(text: string): { text: string; target: NamesListTarget | null } {
  const body = text.trim();
  if (!body.startsWith('(') || !body.endsWith(')')) {
    return { text: body, target: null };
  }
  const inner = body.slice(1, -1).trim();
  let label = inner;
  let target: NamesListTarget | null = null;
  const separators = [' - ', ': '];
  for (const sep of separators) {
    const idx = inner.lastIndexOf(sep);
    if (idx >= 0) {
      const candidate = inner.slice(idx + sep.length);
      const parsed = parseTarget(candidate);
      if (parsed) {
        label = inner.slice(0, idx).trim();
        target = parsed;
        break;
      }
    }
  }
  return { text: label, target };
}

function parseAnnotation(line: string): NamesListAnnotation | null {
  const trimmed = line.trimStart();
  if (trimmed.startsWith('=')) {
    return { kind: 'alias', text: trimmed.slice(1).trimStart() };
  }
  if (trimmed.startsWith('*')) {
    return { kind: 'note', text: trimmed.slice(1).trimStart() };
  }
  if (trimmed.startsWith('x')) {
    const body = trimmed.slice(1).trimStart();
    const { text, target } = parseCrossRef(body);
    return { kind: 'crossRef', text, target };
  }
  return null;
}

function parseNamesList(src: string): { preamble: string[]; sections: NamesListSection[] } {
  const lines = src.split(/\r?\n/);
  const preamble: string[] = [];
  const sections: NamesListSection[] = [];
  let currentSection: NamesListSection | null = null;
  let currentEntry: NamesListEntry | null = null;

  const flushEntry = () => {
    if (currentEntry && currentSection) {
      currentSection.entries.push(currentEntry);
    }
    currentEntry = null;
  };

  const flushSection = () => {
    flushEntry();
    if (currentSection) {
      sections.push(currentSection);
      currentSection = null;
    }
  };

  for (const raw of lines) {
    if (raw.trim().length === 0) {
      continue;
    }

    if (raw.startsWith(';')) {
      if (currentSection) {
        currentSection.comments.push(raw);
      } else {
        preamble.push(raw);
      }
      continue;
    }

    if (raw.startsWith('@')) {
      const fields = raw.split('\t');
      const marker = fields[0] ?? '';
      if (marker === '@@' && fields.length >= 3) {
        flushSection();
        const start = parseHexField(fields[1]!);
        const endField = fields[fields.length - 1]!;
        const maybeEnd = parseTarget(endField);
        const title = fields.slice(2, fields.length - (maybeEnd ? 1 : 0)).join('\t').trim();
        currentSection = {
          comments: [raw],
          start,
          title,
          end: maybeEnd?.kind === 'code' ? maybeEnd.code : maybeEnd?.kind === 'range' ? maybeEnd.end : null,
          entries: []
        };
      } else {
        if (currentSection) {
          currentSection.comments.push(raw);
        } else {
          preamble.push(raw);
        }
      }
      continue;
    }

    const codeMatch = raw.match(/^([0-9A-F]{4,6})\t(.*)$/i);
    if (codeMatch) {
      flushEntry();
      currentEntry = {
        code: parseHexField(codeMatch[1]!),
        name: codeMatch[2]!,
        annotations: []
      };
      continue;
    }

    if (raw.startsWith('\t')) {
      const annotation = currentEntry ? parseAnnotation(raw) : null;
      if (annotation && currentEntry) {
        currentEntry.annotations.push(annotation);
      } else {
        if (currentSection) {
          currentSection.comments.push(raw);
        } else {
          preamble.push(raw);
        }
      }
      continue;
    }

    if (currentSection) {
      currentSection.comments.push(raw);
    } else {
      preamble.push(raw);
    }
  }

  flushSection();
  return { preamble, sections };
}

function emitTarget(target: NamesListTarget): string {
  return target.kind === 'code'
    ? `.code ${target.code}`
    : `.range ${target.start} ${target.end}`;
}

function emitAnnotation(annotation: NamesListAnnotation): string {
  switch (annotation.kind) {
    case 'alias':
      return `.alias ${leanString(annotation.text)}`;
    case 'note':
      return `.note ${leanString(annotation.text)}`;
    case 'crossRef':
      return `.crossRef ${leanString(annotation.text)} ${annotation.target ? `(some (${emitTarget(annotation.target)}))` : 'none'}`;
  }
}

function emitEntry(entry: NamesListEntry, indent: string): string {
  return `${indent}{\n${indent}  code := ${entry.code}\n${indent}  name := ${leanString(entry.name)}\n${indent}  annotations := #[\n${entry.annotations.map((a) => `${indent}    ${emitAnnotation(a)}`).join(',\n')}\n${indent}  ]\n${indent}}`;
}

function emitComments(lines: string[]): string {
  return lines.map((line) => `-- ${line}`).join('\n');
}

function chunk<T>(items: T[], size: number): T[][] {
  const out: T[][] = [];
  for (let i = 0; i < items.length; i += size) {
    out.push(items.slice(i, i + size));
  }
  return out;
}

const srcPath = path.join(repoRoot, 'data', 'ucd', 'core', 'NamesList.txt');
const src = readText(srcPath);
const { preamble, sections } = parseNamesList(src);

let out = '';
out += `/-\n`;
out += `Copyright © 2026 François G. Dorais. All rights reserved.\n`;
out += `Released under Apache 2.0 license as described in the file LICENSE.\n`;
out += `-/\n`;
out += `module\n`;
out += `import UnicodeBasic.Types\n\n`;
out += `namespace Unicode\n\n`;
out += `-- Generated from data/ucd/core/NamesList.txt by scripts/generate_names_list.ts.\n`;
out += `-- The raw text is intentionally not embedded with include_str.\n\n`;
out += `public inductive NamesListTarget where\n`;
out += `| code (code : UInt32)\n`;
out += `| range (start : UInt32) (rangeEnd : UInt32)\n`;
out += `deriving Inhabited, Repr\n\n`;
out += `public inductive NamesListAnnotation where\n`;
out += `| alias (text : String)\n`;
out += `| note (text : String)\n`;
out += `| crossRef (text : String) (target : Option NamesListTarget)\n`;
out += `deriving Inhabited, Repr\n\n`;
out += `public structure NamesListEntry where\n`;
out += `  public code : UInt32\n`;
out += `  public name : String\n`;
out += `  public annotations : Array NamesListAnnotation\n`;
out += `deriving Inhabited, Repr\n\n`;

if (preamble.length > 0) {
  out += `${emitComments(preamble)}\n\n`;
}

for (const [idx, section] of sections.entries()) {
  out += `${emitComments(section.comments)}\n`;
  const parts = chunk(section.entries, 100);
  for (const [partIdx, part] of parts.entries()) {
    out += `public def NamesList.section${idx}Part${partIdx} : Array NamesListEntry := #[\n`;
    out += `${part.map((entry) => emitEntry(entry, '  ')).join(',\n')}\n`;
    out += `]\n\n`;
  }
  out += `public def NamesList.section${idx} : Array NamesListEntry := Id.run do\n`;
  out += `  let mut data := #[]\n`;
  for (const [partIdx] of parts.entries()) {
    out += `  data := data ++ NamesList.section${idx}Part${partIdx}\n`;
  }
  out += `  return data\n\n`;
}

out += `end Unicode\n`;

writeText(path.join(repoRoot, 'UnicodeData', 'NamesList.lean'), out);
console.log(`Wrote UnicodeData/NamesList.lean from ${sections.length} parsed sections.`);
