#!/usr/bin/env node

import * as path from 'node:path';
import { repoRoot, readText, writeText } from './lib/ucd_report_lib.ts';

type DoNotEmitKind =
  | 'Indic_Atomic_Consonant'
  | 'Indic_Consonant_Conjunct'
  | 'Indic_Vowel_Letter'
  | 'Bengali_Khanda_Ta'
  | 'Malayalam_Chillu'
  | 'Tamil_Shrii'
  | 'Dotless_Form'
  | 'Arabic_Tashkil'
  | 'Hamza_Form'
  | 'Precomposed_Form'
  | 'Deprecated'
  | 'Discouraged'
  | 'Preferred_Spelling';

type DoNotEmitEntry = {
  source: number[];
  replacement: number[];
  kind: DoNotEmitKind;
  comment: string | null;
};

function leanString(text: string): string {
  return JSON.stringify(text);
}

function parseHex(text: string): number {
  const n = Number.parseInt(text, 16);
  if (!Number.isFinite(n)) {
    throw new Error(`invalid hex value: ${text}`);
  }
  return n;
}

function parseCodeSequence(text: string): number[] {
  const trimmed = text.trim();
  if (trimmed.length === 0) {
    return [];
  }
  return trimmed.split(/\s+/).map(parseHex);
}

function parseKind(text: string): DoNotEmitKind {
  switch (text) {
    case 'Indic_Atomic_Consonant':
    case 'Indic_Consonant_Conjunct':
    case 'Indic_Vowel_Letter':
    case 'Bengali_Khanda_Ta':
    case 'Malayalam_Chillu':
    case 'Tamil_Shrii':
    case 'Dotless_Form':
    case 'Arabic_Tashkil':
    case 'Hamza_Form':
    case 'Precomposed_Form':
    case 'Deprecated':
    case 'Discouraged':
    case 'Preferred_Spelling':
      return text;
    default:
      throw new Error(`unknown DoNotEmit kind: ${text}`);
  }
}

function emitKind(kind: DoNotEmitKind): string {
  switch (kind) {
    case 'Indic_Atomic_Consonant':
      return '.indicAtomicConsonant';
    case 'Indic_Consonant_Conjunct':
      return '.indicConsonantConjunct';
    case 'Indic_Vowel_Letter':
      return '.indicVowelLetter';
    case 'Bengali_Khanda_Ta':
      return '.bengaliKhandaTa';
    case 'Malayalam_Chillu':
      return '.malayalamChillu';
    case 'Tamil_Shrii':
      return '.tamilShrii';
    case 'Dotless_Form':
      return '.dotlessForm';
    case 'Arabic_Tashkil':
      return '.arabicTashkil';
    case 'Hamza_Form':
      return '.hamzaForm';
    case 'Precomposed_Form':
      return '.precomposedForm';
    case 'Deprecated':
      return '.deprecated';
    case 'Discouraged':
      return '.discouraged';
    case 'Preferred_Spelling':
      return '.preferredSpelling';
  }
}

function parseDoNotEmit(src: string): DoNotEmitEntry[] {
  const items: DoNotEmitEntry[] = [];
  for (const raw of src.split(/\r?\n/)) {
    const line = raw.trimEnd();
    if (line.length === 0) {
      continue;
    }
    if (line.startsWith('#')) {
      continue;
    }
    const hashIndex = line.indexOf('#');
    const body = (hashIndex >= 0 ? line.slice(0, hashIndex) : line).trimEnd();
    const comment = hashIndex >= 0 ? line.slice(hashIndex + 1).trim() : null;
    const parts = body.split(';').map((part) => part.trim());
    if (parts.length !== 3) {
      throw new Error(`invalid DoNotEmit record: ${raw}`);
    }
    items.push({
      source: parseCodeSequence(parts[0]!),
      replacement: parseCodeSequence(parts[1]!),
      kind: parseKind(parts[2]!),
      comment
    });
  }
  return items;
}

function emitCodeSequence(seq: number[]): string {
  return `#[${seq.join(', ')}]`;
}

function emitRecord(entry: DoNotEmitEntry, indent: string): string {
  return `${indent}{\n${indent}  source := ${emitCodeSequence(entry.source)}\n${indent}  replacement := ${emitCodeSequence(entry.replacement)}\n${indent}  kind := ${emitKind(entry.kind)}\n${indent}  comment := ${entry.comment === null ? 'none' : `(some ${leanString(entry.comment)})`}\n${indent}}`;
}

function chunk<T>(items: T[], size: number): T[][] {
  const out: T[][] = [];
  for (let i = 0; i < items.length; i += size) {
    out.push(items.slice(i, i + size));
  }
  return out;
}

const srcPath = path.join(repoRoot, 'data', 'ucd', 'core', 'DoNotEmit.txt');
const src = readText(srcPath);
const items = parseDoNotEmit(src);
const entries = items;
const entryChunks = chunk(entries, 250);

let out = '';
out += `/-\n`;
out += `Copyright © 2026 François G. Dorais. All rights reserved.\n`;
out += `Released under Apache 2.0 license as described in the file LICENSE.\n`;
out += `-/\n`;
out += `module\n`;
out += `import UnicodeBasic.Types\n\n`;
out += `namespace Unicode\n\n`;
out += `-- Generated from data/ucd/core/DoNotEmit.txt by scripts/generate_do_not_emit.ts.\n`;
out += `-- The raw text is intentionally not embedded with include_str.\n\n`;
out += `public inductive DoNotEmitKind where\n`;
out += `| indicAtomicConsonant\n`;
out += `| indicConsonantConjunct\n`;
out += `| indicVowelLetter\n`;
out += `| bengaliKhandaTa\n`;
out += `| malayalamChillu\n`;
out += `| tamilShrii\n`;
out += `| dotlessForm\n`;
out += `| arabicTashkil\n`;
out += `| hamzaForm\n`;
out += `| precomposedForm\n`;
out += `| deprecated\n`;
out += `| discouraged\n`;
out += `| preferredSpelling\n`;
out += `deriving Inhabited, Repr, BEq, DecidableEq\n\n`;
out += `public structure DoNotEmitEntry where\n`;
out += `  public source : Array UInt32\n`;
out += `  public replacement : Array UInt32\n`;
out += `  public kind : DoNotEmitKind\n`;
out += `  public comment : Option String\n`;
out += `deriving Inhabited, Repr\n\n`;
out += `-- Source comments from DoNotEmit.txt are preserved below as ordinary Lean comments.\n`;
for (const raw of src.split(/\r?\n/)) {
  const line = raw.trimEnd();
  if (line.length === 0) {
    out += `--\n`;
  } else if (line.startsWith('#')) {
    out += `-- ${line.slice(1).trimStart()}\n`;
  }
}
out += `\n`;
for (const [idx, chunkEntries] of entryChunks.entries()) {
  out += `public def DoNotEmit.recordChunk${idx} : Array DoNotEmitEntry := #[\n`;
  out += `${chunkEntries.map((entry) => emitRecord(entry, '  ')).join(',\n')}\n`;
  out += `]\n\n`;
}
out += `public def DoNotEmit.records : Array DoNotEmitEntry := Id.run do\n`;
out += `  let mut data := #[]\n`;
for (const [idx] of entryChunks.entries()) {
  out += `  data := data ++ DoNotEmit.recordChunk${idx}\n`;
}
out += `  return data\n\n`;
out += `public def DoNotEmit.data : Array DoNotEmitEntry := Id.run do\n`;
out += `  let mut data := #[]\n`;
for (const [idx] of entryChunks.entries()) {
  out += `  data := data ++ DoNotEmit.recordChunk${idx}\n`;
}
out += `  return data\n\n`;
out += `end Unicode\n`;

writeText(path.join(repoRoot, 'UnicodeData', 'DoNotEmit.lean'), out);
console.log(`Wrote UnicodeData/DoNotEmit.lean from ${entries.length} parsed records and ${items.length - entries.length} comments.`);
