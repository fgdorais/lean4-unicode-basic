#!/usr/bin/env node

import * as fs from 'node:fs';
import * as path from 'node:path';
import { spawnSync } from 'node:child_process';
import { fileURLToPath } from 'node:url';

export const scriptDir = path.dirname(fileURLToPath(import.meta.url));
export const repoRoot = path.resolve(scriptDir, '../..');

export function relPosix(absolutePath: string): string {
  return path.relative(repoRoot, absolutePath).split(path.sep).join('/');
}

export function ensureDir(absolutePath: string): void {
  fs.mkdirSync(absolutePath, { recursive: true });
}

export function readText(absolutePath: string): string {
  return fs.readFileSync(absolutePath, 'utf8');
}

export function writeText(absolutePath: string, contents: string): void {
  ensureDir(path.dirname(absolutePath));
  fs.writeFileSync(absolutePath, contents);
}

export function walkFiles(absoluteDir: string, predicate: (absolutePath: string) => boolean): string[] {
  const out: string[] = [];
  const stack: string[] = [absoluteDir];
  while (stack.length > 0) {
    const current = stack.pop()!;
    for (const entry of fs.readdirSync(current, { withFileTypes: true })) {
      const full = path.join(current, entry.name);
      if (entry.isDirectory()) {
        stack.push(full);
      } else if (predicate(full)) {
        out.push(full);
      }
    }
  }
  out.sort();
  return out;
}

export function walkFilesSkipping(
  absoluteDir: string,
  options: {
    readonly skipDir?: (absolutePath: string) => boolean;
    readonly includeFile?: (absolutePath: string) => boolean;
  }
): string[] {
  const out: string[] = [];
  const stack: string[] = [absoluteDir];
  while (stack.length > 0) {
    const current = stack.pop()!;
    if (options.skipDir?.(current)) {
      continue;
    }
    for (const entry of fs.readdirSync(current, { withFileTypes: true })) {
      const full = path.join(current, entry.name);
      if (entry.isDirectory()) {
        if (!options.skipDir?.(full)) {
          stack.push(full);
        }
      } else if (options.includeFile?.(full) ?? true) {
        out.push(full);
      }
    }
  }
  out.sort();
  return out;
}

export function uniqueSorted(values: Iterable<string>): string[] {
  return [...new Set(values)].sort();
}

export function runRg(args: string[]): string[] {
  const res = spawnSync('rg', args, {
    cwd: repoRoot,
    encoding: 'utf8',
    maxBuffer: 10_000_000
  });
  if (res.status === 1) {
    return [];
  }
  if (res.status !== 0) {
    const stderr = (res.stderr ?? '').toString();
    throw new Error(`rg failed: ${stderr || `exit code ${res.status}`}`);
  }
  return (res.stdout ?? '').split(/\r?\n/).filter(Boolean);
}
