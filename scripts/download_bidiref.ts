#!/usr/bin/env node

// Download the Unicode Bidirectional Algorithm reference implementation
// sources used by UnicodeCLib/bidi.c.

import * as fs from 'node:fs';
import * as path from 'node:path';
import { fileURLToPath } from 'node:url';

const __filename = fileURLToPath(import.meta.url);
const __dirname = path.dirname(__filename);

const repoRoot = path.join(__dirname, '..');
const bidirefDir = path.join(repoRoot, 'UnicodeCLib', 'bidiref');

const SOURCE_BASE = 'https://www.unicode.org/Public/PROGRAMS/BidiReferenceC/16.0.0/source';
const INCLUDE_BASE = 'https://www.unicode.org/Public/PROGRAMS/BidiReferenceC/16.0.0/include';

type DownloadSpec = {
    readonly url: string;
    readonly dest: string;
};

const files: readonly DownloadSpec[] = [
    { url: `${SOURCE_BASE}/bidiref.c`, dest: path.join(bidirefDir, 'bidiref.c') },
    { url: `${SOURCE_BASE}/bidiref1.c`, dest: path.join(bidirefDir, 'bidiref1.c') },
    { url: `${SOURCE_BASE}/bidirefp.h`, dest: path.join(bidirefDir, 'bidirefp.h') },
    { url: `${SOURCE_BASE}/brinput.c`, dest: path.join(bidirefDir, 'brinput.c') },
    { url: `${SOURCE_BASE}/brrule.c`, dest: path.join(bidirefDir, 'brrule.c') },
    { url: `${SOURCE_BASE}/brtable.c`, dest: path.join(bidirefDir, 'brtable.c') },
    { url: `${SOURCE_BASE}/brtest.c`, dest: path.join(bidirefDir, 'brtest.c') },
    { url: `${SOURCE_BASE}/brutils.c`, dest: path.join(bidirefDir, 'brutils.c') },
    { url: `${INCLUDE_BASE}/bidiref.h`, dest: path.join(bidirefDir, 'bidiref.h') }
];

async function downloadFile(spec: DownloadSpec): Promise<void> {
    const res = await fetch(spec.url);
    if (!res.ok) {
        throw new Error(`HTTP ${res.status} while fetching ${spec.url}`);
    }
    const body = Buffer.from(await res.arrayBuffer());
    fs.writeFileSync(spec.dest, body);
    console.log(`✅ ${path.basename(spec.dest)}`);
}

async function main(): Promise<void> {
    console.log(`Cleaning ${bidirefDir}`);
    fs.rmSync(bidirefDir, { recursive: true, force: true });
    fs.mkdirSync(bidirefDir, { recursive: true });

    console.log(`Downloading ${files.length} bidiref source files`);
    for (const file of files) {
        await downloadFile(file);
    }
}

main().catch((err: unknown) => {
    const message = err instanceof Error ? err.message : String(err);
    console.error(`Failed to download bidiref sources: ${message}`);
    process.exit(1);
});
