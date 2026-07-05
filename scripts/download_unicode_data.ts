#!/usr/bin/env node

// This script downloads Unicode 17.0.0 UCD files into data/ucd.
// Cleanup is intentionally handled by the justfile, not by this script.

import * as fs from 'node:fs';
import * as path from 'node:path';
import * as crypto from 'node:crypto';
import { execSync } from 'node:child_process';
import { fileURLToPath } from 'node:url';

// Resolve script directory
const __filename = fileURLToPath(import.meta.url);
const __dirname = path.dirname(__filename);

const dataDir = path.join(__dirname, '..', 'table-generators');
const ucdDir = path.join(dataDir, 'data-ucd');
const metaPath = path.join(dataDir, '.data-ucd-download-meta.json');

// Base URL common to all downloads
const BASE_URL = 'https://www.unicode.org/Public/17.0.0/ucd';

// Types & Interfaces
interface UnicodeGroup {
    readonly urlPath?: string;
    readonly files: readonly string[];
}

interface DownloadTask {
    readonly groupName: string;
    readonly fileName: string;
    readonly url: string;
    readonly destPath: string;
}

interface GroupStats {
    success: number;
    failed: number;
    skipped: number;
}

interface DownloadSummary {
    success: number;
    failed: number;
    skipped: number;
    unihanExtracted: number;
    byGroup: Record<string, GroupStats>;
}

interface DownloadMetaEntry {
    readonly url: string;
    readonly etag?: string;
    readonly lastModified?: string;
    readonly contentLength?: string;
    readonly sha256: string;
}

type DownloadMeta = Record<string, DownloadMetaEntry>;

// Colorization auto-detection
const useColor = process.stdout.isTTY && !process.env.NO_COLOR;
const colors = {
    red: useColor ? '\x1b[31m' : '',
    green: useColor ? '\x1b[32m' : '',
    blue: useColor ? '\x1b[34m' : '',
    yellow: useColor ? '\x1b[33m' : '',
    cyan: useColor ? '\x1b[36m' : '',
    reset: useColor ? '\x1b[0m' : ''
};

// Prepare directories. Do not delete existing data here; justfile owns cleanup.
console.log(`${colors.cyan}📂 Preparing directories...${colors.reset}`);
try {
    fs.mkdirSync(ucdDir, { recursive: true });
} catch (err: unknown) {
    const message = err instanceof Error ? err.message : String(err);
    console.error(`Failed to prepare directory: ${message}`);
    process.exit(1);
}

// Unicode groups configuration mapped to common base URL
const groups: Record<string, UnicodeGroup> = {
    core: {
        files: [
            "ArabicShaping.txt",
            "BidiBrackets.txt",
            "BidiMirroring.txt",
            "Blocks.txt",
            "CJKRadicals.txt",
            "CompositionExclusions.txt",
            "DoNotEmit.txt",
            "EastAsianWidth.txt",
            "EmojiSources.txt",
            "EquivalentUnifiedIdeograph.txt",
            "HangulSyllableType.txt",
            "IndicPositionalCategory.txt",
            "IndicSyllabicCategory.txt",
            "Jamo.txt",
            "LineBreak.txt",
            "NameAliases.txt",
            "NamedSequences.txt",
            "NamedSequencesProv.txt",
            "NamesList.txt",
            "NormalizationCorrections.txt",
            "NushuSources.txt",
            "PropertyAliases.txt",
            "PropertyValueAliases.txt",
            "PropList.txt",
            "Scripts.txt",
            "ScriptExtensions.txt",
            "SpecialCasing.txt",
            "StandardizedVariants.txt",
            "TangutSources.txt",
            "UnicodeData.txt",
            "Unikemet.txt",
            "VerticalOrientation.txt",
            "USourceData.txt",
            "CaseFolding.txt",
            "DerivedAge.txt",
            "DerivedCoreProperties.txt",
            "DerivedNormalizationProps.txt"
        ]
    },
    extracted: {
        urlPath: 'extracted',
        files: [
            "DerivedBidiClass.txt",
            "DerivedBinaryProperties.txt",
            "DerivedCombiningClass.txt",
            "DerivedDecompositionType.txt",
            "DerivedEastAsianWidth.txt",
            "DerivedGeneralCategory.txt",
            "DerivedJoiningGroup.txt",
            "DerivedJoiningType.txt",
            "DerivedLineBreak.txt",
            "DerivedName.txt",
            "DerivedNumericType.txt",
            "DerivedNumericValues.txt"
        ]
    },
    auxiliary: {
        urlPath: 'auxiliary',
        files: [
            "GraphemeBreakProperty.txt",
            "GraphemeBreakTest.txt",
            "LineBreakTest.txt",
            "SentenceBreakProperty.txt",
            "SentenceBreakTest.txt",
            "WordBreakProperty.txt",
            "WordBreakTest.txt"
        ]
    },
    emoji: {
        urlPath: 'emoji',
        files: [
            "emoji-data.txt",
            "emoji-variation-sequences.txt"
        ]
    },
    conformance: {
        files: [
            "BidiCharacterTest.txt",
            "BidiTest.txt",
            "NormalizationTest.txt"
        ]
    },
    unihan: {
        files: [
            "Unihan.zip"
        ]
    }
};

// Generate download tasks using refactored BASE_URL inheritance
const tasks: DownloadTask[] = [];
for (const [groupName, group] of Object.entries(groups)) {
    const groupPath = path.join(ucdDir, groupName);
    fs.mkdirSync(groupPath, { recursive: true });

    const groupBaseUrl = group.urlPath ? `${BASE_URL}/${group.urlPath}` : BASE_URL;

    for (const file of group.files) {
        tasks.push({
            groupName,
            fileName: file,
            url: `${groupBaseUrl}/${file}`,
            destPath: path.join(groupPath, file)
        });
    }
}

// Download metrics
const summary: DownloadSummary = {
    success: 0,
    failed: 0,
    skipped: 0,
    unihanExtracted: 0,
    byGroup: {}
};

function metaKey(task: DownloadTask): string {
    return `${task.groupName}/${task.fileName}`;
}

function readMeta(): DownloadMeta {
    if (!fs.existsSync(metaPath)) {
        return {};
    }
    try {
        return JSON.parse(fs.readFileSync(metaPath, 'utf8')) as DownloadMeta;
    } catch (err: unknown) {
        const message = err instanceof Error ? err.message : String(err);
        console.warn(`${colors.yellow}⚠️ Warning: ignoring invalid download metadata: ${message}${colors.reset}`);
        return {};
    }
}

function writeMeta(meta: DownloadMeta): void {
    fs.writeFileSync(metaPath, `${JSON.stringify(meta, null, 2)}\n`);
}

function hashFile(filePath: string, algorithm: 'md5' | 'sha256'): string {
    return crypto.createHash(algorithm).update(fs.readFileSync(filePath)).digest('hex');
}

function sha256File(filePath: string): string {
    return hashFile(filePath, 'sha256');
}

function hashFromEtag(etag: string | undefined): { algorithm: 'md5' | 'sha256'; value: string } | undefined {
    const value = etag?.replace(/^W\//, '').replace(/^"|"$/g, '').toLowerCase();
    if (!value) {
        return undefined;
    }
    if (/^[0-9a-f]{64}$/.test(value)) {
        return { algorithm: 'sha256', value };
    }
    if (/^[0-9a-f]{32}$/.test(value)) {
        return { algorithm: 'md5', value };
    }
    return undefined;
}

function remoteHeaders(res: Response): Pick<DownloadMetaEntry, 'etag' | 'lastModified' | 'contentLength'> {
    return {
        etag: res.headers.get('etag') ?? undefined,
        lastModified: res.headers.get('last-modified') ?? undefined,
        contentLength: res.headers.get('content-length') ?? undefined
    };
}

function sameRemote(
    entry: DownloadMetaEntry | undefined,
    headers: Pick<DownloadMetaEntry, 'etag' | 'lastModified' | 'contentLength'>
): boolean {
    if (!entry) {
        return false;
    }
    if (headers.etag && entry.etag) {
        return headers.etag === entry.etag;
    }
    if (headers.lastModified && entry.lastModified) {
        return headers.lastModified === entry.lastModified && headers.contentLength === entry.contentLength;
    }
    return false;
}

function localMatchesHashEtag(
    filePath: string,
    headers: Pick<DownloadMetaEntry, 'etag' | 'lastModified' | 'contentLength'>
): boolean {
    const etagHash = hashFromEtag(headers.etag);
    return etagHash !== undefined && hashFile(filePath, etagHash.algorithm) === etagHash.value;
}

function localMatchesRemoteMetadata(
    filePath: string,
    headers: Pick<DownloadMetaEntry, 'etag' | 'lastModified' | 'contentLength'>
): boolean {
    if (!headers.lastModified || !headers.contentLength) {
        return false;
    }
    const stat = fs.statSync(filePath);
    const remoteTime = new Date(headers.lastModified).getTime();
    return Number.isFinite(remoteTime) &&
        stat.size === Number(headers.contentLength) &&
        Math.abs(stat.mtime.getTime() - remoteTime) < 1000;
}

const unihanExtractedFiles = [
    "Unihan_DictionaryIndices.txt",
    "Unihan_DictionaryLikeData.txt",
    "Unihan_IRGSources.txt",
    "Unihan_NumericValues.txt",
    "Unihan_OtherMappings.txt",
    "Unihan_RadicalStrokeCounts.txt",
    "Unihan_Readings.txt",
    "Unihan_Variants.txt"
];

function unihanExtractedFilesExist(): boolean {
    const unihanDir = path.join(ucdDir, 'unihan');
    return unihanExtractedFiles.every(file => fs.existsSync(path.join(unihanDir, file)));
}

const meta = readMeta();

// Download Worker
async function downloadWorker(task: DownloadTask): Promise<void> {
    if (!summary.byGroup[task.groupName]) {
        summary.byGroup[task.groupName] = { success: 0, failed: 0, skipped: 0 };
    }

    try {
        const key = metaKey(task);
        const entry = meta[key];
        const headRes = await fetch(task.url, { method: 'HEAD' });
        const headers = headRes.ok ? remoteHeaders(headRes) : {};
        const destExists = fs.existsSync(task.destPath);
        const canSkipRegularFile =
            destExists &&
            (
                (
                    entry?.url === task.url &&
                    sameRemote(entry, headers) &&
                    sha256File(task.destPath) === entry.sha256
                ) ||
                localMatchesHashEtag(task.destPath, headers) ||
                localMatchesRemoteMetadata(task.destPath, headers)
            );
        const canSkipUnihanZip =
            task.fileName === 'Unihan.zip' &&
            !destExists &&
            unihanExtractedFilesExist() &&
            entry?.url === task.url &&
            sameRemote(entry, headers);

        if (canSkipRegularFile || canSkipUnihanZip) {
            summary.skipped++;
            summary.byGroup[task.groupName].skipped++;
            console.log(`↷ Skipped: ${colors.blue}${task.fileName}${colors.reset} [ucd/${task.groupName}]`);
            return;
        }

        const res = await fetch(task.url);
        if (!res.ok) {
            throw new Error(`HTTP Error ${res.status}`);
        }
        const arrayBuffer = await res.arrayBuffer();
        fs.writeFileSync(task.destPath, Buffer.from(arrayBuffer));
        const downloadedHeaders = remoteHeaders(res);
        if (downloadedHeaders.lastModified) {
            const remoteTime = new Date(downloadedHeaders.lastModified);
            if (Number.isFinite(remoteTime.getTime())) {
                fs.utimesSync(task.destPath, new Date(), remoteTime);
            }
        }
        meta[key] = {
            url: task.url,
            ...downloadedHeaders,
            sha256: sha256File(task.destPath)
        };

        summary.success++;
        summary.byGroup[task.groupName].success++;
        console.log(`✅ Finished: ${colors.green}${task.fileName}${colors.reset} [ucd/${task.groupName}]`);
    } catch (err: unknown) {
        const message = err instanceof Error ? err.message : String(err);
        summary.failed++;
        summary.byGroup[task.groupName].failed++;
        console.error(`❌ Failed: ${colors.red}${task.fileName}${colors.reset} [ucd/${task.groupName}] - ${message}`);
    }
}

// Concurrency Pool Executor
async function runWithConcurrency(
    tasks: readonly DownloadTask[],
    concurrency: number,
    workerFn: (task: DownloadTask) => Promise<void>
): Promise<void> {
    let index = 0;
    const workers = Array.from({ length: Math.min(concurrency, tasks.length) }, async () => {
        while (index < tasks.length) {
            const currentIdx = index++;
            await workerFn(tasks[currentIdx]);
        }
    });
    await Promise.all(workers);
}

// Execution block
(async () => {
    const concurrencyLimit = 5;
    console.log(`${colors.cyan}🚀 Initiating download of ${tasks.length} files with concurrency pool of ${concurrencyLimit}...${colors.reset}\n`);

    await runWithConcurrency(tasks, concurrencyLimit, downloadWorker);
    writeMeta(meta);

    // Unzip Unihan database
    const unihanZipPath = path.join(ucdDir, 'unihan', 'Unihan.zip');
    const unihanDestDir = path.join(ucdDir, 'unihan');

    if (fs.existsSync(unihanZipPath)) {
        console.log(`\n${colors.cyan}🔓 Extracting Unihan Database...${colors.reset}`);
        try {
            execSync(`unzip -q -o "${unihanZipPath}" -d "${unihanDestDir}"`);
            fs.unlinkSync(unihanZipPath);
            summary.unihanExtracted = 8;
            console.log(`✅ Unihan Database extracted successfully.`);
        } catch (err: unknown) {
            const message = err instanceof Error ? err.message : String(err);
            console.warn(`\n${colors.yellow}⚠️ Warning: Failed to extract Unihan.zip. Error: ${message}${colors.reset}`);
        }
    }

    // Compile final total files downloaded
    const totalDownloaded = summary.success + (summary.unihanExtracted > 0 ? (summary.unihanExtracted - 1) : 0);

    console.log(`\n${colors.green}=========================================${colors.reset}`);
    console.log(`${colors.green}🎉 DOWNLOAD PROCESS COMPLETE!             ${colors.reset}`);
    console.log(`${colors.green}=========================================${colors.reset}`);
    console.log(`${colors.yellow}📊 Final Download Summary:${colors.reset}`);

    for (const [groupName, stats] of Object.entries(summary.byGroup)) {
        let detail = `${stats.success} files succeeded`;
        if (stats.skipped > 0) {
            detail += `, ${colors.blue}${stats.skipped} skipped${colors.reset}`;
        }
        if (stats.failed > 0) {
            detail += `, ${colors.red}${stats.failed} failed${colors.reset}`;
        }

        if (groupName === 'unihan' && summary.unihanExtracted > 0) {
            console.log(`  🔹 ucd/unihan (unzipped):   ${colors.yellow}8 files${colors.reset}`);
        } else {
            console.log(`  🔹 ucd/${groupName.padEnd(21)} ${colors.yellow}${detail}${colors.reset}`);
        }
    }

    console.log(`  -----------------------------------------`);
    console.log(`  🚀 ${colors.cyan}Total Output Files:${colors.reset}       ${colors.green}${totalDownloaded}${colors.reset}`);
    console.log(`  ↷ ${colors.cyan}Skipped Downloads:${colors.reset}    ${colors.green}${summary.skipped}${colors.reset}`);

    try {
        const diskSize = execSync(`du -sh "${dataDir}"`).toString().trim().split('\t')[0];
        console.log(`  📂 ${colors.cyan}Total Space Used:${colors.reset}         ${colors.green}${diskSize}${colors.reset}`);
    } catch {
        // Skip silently if the host platform lacks `du`
    }
    console.log(`${colors.green}=========================================${colors.reset}`);
})();
