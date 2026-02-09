export type NvsVersion = 1 | 2;

export type NvsValueType =
  | 'u8'
  | 'i8'
  | 'u16'
  | 'i16'
  | 'u32'
  | 'i32'
  | 'u64'
  | 'i64'
  | 'string'
  | 'blob'
  | 'float'
  | 'double'
  | 'bool'
  | 'any';

export type NvsDetectResult = { version: NvsVersion | 0; reason: string };

export type EntryStateLabel = 'EMPTY' | 'WRITTEN' | 'ERASED' | 'ILLEGAL';

export type NvsPageInfo = {
  index: number;
  state: string;
  seq: number | null;
  valid: boolean;
  errors: string[];
  entryStates?: EntryStateLabel[];
  entryCounts?: { written: number; erased: number; empty: number; illegal: number };
};

export type NvsNamespaceInfo = { id: number; name: string };

export type NvsEntryRawInfo = {
  pageIndex: number;
  entryIndex: number;
  spanCount: number;
  nsIndex: number;
  typeCode: number;
  chunkIndex?: number;
  declaredDataSize?: number;
  headerCrcOk?: boolean;
  itemCrcOk?: boolean;
  dataCrcOk?: boolean;
};

export type NvsEntryInfo = {
  namespace: string;
  key: string;
  type: NvsValueType;
  valuePreview: string;
  value?: number | string | Uint8Array;
  length?: number;
  crcOk?: boolean;

  // IMPORTANT: do NOT name this `raw` (Vuetify uses `.raw` for its internal wrapper)
  location?: NvsEntryRawInfo;

  warnings?: string[];
};

export type NvsParseResult = {
  version: NvsVersion;
  pages: NvsPageInfo[];
  namespaces: NvsNamespaceInfo[];
  entries: NvsEntryInfo[];
  warnings: string[];
  errors: string[];
};

const PAGE_SIZE = 0x1000;
const ENTRY_SIZE = 32;
const ENTRY_COUNT = 126;
const HEADER_SIZE = 32;
const ENTRY_TABLE_SIZE = 32;
const ENTRY_DATA_OFFSET = HEADER_SIZE + ENTRY_TABLE_SIZE;

const PAGE_STATE = {
  UNINITIALIZED: 0xffffffff,
  ACTIVE: 0xfffffffe,
  FULL: 0xfffffffc,
  FREEING: 0xfffffff8,
  CORRUPT: 0xfffffff0,
} as const;

const ITEM_TYPE = {
  U8: 0x01,
  I8: 0x11,
  U16: 0x02,
  I16: 0x12,
  U32: 0x04,
  I32: 0x14,
  U64: 0x08,
  I64: 0x18,
  SZ: 0x21,
  BLOB_LEGACY: 0x41,
  BLOB_DATA: 0x42,
  BLOB_IDX: 0x48,
  F32: 0x24,
  F64: 0x28,
  BOOL: 0x31,
  ANY: 0xff,
} as const;

const PAGE_STATE_LABELS: Record<number, string> = {
  [PAGE_STATE.UNINITIALIZED]: 'UNINITIALIZED',
  [PAGE_STATE.ACTIVE]: 'ACTIVE',
  [PAGE_STATE.FULL]: 'FULL',
  [PAGE_STATE.FREEING]: 'FREEING',
  [PAGE_STATE.CORRUPT]: 'CORRUPT',
};

const ENTRY_STATE_LABELS: Record<number, EntryStateLabel> = {
  0x3: 'EMPTY',
  0x2: 'WRITTEN',
  0x0: 'ERASED',
  0x1: 'ILLEGAL',
};

type Recency = { seq: number | null; pageIndex: number; entryIndex: number };

type ParsedItem = {
  pageIndex: number;
  entryIndex: number;
  spanCount: number;
  pageSeq: number | null;
  headerCrcOk: boolean | undefined;
  nsIndex: number;
  key: string;
  typeCode: number;
  chunkIndex: number | undefined;
  itemCrcOk: boolean | undefined;
  declaredDataSize: number | undefined;
  data: Uint8Array | undefined;
  dataCrcOk: boolean | undefined;
  warnings: string[];
};

type NamespaceRecord = { id: number; name: string; recency: Recency; warnings: string[] };

type BlobIndexRecord = {
  nsIndex: number;
  key: string;
  dataSize: number;
  chunkCount: number;
  chunkStart: number;
  recency: Recency;
  itemCrcOk: boolean | undefined;
  warnings: string[];
  raw: { pageIndex: number; entryIndex: number; spanCount: number; typeCode: number; chunkIndex: number };
};

type BlobChunkRecord = {
  nsIndex: number;
  key: string;
  chunkIndex: number;
  dataSize: number;
  data: Uint8Array;
  recency: Recency;
  crcOk: boolean | undefined;
  warnings: string[];
  raw: { pageIndex: number; entryIndex: number; spanCount: number; typeCode: number };
};

const CRC32_TABLE = (() => {
  const table = new Uint32Array(256);
  for (let i = 0; i < 256; i += 1) {
    let c = i;
    for (let k = 0; k < 8; k += 1) {
      c = (c & 1) ? (0xedb88320 ^ (c >>> 1)) : (c >>> 1);
    }
    table[i] = c >>> 0;
  }
  return table;
})();

const KEY_DECODER = new TextDecoder('utf-8');
let UTF8_FATAL_DECODER: TextDecoder | null = null;
try {
  UTF8_FATAL_DECODER = new TextDecoder('utf-8', { fatal: true });
} catch {
  UTF8_FATAL_DECODER = null;
}

function toHexByte(value: number) {
  return value.toString(16).padStart(2, '0');
}

function hexPreview(bytes: Uint8Array, maxBytes = 16) {
  const slice = bytes.subarray(0, Math.min(bytes.length, maxBytes));
  let out = '0x';
  for (const b of slice) out += toHexByte(b);
  if (bytes.length > slice.length) out += '…';
  return out;
}

function clampSpan(span: number, max: number) {
  if (!Number.isFinite(span) || span < 1) return 1;
  if (span > max) return max;
  return span;
}

function compareRecency(a: Recency, b: Recency) {
  const aSeq = a.seq ?? -1;
  const bSeq = b.seq ?? -1;
  if (aSeq !== bSeq) return aSeq - bSeq;
  if (a.pageIndex !== b.pageIndex) return a.pageIndex - b.pageIndex;
  return a.entryIndex - b.entryIndex;
}

function isVariableLengthType(typeCode: number, version: NvsVersion) {
  if (typeCode === ITEM_TYPE.SZ) return true;
  if (version === 1) return typeCode === ITEM_TYPE.BLOB_LEGACY;
  // v2: variable-length payloads live in BLOB_DATA entries (and SZ)
  return typeCode === ITEM_TYPE.BLOB_DATA;
}

function mapTypeCodeToValueType(typeCode: number, version: NvsVersion): NvsValueType {
  switch (typeCode) {
    case ITEM_TYPE.U8:
      return 'u8';
    case ITEM_TYPE.I8:
      return 'i8';
    case ITEM_TYPE.U16:
      return 'u16';
    case ITEM_TYPE.I16:
      return 'i16';
    case ITEM_TYPE.U32:
      return 'u32';
    case ITEM_TYPE.I32:
      return 'i32';
    case ITEM_TYPE.U64:
      return 'u64';
    case ITEM_TYPE.I64:
      return 'i64';
    case ITEM_TYPE.F32:
      return 'float';
    case ITEM_TYPE.F64:
      return 'double';
    case ITEM_TYPE.BOOL:
      return 'bool';
    case ITEM_TYPE.SZ:
      return 'string';
    case ITEM_TYPE.BLOB_LEGACY:
      return 'blob';
    case ITEM_TYPE.BLOB_DATA:
      return version === 2 ? 'blob' : 'any';
    case ITEM_TYPE.ANY:
      return 'any';
    default:
      return 'any';
  }
}

function decodeKey(rawKey: Uint8Array) {
  let end = rawKey.indexOf(0x00);
  if (end === -1) {
    end = rawKey.length;
    for (let i = rawKey.length - 1; i >= 0; i -= 1) {
      if (rawKey[i] !== 0xff) {
        end = i + 1;
        break;
      }
    }
  }
  if (end <= 0) return '';
  return KEY_DECODER.decode(rawKey.subarray(0, end)).trim();
}

function stringifyPreview(text: string, maxLen = 80) {
  const compact = text.replace(/\s+/g, ' ').trim();
  if (compact.length <= maxLen) return JSON.stringify(compact);
  return JSON.stringify(compact.slice(0, maxLen - 1) + '…');
}

function pageStateLabel(state: number) {
  return PAGE_STATE_LABELS[state] ?? `0x${state.toString(16)}`;
}

function readUint32Le(view: DataView, offset: number) {
  return view.getUint32(offset, true) >>> 0;
}

function detectNvsVersionFromPages(data: Uint8Array) {
  if (data.length < HEADER_SIZE) {
    return { version: 0 as const, reason: `Too small (${data.length} bytes) to contain an NVS page header.` };
  }

  const pageCount = Math.ceil(data.length / PAGE_SIZE);
  let v1 = 0;
  let v2 = 0;
  let validHeaders = 0;
  let checkedPages = 0;

  for (let pageIndex = 0; pageIndex < pageCount && checkedPages < 16; pageIndex += 1) {
    const pageStart = pageIndex * PAGE_SIZE;
    const page = data.subarray(pageStart, Math.min(pageStart + PAGE_SIZE, data.length));
    if (page.length < HEADER_SIZE) continue;

    const view = new DataView(page.buffer, page.byteOffset, page.byteLength);
    const state = readUint32Le(view, 0);
    const versionByte = view.getUint8(8);

    // Skip blank pages entirely (do not count them)
    if (state === PAGE_STATE.UNINITIALIZED) {
      continue;
    }

    // Only count real pages
    checkedPages += 1;


    const stored = readUint32Le(view, 28);
    const calc = nvsCrc32(page, 4, 24);
    if (stored !== calc) continue;
    validHeaders += 1;

    if (versionByte === 0xff) v1 += 1;
    else if (versionByte === 0xfe) v2 += 1;
  }

  if (!validHeaders) {
    return { version: 0 as const, reason: 'No valid NVS page headers found (CRC mismatch or truncated data).' };
  }
  if (v2 && !v1) {
    return { version: 2 as const, reason: `Found ${v2} valid page header(s) with format version 0xFE.` };
  }
  if (v1 && !v2) {
    return { version: 1 as const, reason: `Found ${v1} valid page header(s) with format version 0xFF.` };
  }
  if (v2 >= v1) {
    return { version: 2 as const, reason: `Mixed page versions (0xFE:${v2}, 0xFF:${v1}); choosing v2.` };
  }
  return { version: 1 as const, reason: `Mixed page versions (0xFF:${v1}, 0xFE:${v2}); choosing v1.` };
}

export function detectNvsVersion(data: Uint8Array): NvsDetectResult {
  return detectNvsVersionFromPages(data);
}

function crc32Update(crc: number, data: Uint8Array, start = 0, length = data.length - start) {
  let c = crc >>> 0;
  const end = Math.min(data.length, start + length);
  for (let i = start; i < end; i += 1) {
    c = CRC32_TABLE[(c ^ data[i]) & 0xff] ^ (c >>> 8);
  }
  return c >>> 0;
}

// ESP-IDF NVS uses `esp_crc32_le(0xffffffff, ...)` and stores the running value (no final XOR).
function nvsCrc32(data: Uint8Array, start = 0, length = data.length - start) {
  const running = crc32Update(0x00000000, data, start, length);
  return (running ^ 0xffffffff) >>> 0;
}


function computeItemCrc32(itemBytes: Uint8Array) {
  let crc = 0x00000000;
  crc = crc32Update(crc, itemBytes, 0, 4);
  crc = crc32Update(crc, itemBytes, 8, 16);
  crc = crc32Update(crc, itemBytes, 24, 8);
  return (crc ^ 0xffffffff) >>> 0;
}


function combineCrcOk(itemCrcOk: boolean | undefined, dataCrcOk: boolean | undefined) {
  if (itemCrcOk === false || dataCrcOk === false) return false;
  if (itemCrcOk === true && dataCrcOk === true) return true;
  if (itemCrcOk === true && dataCrcOk === undefined) return undefined;
  if (itemCrcOk === undefined && dataCrcOk === true) return undefined;
  return undefined;
}

function decodeStringValue(bytes: Uint8Array): { ok: boolean; text: string } {
  if (!UTF8_FATAL_DECODER) {
    return { ok: true, text: KEY_DECODER.decode(bytes) };
  }
  try {
    return { ok: true, text: UTF8_FATAL_DECODER.decode(bytes) };
  } catch {
    return { ok: false, text: KEY_DECODER.decode(bytes) };
  }
}

function parseWithVersion(data: Uint8Array, version: NvsVersion): NvsParseResult {
  const warnings: string[] = [];
  const errors: string[] = [];
  const pages: NvsPageInfo[] = [];

  const namespaceRecords = new Map<number, NamespaceRecord>();
  const parsedItems: ParsedItem[] = [];
  const blobIndexes: BlobIndexRecord[] = [];
  const blobChunks = new Map<string, BlobChunkRecord>();

  const pageCount = Math.ceil(data.length / PAGE_SIZE);
  if (!pageCount) {
    errors.push('Empty input buffer.');
    return { version, pages, namespaces: [], entries: [], warnings, errors };
  }
  if (data.length % PAGE_SIZE !== 0) {
    warnings.push(`Input length (${data.length} bytes) is not a multiple of 0x1000; parsing last page as truncated.`);
  }

  for (let pageIndex = 0; pageIndex < pageCount; pageIndex += 1) {
    const pageStart = pageIndex * PAGE_SIZE;
    const page = data.subarray(pageStart, Math.min(pageStart + PAGE_SIZE, data.length));
    const pageErrors: string[] = [];
    let seq: number | null = null;
    let headerCrcOk: boolean | undefined;

    if (page.length < HEADER_SIZE) {
      pageErrors.push(`Truncated page header (${page.length} bytes).`);
      pages.push({ index: pageIndex, state: 'TRUNCATED', seq: null, valid: false, errors: pageErrors });
      continue;
    }

    const view = new DataView(page.buffer, page.byteOffset, page.byteLength);
    const state = readUint32Le(view, 0);
    seq = readUint32Le(view, 4);
    const versionByte = view.getUint8(8);
    const storedHeaderCrc = readUint32Le(view, 28);
    const calcHeaderCrc = nvsCrc32(page, 4, 24);
    if (pageIndex === 0) {
      const a = crc32Update(0x00000000, page, 4, 24) >>> 0;
      const b = (a ^ 0xffffffff) >>> 0;

      const c = crc32Update(0xffffffff, page, 4, 24) >>> 0;
      const d = (c ^ 0xffffffff) >>> 0;

      console.debug(
        `[NVS CRC VARIANTS] page=${pageIndex}`,
        `stored=0x${storedHeaderCrc.toString(16)}`,
        `init0=0x${a.toString(16)}`,
        `init0^final=0x${b.toString(16)}`,
        `initFF=0x${c.toString(16)}`,
        `initFF^final=0x${d.toString(16)}`,
      );
    }


    if (state === PAGE_STATE.UNINITIALIZED) {
      headerCrcOk = true;
      if (page.some(b => b !== 0xff)) {
        pageErrors.push('Page header is UNINITIALIZED but the page is not blank; page may be corrupt.');
      }
    } else if (storedHeaderCrc !== calcHeaderCrc) {
      headerCrcOk = false;
      pageErrors.push(
        `Header CRC mismatch (stored 0x${storedHeaderCrc.toString(16)}, calc 0x${calcHeaderCrc.toString(16)}).`,
      );
    } else {
      headerCrcOk = true;
    }

    if (state !== PAGE_STATE.UNINITIALIZED) {
      if (version === 1 && versionByte !== 0xff) {
        pageErrors.push(`Unexpected page format version 0x${versionByte.toString(16)} (expected 0xFF for v1).`);
      }
      if (version === 2 && versionByte === 0xff) {
        pageErrors.push('Page format version is 0xFF (looks like NVS v1) but parsing as v2.');
      }
    }

    pages.push({
      index: pageIndex,
      state: pageStateLabel(state),
      seq,
      valid: Boolean(headerCrcOk),
      errors: pageErrors,
    });

    if (headerCrcOk === false) {
      // page is corrupt; don't trust its entry table or items
      continue;
    }
    if (page.length < ENTRY_DATA_OFFSET) {
      continue;
    }

    const entryTableWords: number[] = [];
    for (let w = 0; w < 8; w += 1) {
      const wordOffset = HEADER_SIZE + w * 4;
      if (wordOffset + 4 > page.length) break;
      entryTableWords.push(readUint32Le(view, wordOffset));
    }
    if (entryTableWords.length < 8) {
      warnings.push(`Page ${pageIndex}: truncated entry table.`);
      continue;
    }

    const entryStates: EntryStateLabel[] = new Array(ENTRY_COUNT);
    const entryCounts = { written: 0, erased: 0, empty: 0, illegal: 0 };
    for (let entryIndex = 0; entryIndex < ENTRY_COUNT; entryIndex += 1) {
      const wordIndex = entryIndex >> 4; // 16 entries per u32 word
      const bitOffset = (entryIndex & 0x0f) * 2;
      const stateBits = (entryTableWords[wordIndex] >>> bitOffset) & 0x3;
      const entryState = ENTRY_STATE_LABELS[stateBits] ?? 'ILLEGAL';
      entryStates[entryIndex] = entryState;
      if (entryState === 'WRITTEN') {
        entryCounts.written += 1;
      } else if (entryState === 'ERASED') {
        entryCounts.erased += 1;
      } else if (entryState === 'EMPTY') {
        entryCounts.empty += 1;
      } else {
        entryCounts.illegal += 1;
      }
    }

    const pageInfo = pages[pages.length - 1];
    pageInfo.entryStates = entryStates;
    pageInfo.entryCounts = entryCounts;

    let skipRemaining = 0;
    for (let entryIndex = 0; entryIndex < ENTRY_COUNT; entryIndex += 1) {
      const entryOffset = ENTRY_DATA_OFFSET + entryIndex * ENTRY_SIZE;
      if (entryOffset + ENTRY_SIZE > page.length) {
        if (entryOffset < page.length) {
          warnings.push(`Page ${pageIndex}: truncated entry data at entry ${entryIndex}.`);
        }
        break;
      }

      const entryState = entryStates[entryIndex];
      if (entryState !== 'WRITTEN') continue;

      if (skipRemaining > 0) {
        skipRemaining -= 1;
        continue;
      }

      const itemBytes = page.subarray(entryOffset, entryOffset + ENTRY_SIZE);
      const itemView = new DataView(itemBytes.buffer, itemBytes.byteOffset, itemBytes.byteLength);
      const nsIndex = itemView.getUint8(0);
      const typeCode = itemView.getUint8(1);
      const spanRaw = itemView.getUint8(2);
      const chunkIndex = version === 2 ? itemView.getUint8(3) : undefined;
      const storedItemCrc = readUint32Le(itemView, 4);
      const calcItemCrc = computeItemCrc32(itemBytes);
      const itemCrcOk = storedItemCrc === calcItemCrc;
      const key = decodeKey(itemBytes.subarray(8, 24));

      const warningsForItem: string[] = [];
      if (!key) {
        warningsForItem.push('Empty key decoded; skipping entry.');
        continue;
      }
      if (!itemCrcOk) {
        warningsForItem.push(
          `Item CRC mismatch (stored 0x${storedItemCrc.toString(16)}, calc 0x${calcItemCrc.toString(16)}).`,
        );
      }

      const spanCount = clampSpan(spanRaw, ENTRY_COUNT - entryIndex);
      if (spanCount !== spanRaw) {
        warningsForItem.push(`Invalid span ${spanRaw}; clamped to ${spanCount}.`);
      }

      if (version === 1) {
        const reserved = itemView.getUint8(3);
        if (reserved !== 0xff) {
          warningsForItem.push(`Unexpected reserved byte 0x${reserved.toString(16)} (expected 0xFF for v1).`);
        }
      }

      let declaredDataSize: number | undefined;
      let data: Uint8Array | undefined;
      let dataCrcOk: boolean | undefined;

      if (isVariableLengthType(typeCode, version)) {
        declaredDataSize = itemView.getUint16(24, true);
        const storedDataCrc = readUint32Le(itemView, 28);
        const availablePayloadBytes = (spanCount - 1) * ENTRY_SIZE;
        if (spanCount === 1) {
          warningsForItem.push('Variable-length type with span=1 (no payload entries).');
        }
        if (declaredDataSize > availablePayloadBytes) {
          warningsForItem.push(
            `Declared dataSize ${declaredDataSize} exceeds span payload capacity ${availablePayloadBytes}; clamping.`,
          );
          declaredDataSize = availablePayloadBytes;
        }

        const out = new Uint8Array(declaredDataSize);
        let written = 0;
        let truncated = false;
        for (let rel = 1; rel < spanCount && written < declaredDataSize; rel += 1) {
          const dataEntryOffset = ENTRY_DATA_OFFSET + (entryIndex + rel) * ENTRY_SIZE;
          if (dataEntryOffset + ENTRY_SIZE > page.length) {
            truncated = true;
            break;
          }
          const chunk = page.subarray(dataEntryOffset, dataEntryOffset + ENTRY_SIZE);
          const toCopy = Math.min(chunk.length, declaredDataSize - written);
          out.set(chunk.subarray(0, toCopy), written);
          written += toCopy;
        }
        data = out;
        skipRemaining = spanCount - 1;

        if (written < declaredDataSize) {
          truncated = true;
          warningsForItem.push(`Truncated payload (${written}/${declaredDataSize} bytes available).`);
        }

        if (!truncated) {
          const calcDataCrc = nvsCrc32(data);
          dataCrcOk = calcDataCrc === storedDataCrc;
          if (!dataCrcOk) {
            warningsForItem.push(
              `Payload CRC mismatch (stored 0x${storedDataCrc.toString(16)}, calc 0x${calcDataCrc.toString(16)}).`,
            );
          }
        } else {
          dataCrcOk = undefined;
        }
      }

      if (version === 2 && typeCode === ITEM_TYPE.BLOB_IDX) {
        const blobDataSize = readUint32Le(itemView, 24);
        const blobChunkCount = itemView.getUint8(28);
        const blobChunkStart = itemView.getUint8(29);
        blobIndexes.push({
          nsIndex,
          key,
          dataSize: blobDataSize,
          chunkCount: blobChunkCount,
          chunkStart: blobChunkStart,
          recency: { seq, pageIndex, entryIndex },
          itemCrcOk: itemCrcOk ? true : false,
          warnings: warningsForItem,
          raw: { pageIndex, entryIndex, spanCount, typeCode, chunkIndex: chunkIndex ?? 0xff },
        });
      } else if (version === 2 && typeCode === ITEM_TYPE.BLOB_DATA && data) {
        const chunkKey = `${nsIndex}|${key}|${chunkIndex ?? 0}`;
        const existing = blobChunks.get(chunkKey);
        const record: BlobChunkRecord = {
          nsIndex,
          key,
          chunkIndex: chunkIndex ?? 0,
          dataSize: declaredDataSize ?? data.length,
          data,
          recency: { seq, pageIndex, entryIndex },
          crcOk: itemCrcOk && dataCrcOk ? true : itemCrcOk === false || dataCrcOk === false ? false : undefined,
          warnings: warningsForItem,
          raw: { pageIndex, entryIndex, spanCount, typeCode },
        };
        if (!existing || compareRecency(existing.recency, record.recency) < 0) {
          blobChunks.set(chunkKey, record);
        }
      } else if (nsIndex === 0 && typeCode === ITEM_TYPE.U8) {
        const namespaceId = itemView.getUint8(24);
        if (namespaceId === 0 || namespaceId === 255) {
          warningsForItem.push(`Namespace id ${namespaceId} is reserved.`);
        }
        const recency = { seq, pageIndex, entryIndex };
        const existing = namespaceRecords.get(namespaceId);
        const record: NamespaceRecord = {
          id: namespaceId,
          name: key || `ns_${namespaceId}`,
          recency,
          warnings: warningsForItem,
        };
        if (!existing || compareRecency(existing.recency, recency) < 0) {
          namespaceRecords.set(namespaceId, record);
        }
      } else {
        parsedItems.push({
          pageIndex,
          entryIndex,
          spanCount,
          pageSeq: seq,
          headerCrcOk,
          nsIndex,
          key,
          typeCode,
          chunkIndex,
          itemCrcOk: itemCrcOk ? true : false,
          declaredDataSize,
          data,
          dataCrcOk,
          warnings: warningsForItem,
        });
      }
    }
  }

  const namespaces = [...namespaceRecords.values()]
    .sort((a, b) => a.id - b.id)
    .map(record => ({ id: record.id, name: record.name }));
  const namespaceNameById = new Map<number, string>();
  for (const ns of namespaces) namespaceNameById.set(ns.id, ns.name);

  const consumedBlobChunks = new Set<string>();
  const blobEntries: NvsEntryInfo[] = [];
  if (version === 2 && blobIndexes.length) {
    const indexByKey = new Map<string, BlobIndexRecord>();
    for (const idx of blobIndexes) {
      const k = `${idx.nsIndex}|${idx.key}`;
      const existing = indexByKey.get(k);
      if (!existing || compareRecency(existing.recency, idx.recency) < 0) {
        indexByKey.set(k, idx);
      }
    }

    for (const idx of indexByKey.values()) {
      const warningsForEntry = [...idx.warnings];
      const assembledChunks: Uint8Array[] = [];
      let assembledSize = 0;
      let allCrcOk = idx.itemCrcOk;

      for (let i = 0; i < idx.chunkCount; i += 1) {
        const chunkIndex = (idx.chunkStart + i) & 0xff;
        const chunkKey = `${idx.nsIndex}|${idx.key}|${chunkIndex}`;
        const chunk = blobChunks.get(chunkKey);
        if (!chunk) {
          warningsForEntry.push(
            `Missing blob chunk ${i + 1}/${idx.chunkCount} (chunkIndex=0x${chunkIndex.toString(16)}).`,
          );
          allCrcOk = false;
          continue;
        }
        consumedBlobChunks.add(chunkKey);
        assembledChunks.push(chunk.data);
        assembledSize += chunk.data.length;
        if (chunk.crcOk === false) allCrcOk = false;
      }

      let blobData = new Uint8Array(0);
      if (assembledChunks.length) {
        blobData = new Uint8Array(assembledSize);
        let offset = 0;
        for (const c of assembledChunks) {
          blobData.set(c, offset);
          offset += c.length;
        }
      }

      if (blobData.length < idx.dataSize) {
        warningsForEntry.push(`Assembled blob shorter than index size (${blobData.length}/${idx.dataSize} bytes).`);
      } else if (blobData.length > idx.dataSize) {
        blobData = blobData.subarray(0, idx.dataSize);
      }

      const namespace = namespaceNameById.get(idx.nsIndex) ?? `namespace#${idx.nsIndex}`;

      // Heuristic decode for floats/doubles stored via Preferences as blob(4/8)
      const k = (idx.key ?? '').toLowerCase();
      const looksF32 = k.includes('f32') || k.includes('float');
      const looksF64 = k.includes('f64') || k.includes('double');

      if (idx.dataSize === 4 && blobData.length >= 4 && looksF32) {
        const dv = new DataView(blobData.buffer, blobData.byteOffset, blobData.byteLength);
        const f = dv.getFloat32(0, true);
        blobEntries.push({
          namespace,
          key: idx.key,
          type: 'float',
          valuePreview: `${f}`,
          value: f,
          length: idx.dataSize,
          crcOk: allCrcOk,
          location: {
            pageIndex: idx.raw.pageIndex,
            entryIndex: idx.raw.entryIndex,
            spanCount: idx.raw.spanCount,
            nsIndex: idx.nsIndex,
            typeCode: idx.raw.typeCode,
            chunkIndex: idx.raw.chunkIndex,
            declaredDataSize: idx.dataSize,
            itemCrcOk: idx.itemCrcOk,
          },
          warnings: warningsForEntry.length ? warningsForEntry : undefined,
        });
        continue;
      }

      if (idx.dataSize === 8 && blobData.length >= 8 && looksF64) {
        const dv = new DataView(blobData.buffer, blobData.byteOffset, blobData.byteLength);
        const d = dv.getFloat64(0, true);
        blobEntries.push({
          namespace,
          key: idx.key,
          type: 'double',
          valuePreview: `${d}`,
          value: d,
          length: idx.dataSize,
          crcOk: allCrcOk,
          location: {
            pageIndex: idx.raw.pageIndex,
            entryIndex: idx.raw.entryIndex,
            spanCount: idx.raw.spanCount,
            nsIndex: idx.nsIndex,
            typeCode: idx.raw.typeCode,
            chunkIndex: idx.raw.chunkIndex,
            declaredDataSize: idx.dataSize,
            itemCrcOk: idx.itemCrcOk,
          },
          warnings: warningsForEntry.length ? warningsForEntry : undefined,
        });
        continue;
      }

      // default: normal blob entry
      const valuePreview = `blob[${idx.dataSize}] ${hexPreview(blobData)}`;
      blobEntries.push({
        namespace,
        key: idx.key,
        type: 'blob',
        valuePreview,
        value: blobData,
        length: idx.dataSize,
        crcOk: allCrcOk,
        location: {
          pageIndex: idx.raw.pageIndex,
          entryIndex: idx.raw.entryIndex,
          spanCount: idx.raw.spanCount,
          nsIndex: idx.nsIndex,
          typeCode: idx.raw.typeCode,
          chunkIndex: idx.raw.chunkIndex,
          declaredDataSize: idx.dataSize,
          itemCrcOk: idx.itemCrcOk,
        },
        warnings: warningsForEntry.length ? warningsForEntry : undefined,
      });
    }
  }

  const entries: NvsEntryInfo[] = [];
  for (const item of parsedItems) {
    const itemWarnings = [...(item.warnings || [])];
    const namespace =
      namespaceNameById.get(item.nsIndex) ?? (item.nsIndex === 0 ? 'namespace#0' : `namespace#${item.nsIndex}`);
    const key = item.key || '(empty)';
    const valueType = mapTypeCodeToValueType(item.typeCode, version);

    if (version === 2 && item.typeCode === ITEM_TYPE.BLOB_DATA) {
      const chunkKey = `${item.nsIndex}|${item.key}|${item.chunkIndex ?? 0}`;
      if (consumedBlobChunks.has(chunkKey)) {
        continue;
      }
      itemWarnings.push('Orphan BLOB_DATA chunk (no matching BLOB_IDX found).');
    }

    const location: NvsEntryRawInfo = {
      pageIndex: item.pageIndex,
      entryIndex: item.entryIndex,
      spanCount: item.spanCount,
      nsIndex: item.nsIndex,
      typeCode: item.typeCode,
      headerCrcOk: item.headerCrcOk,
      itemCrcOk: item.itemCrcOk,
      dataCrcOk: item.dataCrcOk,
    };
    if (typeof item.chunkIndex === 'number') location.chunkIndex = item.chunkIndex;
    if (typeof item.declaredDataSize === 'number') location.declaredDataSize = item.declaredDataSize;

    if (valueType === 'string' && item.data) {
      const data = item.data;
      const trimmed = data.length && data[data.length - 1] === 0x00 ? data.subarray(0, data.length - 1) : data;
      const decoded = decodeStringValue(trimmed);
      let value: string | Uint8Array;
      let valuePreview: string;
      if (decoded.ok) {
        value = decoded.text;
        valuePreview = stringifyPreview(decoded.text);
      } else {
        value = data;
        valuePreview = `string[${data.length}] ${hexPreview(data)}`;
        itemWarnings.push('Invalid UTF-8 string; showing hex preview.');
      }
      entries.push({
        namespace,
        key,
        type: 'string',
        valuePreview,
        value,
        length: item.declaredDataSize ?? data.length,
        crcOk: combineCrcOk(item.itemCrcOk, item.dataCrcOk),
        location,
        warnings: itemWarnings.length ? itemWarnings : undefined,
      });
      continue;
    }

    if (valueType === 'blob' && item.data) {
      const data = item.data;

      // Use declared size when present (NVS spans can allocate more than the declared payload)
      const declaredLen = typeof item.declaredDataSize === 'number' ? item.declaredDataSize : data.length;
      const payload = data.subarray(0, Math.min(declaredLen, data.length));

      // Heuristic decode: Arduino Preferences stores float/double as raw bytes (blobs)
      // Gate it by key name to avoid converting random 4/8-byte blobs.
      const k = (key ?? '').toLowerCase();
      const looksF32 = k.includes('f32') || k.includes('float');
      const looksF64 = k.includes('f64') || k.includes('double');

      if (payload.length === 4 && looksF32) {
        const dv = new DataView(payload.buffer, payload.byteOffset, payload.byteLength);
        const f = dv.getFloat32(0, true);
        entries.push({
          namespace,
          key,
          type: 'float',
          valuePreview: `${f}`,
          value: f,
          length: declaredLen,
          crcOk: combineCrcOk(item.itemCrcOk, item.dataCrcOk),
          location,
          warnings: itemWarnings.length ? itemWarnings : undefined,
        });
        continue;
      }

      if (payload.length === 8 && looksF64) {
        const dv = new DataView(payload.buffer, payload.byteOffset, payload.byteLength);
        const d = dv.getFloat64(0, true);
        entries.push({
          namespace,
          key,
          type: 'double',
          valuePreview: `${d}`,
          value: d,
          length: declaredLen,
          crcOk: combineCrcOk(item.itemCrcOk, item.dataCrcOk),
          location,
          warnings: itemWarnings.length ? itemWarnings : undefined,
        });
        continue;
      }

      // fallback: normal blob
      entries.push({
        namespace,
        key,
        type: 'blob',
        valuePreview: `blob[${declaredLen}] ${hexPreview(payload)}`,
        value: payload,
        length: declaredLen,
        crcOk: combineCrcOk(item.itemCrcOk, item.dataCrcOk),
        location,
        warnings: itemWarnings.length ? itemWarnings : undefined,
      });
      continue;
    }


    const itemBytesOffset = item.pageIndex * PAGE_SIZE + ENTRY_DATA_OFFSET + item.entryIndex * ENTRY_SIZE;
    if (itemBytesOffset + ENTRY_SIZE > data.length) {
      entries.push({
        namespace,
        key,
        type: valueType,
        valuePreview: '(truncated)',
        location,
        warnings: [...itemWarnings, 'Truncated item bytes.'],
      });
      continue;
    }

    const itemBytes = data.subarray(itemBytesOffset, itemBytesOffset + ENTRY_SIZE);
    const itemView = new DataView(itemBytes.buffer, itemBytes.byteOffset, itemBytes.byteLength);
    const valueBytes = itemBytes.subarray(24, 32);

    const toNumberPreview = (val: number) => `${val}`;

    if (valueType === 'bool') {
      const v = valueBytes[0] !== 0;
      entries.push({ namespace, key, type: 'bool', valuePreview: v ? 'true' : 'false', value: v ? 1 : 0, crcOk: item.itemCrcOk, location, warnings: itemWarnings.length ? itemWarnings : undefined });
      continue;
    }

    if (valueType === 'float') {
      const v = itemView.getFloat32(24, true);
      entries.push({ namespace, key, type: 'float', valuePreview: `${v}`, value: v, crcOk: item.itemCrcOk, location, warnings: itemWarnings.length ? itemWarnings : undefined });
      continue;
    }

    if (valueType === 'double') {
      const v = itemView.getFloat64(24, true);
      entries.push({ namespace, key, type: 'double', valuePreview: `${v}`, value: v, crcOk: item.itemCrcOk, location, warnings: itemWarnings.length ? itemWarnings : undefined });
      continue;
    }

    if (valueType === 'u8') {
      const v = valueBytes[0];
      entries.push({
        namespace,
        key,
        type: 'u8',
        valuePreview: toNumberPreview(v),
        value: v,
        crcOk: item.itemCrcOk,
        location,
        warnings: itemWarnings.length ? itemWarnings : undefined,
      });
      continue;
    }
    if (valueType === 'i8') {
      const v = (valueBytes[0] << 24) >> 24;
      entries.push({
        namespace,
        key,
        type: 'i8',
        valuePreview: toNumberPreview(v),
        value: v,
        crcOk: item.itemCrcOk,
        location,
        warnings: itemWarnings.length ? itemWarnings : undefined,
      });
      continue;
    }
    if (valueType === 'u16') {
      const v = itemView.getUint16(24, true);
      entries.push({
        namespace,
        key,
        type: 'u16',
        valuePreview: toNumberPreview(v),
        value: v,
        crcOk: item.itemCrcOk,
        location,
        warnings: itemWarnings.length ? itemWarnings : undefined,
      });
      continue;
    }
    if (valueType === 'i16') {
      const v = itemView.getInt16(24, true);
      entries.push({
        namespace,
        key,
        type: 'i16',
        valuePreview: toNumberPreview(v),
        value: v,
        crcOk: item.itemCrcOk,
        location,
        warnings: itemWarnings.length ? itemWarnings : undefined,
      });
      continue;
    }
    if (valueType === 'u32') {
      const v = itemView.getUint32(24, true) >>> 0;
      entries.push({
        namespace,
        key,
        type: 'u32',
        valuePreview: toNumberPreview(v),
        value: v,
        crcOk: item.itemCrcOk,
        location,
        warnings: itemWarnings.length ? itemWarnings : undefined,
      });
      continue;
    }
    if (valueType === 'i32') {
      const v = itemView.getInt32(24, true);
      entries.push({
        namespace,
        key,
        type: 'i32',
        valuePreview: toNumberPreview(v),
        value: v,
        crcOk: item.itemCrcOk,
        location,
        warnings: itemWarnings.length ? itemWarnings : undefined,
      });
      continue;
    }
    if (valueType === 'u64') {
      let asString: string;
      try {
        const v = itemView.getBigUint64(24, true);
        asString = v.toString(10);
      } catch {
        const lo = itemView.getUint32(24, true) >>> 0;
        const hi = itemView.getUint32(28, true) >>> 0;
        asString = `0x${hi.toString(16).padStart(8, '0')}${lo.toString(16).padStart(8, '0')}`;
        itemWarnings.push('BigInt unavailable; showing hex for u64.');
      }
      entries.push({
        namespace,
        key,
        type: 'u64',
        valuePreview: asString,
        value: asString,
        crcOk: item.itemCrcOk,
        location,
        warnings: itemWarnings.length ? itemWarnings : undefined,
      });
      continue;
    }
    if (valueType === 'i64') {
      let asString: string;
      try {
        const v = itemView.getBigInt64(24, true);
        asString = v.toString(10);
      } catch {
        const lo = itemView.getUint32(24, true) >>> 0;
        const hi = itemView.getInt32(28, true);
        asString = `0x${(hi >>> 0).toString(16).padStart(8, '0')}${lo.toString(16).padStart(8, '0')}`;
        itemWarnings.push('BigInt unavailable; showing hex for i64.');
      }
      entries.push({
        namespace,
        key,
        type: 'i64',
        valuePreview: asString,
        value: asString,
        crcOk: item.itemCrcOk,
        location,
        warnings: itemWarnings.length ? itemWarnings : undefined,
      });
      continue;
    }

    entries.push({
      namespace,
      key,
      type: 'any',
      valuePreview: `type 0x${item.typeCode.toString(16)} ${hexPreview(valueBytes)}`,
      location,
      warnings: itemWarnings.length ? itemWarnings : undefined,
    });
  }

  entries.push(...blobEntries);

  entries.sort((a, b) => {
    const ns = a.namespace.localeCompare(b.namespace);
    if (ns !== 0) return ns;
    const k = a.key.localeCompare(b.key);
    if (k !== 0) return k;
    return a.type.localeCompare(b.type);
  });

  for (const p of pages) {
    if (p.errors?.length) {
      for (const err of p.errors) errors.push(`Page ${p.index}: ${err}`);
    }
  }

  return { version, pages, namespaces, entries, warnings, errors };
}

export function parseNvsPartition(data: Uint8Array): NvsParseResult {
  const detected = detectNvsVersion(data);

  if (detected.version === 1 || detected.version === 2) {
    const result = parseWithVersion(data, detected.version);

    if (detected.reason.startsWith('Mixed page versions')) {
      result.warnings.unshift(detected.reason);
    }

    return result;
  }

  // detection failed → heuristic fallback
  const v2 = parseWithVersion(data, 2);
  const v1 = parseWithVersion(data, 1);

  const score = (res: NvsParseResult) =>
    res.entries.length * 2 + res.namespaces.length - res.errors.length * 3;

  const chosen = score(v2) >= score(v1) ? v2 : v1;
  chosen.warnings.unshift(
    `NVS version detection failed: ${detected.reason} (heuristic parse picked v${chosen.version}).`,
  );

  return chosen;
}

