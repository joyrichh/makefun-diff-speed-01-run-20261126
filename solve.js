const FORMAT = 'makefun-diff/1';
const CONTEXT = 3;
const KEEP = 0;
const DELETE = 1;
const INSERT = 2;
const INVALID = -2;

function tokenize(text, intern, lineValues) {
  const parts = text.split('\n');
  const last = parts.length - 1;
  const length = last + (parts[last] === '' ? 0 : 1);
  const ids = new Int32Array(length);
  for (let index = 0; index < last; index++) {
    const line = parts[index] + '\n';
    let id = intern.get(line);
    if (id === undefined) {
      id = lineValues.length;
      intern.set(line, id);
      lineValues.push(line);
    }
    ids[index] = id;
  }
  if (parts[last] !== '') {
    const line = parts[last];
    let id = intern.get(line);
    if (id === undefined) {
      id = lineValues.length;
      intern.set(line, id);
      lineValues.push(line);
    }
    ids[last] = id;
  }
  return ids;
}

function appendRun(kinds, counts, length, kind, count) {
  if (count === 0) return length;
  if (length > 0 && kinds[length - 1] === kind) {
    counts[length - 1] += count;
    return length;
  }
  kinds[length] = kind;
  counts[length] = count;
  return length + 1;
}

export function run(input) {
  if (input === null || typeof input !== 'object' || typeof input.old !== 'string' || typeof input.new !== 'string') {
    throw new TypeError('makefun-diff: the input is { old, new }, two strings');
  }

  const intern = new Map();
  const lineValues = [];
  const oldIds = tokenize(input.old, intern, lineValues);
  const newIds = tokenize(input.new, intern, lineValues);
  const oldLength = oldIds.length;
  const newLength = newIds.length;

  let prefix = 0;
  const sharedLength = Math.min(oldLength, newLength);
  while (prefix < sharedLength && oldIds[prefix] === newIds[prefix]) prefix++;
  let suffix = 0;
  while (
    suffix < oldLength - prefix &&
    suffix < newLength - prefix &&
    oldIds[oldLength - suffix - 1] === newIds[newLength - suffix - 1]
  ) suffix++;

  const middleOldLength = oldLength - prefix - suffix;
  const middleNewLength = newLength - prefix - suffix;
  let traceOffsets = new Int32Array(16);
  let trace = new Int32Array(64);
  trace.fill(INVALID);
  let levelCapacity = traceOffsets.length;
  let traceCapacity = trace.length;
  traceOffsets[0] = 0;

  let oldPos = -1;
  let newPos = -1;
  while (
    oldPos + 1 < middleOldLength &&
    newPos + 1 < middleNewLength &&
    oldIds[prefix + oldPos + 1] === newIds[prefix + newPos + 1]
  ) {
    oldPos++;
    newPos++;
  }
  trace[0] = oldPos;

  let finalDistance = 0;
  let finalDiagonal = 0;
  let reachedEnd = oldPos + 1 >= middleOldLength && newPos + 1 >= middleNewLength;

  for (let distance = 1; !reachedEnd && distance <= middleOldLength + middleNewLength; distance++) {
    const rowOffset = (distance * (distance + 1)) / 2;
    const rowEnd = rowOffset + distance + 1;
    if (distance >= levelCapacity) {
      let nextCapacity = levelCapacity;
      while (nextCapacity <= distance) nextCapacity *= 2;
      const nextOffsets = new Int32Array(nextCapacity);
      nextOffsets.set(traceOffsets);
      traceOffsets = nextOffsets;
      levelCapacity = nextCapacity;
    }
    if (rowEnd > traceCapacity) {
      let nextCapacity = traceCapacity;
      while (nextCapacity < rowEnd) nextCapacity *= 2;
      const nextTrace = new Int32Array(nextCapacity);
      nextTrace.fill(INVALID);
      nextTrace.set(trace);
      trace = nextTrace;
      traceCapacity = nextCapacity;
    }
    traceOffsets[distance] = rowOffset;
    const previousOffset = traceOffsets[distance - 1];

    for (let diagonal = -distance; diagonal <= distance; diagonal += 2) {
      let removePos = INVALID;
      let addPos = INVALID;
      if (diagonal > -distance) {
        removePos = trace[previousOffset + ((diagonal + distance - 2) >> 1)];
      }
      if (diagonal < distance) {
        addPos = trace[previousOffset + ((diagonal + distance) >> 1)];
      }
      const canRemove = removePos !== INVALID && removePos + 1 < middleOldLength;
      const canAdd = addPos !== INVALID && addPos - diagonal < middleNewLength;
      if (!canRemove && !canAdd) continue;

      let nextOldPos;
      if (canRemove && (!canAdd || removePos + 1 >= addPos)) {
        nextOldPos = removePos + 1;
      } else {
        nextOldPos = addPos;
      }
      let nextNewPos = nextOldPos - diagonal;
      while (
        nextOldPos + 1 < middleOldLength &&
        nextNewPos + 1 < middleNewLength &&
        oldIds[prefix + nextOldPos + 1] === newIds[prefix + nextNewPos + 1]
      ) {
        nextOldPos++;
        nextNewPos++;
      }
      trace[rowOffset + ((diagonal + distance) >> 1)] = nextOldPos;
      if (nextOldPos + 1 >= middleOldLength && nextNewPos + 1 >= middleNewLength) {
        finalDistance = distance;
        finalDiagonal = diagonal;
        reachedEnd = true;
        break;
      }
    }
  }

  if (!reachedEnd) throw new Error('makefun-diff: the search ended without reaching both ends');

  const reverseCapacity = finalDistance * 2 + 1;
  const reverseKinds = new Int32Array(reverseCapacity);
  const reverseCounts = new Int32Array(reverseCapacity);
  let reverseLength = 0;
  let diagonal = finalDiagonal;
  let backtrackOldPos = trace[traceOffsets[finalDistance] + ((diagonal + finalDistance) >> 1)];

  for (let distance = finalDistance; distance > 0; distance--) {
    const previousOffset = traceOffsets[distance - 1];
    let removePos = INVALID;
    let addPos = INVALID;
    if (diagonal > -distance) {
      removePos = trace[previousOffset + ((diagonal + distance - 2) >> 1)];
    }
    if (diagonal < distance) {
      addPos = trace[previousOffset + ((diagonal + distance) >> 1)];
    }
    const canRemove = removePos !== INVALID && removePos + 1 < middleOldLength;
    const canAdd = addPos !== INVALID && addPos - diagonal < middleNewLength;
    const deletion = canRemove && (!canAdd || removePos + 1 >= addPos);
    const previousDiagonal = deletion ? diagonal - 1 : diagonal + 1;
    const previousOldPos = deletion ? removePos : addPos;
    const previousNewPos = previousOldPos - previousDiagonal;
    const afterEditOldPos = deletion ? previousOldPos + 1 : previousOldPos;
    const afterEditNewPos = deletion ? previousNewPos : previousNewPos + 1;
    const snakeLength = backtrackOldPos - afterEditOldPos;

    if (snakeLength > 0) {
      reverseKinds[reverseLength] = KEEP;
      reverseCounts[reverseLength++] = snakeLength;
    }
    reverseKinds[reverseLength] = deletion ? DELETE : INSERT;
    reverseCounts[reverseLength++] = 1;
    backtrackOldPos = previousOldPos;
    diagonal = previousDiagonal;
  }

  if (backtrackOldPos >= 0) {
    reverseKinds[reverseLength] = KEEP;
    reverseCounts[reverseLength++] = backtrackOldPos + 1;
  }

  const runKinds = new Int32Array(reverseLength + 2);
  const runCounts = new Int32Array(reverseLength + 2);
  let runLength = 0;
  runLength = appendRun(runKinds, runCounts, runLength, KEEP, prefix);
  for (let index = reverseLength - 1; index >= 0; index--) {
    runLength = appendRun(runKinds, runCounts, runLength, reverseKinds[index], reverseCounts[index]);
  }
  runLength = appendRun(runKinds, runCounts, runLength, KEEP, suffix);

  const changeOld = new Int32Array(runLength);
  const changeNew = new Int32Array(runLength);
  const changeDeleted = new Int32Array(runLength);
  const changeInserted = new Int32Array(runLength);
  let changeCount = 0;
  let oldLine = 0;
  let newLine = 0;
  let deleted = 0;
  let inserted = 0;
  let inChange = false;
  for (let index = 0; index < runLength; index++) {
    const kind = runKinds[index];
    const count = runCounts[index];
    if (kind === KEEP) {
      oldLine += count;
      newLine += count;
      inChange = false;
    } else {
      if (!inChange) {
        changeOld[changeCount] = oldLine;
        changeNew[changeCount] = newLine;
        changeCount++;
        inChange = true;
      }
      const changeIndex = changeCount - 1;
      if (kind === DELETE) {
        changeDeleted[changeIndex] += count;
        oldLine += count;
        deleted += count;
      } else {
        changeInserted[changeIndex] += count;
        newLine += count;
        inserted += count;
      }
    }
  }

  const hunkFirst = new Int32Array(changeCount);
  const hunkLast = new Int32Array(changeCount);
  let hunkCount = 0;
  for (let index = 0; index < changeCount; index++) {
    if (
      hunkCount === 0 ||
      changeOld[index] - (changeOld[hunkLast[hunkCount - 1]] + changeDeleted[hunkLast[hunkCount - 1]]) > 2 * CONTEXT
    ) {
      hunkFirst[hunkCount] = index;
      hunkLast[hunkCount] = index;
      hunkCount++;
    } else {
      hunkLast[hunkCount - 1] = index;
    }
  }

  const output = [`${FORMAT} old=${oldLength} new=${newLength} hunks=${hunkCount} deleted=${deleted} inserted=${inserted}\n`];
  for (let hunkIndex = 0; hunkIndex < hunkCount; hunkIndex++) {
    const first = hunkFirst[hunkIndex];
    const last = hunkLast[hunkIndex];
    const oldStart = Math.max(0, changeOld[first] - CONTEXT);
    const newStart = changeNew[first] - (changeOld[first] - oldStart);
    const after = Math.min(CONTEXT, oldLength - (changeOld[last] + changeDeleted[last]));
    const oldEnd = changeOld[last] + changeDeleted[last] + after;
    const newEnd = changeNew[last] + changeInserted[last] + after;
    output.push(`@ ${oldStart + 1} ${oldEnd - oldStart} ${newStart + 1} ${newEnd - newStart}\n`);
    let at = oldStart;
    for (let index = first; index <= last; index++) {
      const changeAt = changeOld[index];
      while (at < changeAt) {
        const line = lineValues[oldIds[at++]];
        output.push('=' + line + (line.charCodeAt(line.length - 1) === 10 ? '' : '\n%\n'));
      }
      const deletedCount = changeDeleted[index];
      for (let offset = 0; offset < deletedCount; offset++) {
        const line = lineValues[oldIds[changeAt + offset]];
        output.push('-' + line + (line.charCodeAt(line.length - 1) === 10 ? '' : '\n%\n'));
      }
      const insertedCount = changeInserted[index];
      const insertAt = changeNew[index];
      for (let offset = 0; offset < insertedCount; offset++) {
        const line = lineValues[newIds[insertAt + offset]];
        output.push('+' + line + (line.charCodeAt(line.length - 1) === 10 ? '' : '\n%\n'));
      }
      at = changeAt + deletedCount;
    }
    while (at < oldEnd) {
      const line = lineValues[oldIds[at++]];
      output.push('=' + line + (line.charCodeAt(line.length - 1) === 10 ? '' : '\n%\n'));
    }
  }
  return output.join('');
}
