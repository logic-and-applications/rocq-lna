import { Position, Range } from "vscode";

/**
 * Trims leading and trailing empty lines and adjusts the range for the given text fragment.
 * The range is calculated by removing any leading/trailing empty lines and trimming whitespace from the first
 * and last non-empty lines.
 *
 * @param fragment - The text fragment to be trimmed and adjusted.
 * @param start - The starting position of the fragment.
 * 
 * @returns A tuple containing the trimmed fragment and its adjusted range.
 */
function trimFragmentAndAdjustRange(fragment: string, start: Position): [string, Range] {
    const lines = fragment.split("\n");

    // Trim leading and trailing empty lines
    let firstLineIndex = 0;
    while (firstLineIndex < lines.length && lines[firstLineIndex].trim() === "") {
        firstLineIndex++;
    }

    let lastLineIndex = lines.length - 1;
    while (lastLineIndex >= firstLineIndex && lines[lastLineIndex].trim() === "") {
        lastLineIndex--;
    }

    // If there are no non-empty lines, return empty fragment and range
    if (firstLineIndex > lastLineIndex) {
        return ["", new Range(start, start)];
    }

    // Trim leading whitespace of the first non-empty line
    const firstLine = lines[firstLineIndex];
    const leadingWhitespace = firstLine.length - firstLine.trimStart().length;
    const charStart = firstLineIndex === 0 ? start.character : 0;
    const adjustedStart = new Position(start.line + firstLineIndex, charStart + leadingWhitespace);

    // Trim trailing whitespace of the last non-empty line
    const lastLine = lines[lastLineIndex];
    const lineEnd = start.line + lastLineIndex;
    const charEnd = lastLineIndex === 0 ? start.character : 0;
    const adjustedEnd = new Position(lineEnd, charEnd + lastLine.trimEnd().length);

    const trimmedFragment = lines.slice(firstLineIndex, lastLineIndex + 1).map((line, index, arr) => {
        if (index === 0) {
            return line.trimStart();
        }
        if (index === arr.length - 1) {
            return line.trimEnd();
        }
        return line;
    }).join("");
    return [trimmedFragment, new Range(adjustedStart, adjustedEnd)];
}

/**
 * Splits the given text into fragments based on a separator and computes a range for each fragment.
 * The range is trimmed to exclude any leading or trailing empty lines and unnecessary whitespace. 
 *
 * @param text - The text to be split into fragments.
 * @param range - The initial range used as a starting point for calculating fragment ranges.
 * @param delimiter - The delimiter used to split the text into fragments.
 * 
 * @returns An array of tuples, where each tuple contains a trimmed fragment and its associated range.
 */
export default function splitWithRange(text: string, range: Range, delimiter: string): [string, Range][] {
    const splitText = text.split(delimiter);
    const result: [string, Range][] = [];
    let currentStart = range.start;

    // Helper function to calculate the end position of a fragment
    function calculateEndPosition(fragment: string, start: Position): Position {
        const lines = fragment.split("\n");
        if (lines.length === 1) {
            return new Position(start.line, start.character + fragment.length + delimiter.length);
        }
        const lineEnd = start.line + lines.length - 1;
        const charEnd = lines[lines.length - 1].length;
        return new Position(lineEnd, charEnd);
    }

    for (const fragment of splitText) {
        const end = calculateEndPosition(fragment, currentStart);
        const trimmedResult = trimFragmentAndAdjustRange(fragment, currentStart);
        result.push(trimmedResult);
        currentStart = end; // Update start for next fragment
    }

    return result;
}
