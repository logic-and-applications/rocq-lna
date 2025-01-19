import allowLists, { pragma, pragmas } from './tactics';
import { DocumentProofsResponse, ProofBlock, VscoqExport } from './types';
import { DecorationOptions, Extension, extensions, Position, Range, TextDocument, window, workspace } from 'vscode';
import splitWithRange from './splitWithRange';

// The delay of waiting after each change before updating the decorations
const UPDATE_DELAY_MS = 300;
// The delay of waiting before retrying the server after a busy signal
const SERVER_CANCEL_DELAY_MS = 500;

const decoration = window.createTextEditorDecorationType({
	textDecoration: 'underline wavy #ff0000'
});

type PragmaData = {
	// Any key of allowLists
	pragma: pragma,
	// The range for which this pragma does NOT apply in the proof
	ignorableRange?: Range,
}

let timeout: NodeJS.Timeout;

/**
 * Extracts the pragma data (identifier and range to ignore this pragma) from a given proof block and editor document.
 * 
 * @param proofBlock - The proof block containing the range to search for a pragma.
 * @param editor - The editor document containing the proof text.
 * 
 * @returns An object containing the found pragma data or default pragma if not found.
 */
function getPragmaData(proofBlock: ProofBlock, editor: TextDocument): PragmaData {
	// Helper to get the right type
	function isPragma(pragma: string): pragma is pragma {
		return pragmas.includes(pragma);
	}

	for (let [lineNumber, line] of editor.getText(proofBlock.range).split("\n").entries()) {
		const pragma = line.replaceAll(/[\(\*\!]|[\*\)]/g, "").trim();
		if (isPragma(pragma)) {
			lineNumber += proofBlock.range.start.line;
			const range = new Range(new Position(lineNumber, 0), new Position(lineNumber, line.length - 1));
			return { pragma, ignorableRange: range };
		}
	}
	return { pragma: "default" };
}

/**
 * Generates all necessary decorations for a proof block within the editor.
 *
 * @param proofBlock - The proof block containing steps and their associated ranges.
 * @param editor - The editor document to apply the decorations to.
 * 
 * @returns An array of decorations for the proof block.
 */
function createBlockDecorations(proofBlock: ProofBlock, editor: TextDocument): DecorationOptions[] {

	// Helper that checks whether a given proof line should be ignored based on the pragma data.
	function shouldBeIgnored(pragmaData: PragmaData, proofLine: number): boolean {
		return !!pragmaData.ignorableRange && pragmaData.ignorableRange.end.line >= proofLine;
	}

	// Helper that creates a decoration with the tactic name's name as a hover message
	function createDecoration(range: Range, tacticName: string, pragma: string): DecorationOptions {
		return {
			range: range,
			hoverMessage: `tactic ${tacticName.replace(".", "")} is not allowed for ${pragma} proofs.`,
		};
	}

	const pragmaData = getPragmaData(proofBlock, editor);

	let allowList = allowLists[pragmaData.pragma];
	const decorations: DecorationOptions[] = [];

	for (let { tactic, range } of proofBlock.steps) {
		if (shouldBeIgnored(pragmaData, range.start.line)) {
			continue;
		}

		for (const [splitTactic, splitRange] of splitWithRange(tactic, range, ";")) {

			if (allowList.some((allowedTactic) => splitTactic.includes(allowedTactic))) {
				continue;
			}

			decorations.push(createDecoration(splitRange, splitTactic, pragmaData.pragma));
		}
	}

	return decorations;
}

/**
 * Generates the decorations for an entire document based on parsed proof data.
 *
 * @param documentProofs - The parsed proof data for the document.
 * @param document - The editor document where the decorations will be applied.
 * 
 * @returns A promise that resolves to an array of decoration options for the document.
 */
export async function createDocumentDecorations(documentProofs: DocumentProofsResponse, document: TextDocument): Promise<DecorationOptions[]> {
	const decorations = documentProofs.proofs.flatMap((proofBlock) => {

		// make proofBlock.range an actual range, not just an object
		proofBlock.range = new Range(proofBlock.range.start, proofBlock.range.end);

		return createBlockDecorations(proofBlock, document);
	});

	return decorations;
}

/**
 * Schedules an update to apply decorations after a delay.
 * If there's already an ongoing update, it will be canceled and start a new calculation.
 *
 * @param document - The document whose decorations need to be updated.
 * @param delay - The delay in milliseconds before updating the decorations (defaults to the constant `UPDATE_DELAY_MS`).
 */
function triggerUpdateDecorations(document: TextDocument, delay = UPDATE_DELAY_MS) {
	if (timeout) {
		clearTimeout(timeout);
	}
	timeout = setTimeout(() => updateDecorations(document), delay);
}

/**
 * Refreshes the decorations for the given document by fetching the latest proof data and applying 
 * the corresponding decorations. If the request is canceled by the server, the function will 
 * reschedule the update with a delay of `SERVER_CANCEL_DELAY_MS`, which should be longer than the 
 * default delay.
 *
 * @param document - The document whose decorations will be refreshed.
 */
async function updateDecorations(document: TextDocument) {

	// Helper that applies the provided decoration options to the active editor.
	function applyDecorations(decorations: DecorationOptions[]) {
		log.appendLine(`Applied decorations:\n ${JSON.stringify(decorations)}`);
		window.activeTextEditor?.setDecorations(decoration, decorations);
	}

	if (!window.activeTextEditor) { return; }

	try {

		const documentProofs = await vscoq?.exports.getDocumentProofs(document.uri);

		if (!documentProofs) { return; }

		log.appendLine(`Received parsed file:\n ${JSON.stringify(documentProofs)}`);

		const decorations = await createDocumentDecorations(documentProofs, document);

		applyDecorations(decorations);
	} catch (e) {
		const ServerCancelledCode = -32802;
		if (e && typeof e === "object" && "code" in e && e.code === ServerCancelledCode) {
			triggerUpdateDecorations(document, SERVER_CANCEL_DELAY_MS);
		}
	}

}

let vscoq: Extension<VscoqExport> | undefined;
const log = window.createOutputChannel('rocq-lna');

/**
 * Activates the extension and sets up event listeners for editor and document changes.
 * When the active editor or document changes, it triggers the decoration update process.
 */
export function activate() {
	vscoq = extensions.getExtension('maximedenes.vscoq');
	log.appendLine("Extension activated");

	if (window.activeTextEditor) {
		triggerUpdateDecorations(window.activeTextEditor.document);
	}

	window.onDidChangeActiveTextEditor(editor => {
		if (!editor) { return; }

		triggerUpdateDecorations(editor.document);
	});

	window.onDidChangeWindowState(() => {
		if (!window.activeTextEditor) { return; }
		triggerUpdateDecorations(window.activeTextEditor.document);
	});

	workspace.onDidChangeTextDocument(async (event) => {

		if (window.activeTextEditor && event.document === window.activeTextEditor.document) {
			await triggerUpdateDecorations(event.document);
		}
	});
}

// This method is called when your extension is deactivated
export function deactivate() { }