import allowLists, { pragma, pragmas } from './tactics';
import { DocumentProofsResponse, ProofBlock, VscoqExport } from './types';
import { DecorationOptions, Extension, extensions, Location, Position, Range, TextDocument, TextDocumentChangeEvent, TextEditor, window, workspace } from 'vscode';

const decoration = window.createTextEditorDecorationType({
	textDecoration: 'underline wavy #ff0000'
});

type PragmaData = {
	pragma: pragma,
	range?: Range,
}

let timeout: NodeJS.Timeout;

function isPragma(pragma: string): pragma is pragma {
	return pragmas.includes(pragma);
}

function getPragmaData(proofBlock: ProofBlock, editor: TextDocument): PragmaData {
	for (let [lineNumber, line] of editor.getText(proofBlock.range).split("\n").entries()) {
		const pragma = line.replaceAll(/[\(\*\!]|[\*\)]/g, "").trim();
		if (isPragma(pragma)) {
			lineNumber += proofBlock.range.start.line;
			const range = new Range(new Position(lineNumber, 0), new Position(lineNumber, line.length - 1));
			return { pragma, range };
		}
	}
	return { pragma: "default" };
}

function isBeforePragma(pragmaData: PragmaData, proofLine: number) {
	return !!pragmaData.range && pragmaData.range.end.line >= proofLine;
}

function createDecoration(range: Range, tacticName: string, pragma: string): DecorationOptions {
	return {
		range: range,
		hoverMessage: `tactic ${tacticName} is not allowed for ${pragma} proofs	.`,
	};
}

function createBlockDecorations(proofBlock: ProofBlock, editor: TextDocument) {
	const pragmaData = getPragmaData(proofBlock, editor);

	let allowList = allowLists[pragmaData.pragma];
	const decorations = [];

	for (let { tactic, range } of proofBlock.steps) {
		if (isBeforePragma(pragmaData, range.start.line)) {
			continue;
		}

		if (allowList.some((allowedTactic) => tactic.includes(allowedTactic))) {
			continue;
		}

		decorations.push(createDecoration(range, tactic, pragmaData.pragma));
	}

	return decorations;
}

function applyDecorations(decorations: DecorationOptions[]) {
	window.activeTextEditor?.setDecorations(decoration, decorations);
}

// fire decoration update using a small delay
function triggerUpdateDecorations(document: TextDocument, delay = 200) {
	if (timeout) {
		clearTimeout(timeout);
	}
	timeout = setTimeout(() => updateDecorations(document), delay);
}

async function updateDecorations(document: TextDocument) {
	if (!window.activeTextEditor) { return; }
	try {
		const documentProofs = await vscoq?.exports.getDocumentProofs(document.uri);

		if (!documentProofs) { return; }

		const decorations = documentProofs.proofs.flatMap((proofBlock) => {
			// make proofBlock.range an actual range, not just an object
			proofBlock.range = new Range(proofBlock.range.start, proofBlock.range.end);
			return createBlockDecorations(proofBlock, document);
		});

		applyDecorations(decorations);
	} catch (e) {
		if (e && typeof e === "object" && "code" in e && e.code === "ServerCancelled") {
			triggerUpdateDecorations(document, 400);
		}
	}
}

let vscoq: Extension<VscoqExport> | undefined;
const log = window.createOutputChannel('rocq-lna');
export function activate() {
	vscoq = extensions.getExtension('maximedenes.vscoq');
	log.appendLine("Extension activated !");

	window.onDidChangeActiveTextEditor(editor => {
		log.appendLine("Active editor changed");
		if (!editor) { return; }

		triggerUpdateDecorations(editor.document);
	});

	workspace.onDidChangeTextDocument(async (event) => {

		if (window.activeTextEditor && event.document === window.activeTextEditor.document) {
			await triggerUpdateDecorations(event.document);
		}
	});
}

// This method is called when your extension is deactivated
export function deactivate() { }