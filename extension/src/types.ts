import { Range, Uri } from "vscode";

export type VscoqExport = {
    getDocumentProofs: (uri: Uri) => Promise<DocumentProofsResponse>
}

export type ProofStatement = {
    range: Range;
    statement: string;
}

export type ProofStep = {
    range: Range;
    tactic: string;
};

export type ProofBlock = {
    statement: ProofStatement;
    range: Range;
    steps: ProofStep[];
};

export interface DocumentProofsResponse {
    proofs: ProofBlock[];
}
