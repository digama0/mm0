import { window, workspace, ExtensionContext, TextDocument, EndOfLine } from 'vscode';

import {
	LanguageClient,
	LanguageClientOptions,
	ServerOptions
} from 'vscode-languageclient';

let client: LanguageClient;

export function activate(context: ExtensionContext) {
	// If the extension is launched in debug mode then the debug server options are used
	// Otherwise the run options are used
	let serverOptions: ServerOptions = {
		run: { command: 'mm0-hs', args: ['server'] },
		debug: { command: 'mm0-hs', args: ['server', '--debug'] }
	};

	// Options to control the language client
	let clientOptions: LanguageClientOptions = {
		// Register the server for MM0 files
		documentSelector: [{ scheme: 'file', language: 'metamath-zero' }],
	};

	// Create the language client and start the client.
	client = new LanguageClient(
		'metamath-zero', 'Metamath Zero', serverOptions, clientOptions);

	// Start the client. This will also launch the server
	client.start();

	// Unfortunately it is not possible to set the default line endings to LF,
	// which is required for MM0 files. Instead we just try to set it to LF
	// on open and save.
	function makeLF(doc: TextDocument) {
		if (doc.languageId === 'metamath-zero' &&
				doc.eol !== EndOfLine.LF &&
				window.activeTextEditor) {
			window.activeTextEditor.edit(
				builder => builder.setEndOfLine(EndOfLine.LF))
		}
	}
	context.subscriptions.push(
		workspace.onDidOpenTextDocument(makeLF),
		workspace.onWillSaveTextDocument(e => makeLF(e.document)));
}

export function deactivate(): Thenable<void> | undefined {
	if (!client) {
		return undefined;
	}
	return client.stop();
}
