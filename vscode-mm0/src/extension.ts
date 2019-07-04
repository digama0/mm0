/* --------------------------------------------------------------------------------------------
 * Copyright (c) Microsoft Corporation. All rights reserved.
 * Licensed under the MIT License. See License.txt in the project root for license information.
 * ------------------------------------------------------------------------------------------ */

import * as path from 'path';
import { workspace, ExtensionContext } from 'vscode';

import {
	LanguageClient,
	LanguageClientOptions,
	ServerOptions,
	TransportKind
} from 'vscode-languageclient';

let client: LanguageClient;

export function activate(_context: ExtensionContext) {
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
}

export function deactivate(): Thenable<void> | undefined {
	if (!client) {
		return undefined;
	}
	return client.stop();
}
