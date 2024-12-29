# LnA-vscode-extension README

An extension made for Radboud University CS course Logic and Applications to highlight illegal tactics

## Features

- Highlights illegal tactics based on the pragma associated with a proof

## Requirements

Requires $\geq$ Vscoq v2.2.1 to be installed as well

## For Maintainers

The [`tactics.ts`] file is where the set of tactics for each pragma is saved. It simply creates lists of strings, which are then associated with pragmas at the bottom of the page in the `allowLists` object. The keys of this object are the pragmas and the values the allowed tactics. For example, the line
https://github.com/logic-and-applications/rocq-lna/blob/cf20918e8092b3cd2be02d3d25c905bc2470846d/extension/src/tactics.ts#L51
creates a pragma `(*! benb_proof *)` which only allows tactics saved in the `allowed_tacs_benb` list.
The `allowList` object is required to have the `default` pragma, which is the allow list used when no pragmas are given.

Similar to the `library` subdirectory, the extension has a few tests which tests to see if the output of the extension has not changed. Unlike the `library` subdirectory, however, the expected output is not automatically generated. Instead, the extension provides debug information in the output channel `LnA` whenever it generates the highlights announced with `Applied Decorations`.

<!-- ![Applied decorations json in output channel](images/output-channel-decorations.png) -->
<!-- Does not work until repo public! -->

This can then be copied to a file with the correct name. It is preferable to format this file (eg. using an auto formatter like Prettier) to make this output more readable.

The tests are run automatically whenever any changes are made within the `extension` subdirectory. They can be run manually with `npm i && npm run test` from within the `extension` subdirectory. This opens a new VS Code window to run the tests in, which is why the [`test_extension.yml`](../.github/workflows/tests_extension.yml) workflow uses `xvfb`.

The extension can be debugged by opening the `extension` folder in VS Code and pressing F5. This will open a new VS Code window with the extension installed, while debug information is available in the original window.

Building the extension locally can be done by calling `npm i && npx vsce package`.

## Release Notes

Users appreciate release notes as you update your extension.

### 1.0.0

Initial release
