import { defineConfig } from "@vscode/test-cli";

export default defineConfig({
  files: "out/test/**/*.test.js",
  //   installExtensions: ["maximedenes.vscoq"], TODO: uncomment when extension is actually used for testing
});
