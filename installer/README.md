## Configuring custom packages

This configuration file specifies which packages should be installed and the default selection.
Each package to be added needs the following properties:

- The source type of the package. Specified by one of OPAM, GITHUB and LOCAL. Read next sections for clarification for each of these
- The name of the package which to be displayed in the installer
- Whether or not the package should be selected in the installer by default. Specified by either SELECTED or UNSELECTED

## Existing opam packages

For existing Opam packages, the display name should be the name as **registered in opam**.

example:

`OPAM 'coq-serapi' SELECTED`

`OPAM 'vscoq-language-server' SELECTED `

### Custom Github packages

In addition to the standard properties, custom Github packages require the following properties needs to be specified

- relative package location: the path location in windows format relative to the Opam switch
- package description: description shown in installer
- Github owner: repository owner
- Github repository: name of repository

example:

`GITHUB 'zfc' UNSELECTED 'lib/coq/user-contrib/ZFC' 'An encoding of Zermelo-Fraenkel Set Theory in Coq' 'coq-contribs' 'zfc'`

### Custom Local packages

For custom local packages already on the device (for example in case of a mono repo), the following additional properties needs to be specified:

- relative package location: the path location in windows format relative to the Opam switch
- package description: description shown in installer
- path to local makefile

example:

`LOCAL 'LnA' SELECTED 'lib/coq/user-contrib/LnA' 'A libary used for Radboud University CS course Logic and Applications' '/platform/LnA'`
