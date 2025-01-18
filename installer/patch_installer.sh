#!/usr/bin/bash

# Comment out copies of non existing compcert files in installer
sed -i 's/cp source.coq-compcert/# cp source/' '/platform/windows/create_installer_windows.sh'

# Comment out coqide related files
sed -i 's/cp source.coqide/# cp source/' '/platform/windows/create_installer_windows.sh'
sed -i 's/\(.*\)coqide/; \1coqide/' '/platform/windows/Coq.nsi'
sed -i "s/!define MUI_ICON/; !define MUI_ICON/" '/platform/windows/Coq.nsi'