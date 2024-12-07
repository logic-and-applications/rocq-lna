#!/usr/bin/bash

# Comment out copies of non existing compcert files in installer
sed -i 's/cp source.coq-compcert/# cp source/' '/platform/windows/create_installer_windows.sh'

