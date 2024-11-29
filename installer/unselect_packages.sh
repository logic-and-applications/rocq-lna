#######################################
# Change nsh files to unselect package by default.
# Globals:
#   $FILE_SEC_VISIBLE:      Location of the NSIS include file for the visible installer sections.
# Arguments:
#   $1 Package name.
# Outputs:
#   Change in package nsh file which makes it unselected by default.
#######################################
function unselect_package {
  package=$1
  package_lower=${1//-/_}

  # Add /o to line to make it unselected
  sed -i 's|^Section "'"$package"'".*|Section /o "'"$package"'" Sec_'"$package_lower"'|g' $FILE_SEC_VISIBLE
}
