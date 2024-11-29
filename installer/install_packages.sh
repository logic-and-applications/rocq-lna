#!/usr/bin/bash

set -e

#######################################
# Installs Github repository.
# Globals:
#   -
# Arguments:
#   $1 Owner of repository.
#   $2 Repository name.
# Outputs:
#   Creates compiled package in Coq directory
#######################################
function install_package_github {
  echo "Installing Github package $1/$2."
  
  # Clone repo
  git clone https://github.com/$1/$2

  # Build and install repository
  cd $2  # Enter repository
  
  # print last commit
  git log -1
  
  make
  make install
  cd ..  # Leave repository
  rm -rf $2  # Delete repository
  
  echo "Finished installing Github package $1/$2."
}

#######################################
# Let create installer script create package unselected by default.
# Globals:
#   -
# Arguments:
#   $1 package
# Outputs:
#   Changes create installer script to have $1 unselected by default in installer
#######################################
function unselect {
      sed -i '/^###### Create the NSIS installer #####/a unselect_package '"$1" windows/create_installer_windows.sh
}

# Create folder in which to perform Github clones
mkdir github_packages

config_file=$1
# Read all lines not starting with #
grep -v '^#' $config_file | while read -r line ; do
  eval "package_info=($line)"

  package_name=${package_info[1]}
  package_selected=${package_info[2]}
  
  if [ "$package_selected" == "UNSELECTED" ] ; then
    unselect ${package_info[1]}
  fi
  
  if [[ $line =~ ^GITHUB* ]] ; then
    package_path=${package_info[3]}
    package_description=${package_info[4]}
    owner_name=${package_info[5]}
    repo_name=${package_info[6]}

    cd github_packages
    install_package_github $owner_name $repo_name
    cd ..

    # Inject install code into installer script
    sed -i '/^echo "Create package list"/a add_custom_package "'"${package_name}"'" "'"${package_path}"'" "'"${package_description}"'"' windows/create_installer_windows.sh
  elif [[ $line =~ ^OPAM* ]] ; then
    opam install -y $package_name
  fi
done

# Remove folders in which to 
rmdir github_packages

# Inject install imports into create installer script
sed -i '/^echo "Create package list"/a source add_custom_nsis.sh' windows/create_installer_windows.sh  # Custom package functions

sed -i '/^###### Create the NSIS installer #####/a source unselect_packages.sh' windows/create_installer_windows.sh  # Unselect package functions

cat windows/create_installer_windows.sh
