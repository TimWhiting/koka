new_version=$1
if [ -z "$new_version" ]; then
  echo "Usage: $0 <new-version>"
  exit 1
fi

if [ -f "package.yaml" ]; then
  sed -i '' "s/^version:    .*/version:    $new_version/" package.yaml
  sed -i '' "s/DKOKA_VERSION=.*/DKOKA_VERSION=\"$new_version\"/" package.yaml
else 
  echo "Error: Run in the koka root directory."
  exit 1
fi

# Update the version in the install scripts
sed -i '' "s/^VERSION=.*/VERSION=\"v$new_version\"/" util/install.sh
sed -i '' "s/^set KOKA_VERSION=.*/set KOKA_VERSION=v$new_version/" util/install.bat
# Build Script
sed -i '' "s/^KOKA_VERSION=.*/KOKA_VERSION=$new_version/" util/minbuild.sh
# VSCode extension compiler version
sed -i '' "s/\"compilerVersion\": .*/\"compilerVersion\": \"$new_version\",/" support/vscode/koka.language-koka/package.json