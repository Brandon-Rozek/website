#!/usr/bin/env sh

# Generate toot markdown files

pushd content/toots/.scripts > /dev/null

generate_exe="./target/release/generate_md"

# Check if the file exists and is executable
if [ -e "$generate_exe" ] && [ -x "$generate_exe" ]; then
    echo "The file '$file_path' exists and is executable."
    ./target/release/generate_md
else
    echo "The executable '$generate_exe' does not exist."
    echo "Perhaps run cargo build in 'content/toots/.scripts'?"
fi

popd > /dev/null
