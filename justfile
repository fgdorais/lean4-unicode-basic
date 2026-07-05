# just --list

set shell := ["bash", "-cu"]

# Define the directories once
dirs := "common table-generators lib lean-scripts tests"

# Run an arbitrary command in every directory
# Usage: just lake-all-do "lake update"
lake-all-do command:
    @for dir in {{ dirs }}; do \
        echo "==> Entering $dir to execute {{ command }}"; \
        (cd $dir && {{ command }}); \
    done
clean:
    @just lake-all-do "lake clean"
    # rm -rf table-generators/data-ucd
    rm -frd lib/UnicodeBasic/TableLookupTables

update:
    @just lake-all-do "lake update"

download_unicode_data:
    node scripts/download_unicode_data.ts

docs-readme:
    ln -sfn ../README.md docs/README.md

ucd-txt-usage:
    node scripts/ucd_txt_usage.ts

generate-do-not-emit:
    node scripts/generate_do_not_emit.ts

generate-names-list:
    node scripts/generate_names_list.ts

generate-script-types:
    node scripts/generate_script_types.ts

table-provenance:
    node scripts/ucd_table_provenance.ts

tables:
    cd table-generators && lake exe makeTablesForLookup

set-toolchain tag:
    for dir in {{ dirs }}; do \
        echo "leanprover/lean4:{{ tag }}" > "$dir/lean-toolchain"; \
    done

# Build all directories
build:
    @just lake-all-do "lake build --wfail"

test:
    cd tests && lake test

check-ucd-text:
    node scripts/check_ucd_text_not_baked.ts

all: generate-script-types tables build test
