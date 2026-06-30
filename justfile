set shell := ["bash", "-cu"]

default:
    just --list

clean:
    lake clean
    rm -rf data

download-ucd:
    node scripts/download_unicode_data.ts

docs-readme:
    ln -sfn ../README.md docs/README.md

ucd-usage-status:
    node scripts/ucd_txt_usage.ts

generate-do-not-emit:
    node scripts/generate_do_not_emit.ts

generate-names-list:
    node scripts/generate_names_list.ts

table-provenance:
    node scripts/ucd_table_provenance.ts

tables:
    lake exe makeTables

clib:
    lake exe makeCLib

build:
    lake build --wfail UnicodeBasic UnicodeData lookup makeCLib makeTables

test:
    lake exe testTables && lake exe testConformance

check-ucd-text:
    node scripts/check_ucd_text_not_baked.ts

update-all: clean download-ucd tables clib build test
