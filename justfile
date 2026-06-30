set shell := ["bash", "-cu"]

default:
    just --list

clean:
    lake clean
    rm -rf data

download-ucd:
    node scripts/download_unicode_data.ts

tables:
    lake exe makeTables

clib:
    lake exe makeCLib

build:
    lake build --wfail UnicodeBasic UnicodeData lookup makeCLib makeTables

test:
    lake exe testTables

update-all: clean download-ucd tables clib build test
