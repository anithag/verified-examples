#!/bin/sh

krml -tmpdir extracted -verify -skip-compilation -bundle WasmSupport  -bundle Ring+Reader+Writer+Misc= Ring.fst Reader.fst Writer.fst Misc.fst
