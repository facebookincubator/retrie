#!/bin/sh

cabal configure --allow-newer --with-compiler=ghc-9.2.1 --enable-tests
# cabal configure --allow-newer --with-compiler=/opt/ghc/9.2.0.20211025/bin/ghc --enable-tests
