{ mkDerivation, attoparsec, base, containers, deepseq, hspec
, iso8601-duration, monad-loops, mtl, QuickCheck, stdenv, time
}:
mkDerivation {
  pname = "sigym4-dimension";
  version = "0.1.0.3";
  src = ./.;
  libraryHaskellDepends = [
    attoparsec base containers deepseq iso8601-duration monad-loops mtl
    time
  ];
  testHaskellDepends = [
    attoparsec base containers hspec QuickCheck time
  ];
  homepage = "http://github/meteogrid/sigym4-dimension";
  description = "Dimension types";
  license = stdenv.lib.licenses.bsd3;
}
