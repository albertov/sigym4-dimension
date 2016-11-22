{ mkDerivation, attoparsec, base, bytestring, containers, deepseq
, hspec, iso8601-duration, monad-loops, mtl, newtype, QuickCheck
, stdenv, template-haskell, time
}:
mkDerivation {
  pname = "sigym4-dimension";
  version = "0.1.0.3";
  src = ./.;
  libraryHaskellDepends = [
    attoparsec base bytestring containers deepseq iso8601-duration
    monad-loops mtl newtype template-haskell time
  ];
  testHaskellDepends = [
    attoparsec base containers hspec QuickCheck time
  ];
  homepage = "http://github/meteogrid/sigym4-dimension";
  description = "Dimension types";
  license = stdenv.lib.licenses.bsd3;
}
