module DataStructure.Measured

public export

interface (Monoid v) => Measured a v where
  measure : a -> v
