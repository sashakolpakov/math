import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Abelian.Schemes

/-! # Data -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Level.Data

/-! An abelian family with its actual full-level structure. -/

universe u

structure AbelianSchemeWithFullLevel (g N : ℕ) (S : AlgebraicGeometry.Scheme.{u}) where
  abelian : Abelian.Schemes.AbelianScheme g S
  level : abelian.FullLevel N

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Level.Data
