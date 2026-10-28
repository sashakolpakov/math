import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Level.Data
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Projective.LevelParameters

/-! # Families -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction

noncomputable section

/-! An actual abelian family with full level, and the universal such family on the constructed full-level parameter. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

def Abelian.Schemes.AbelianScheme.universalFullLevelFamily {g : ℕ} {S : Scheme.{u}} [IsNoetherian S]
    (A : Abelian.Schemes.AbelianScheme g S) (N : ℕ) [NeZero N] :
    Level.Data.AbelianSchemeWithFullLevel g N (A.fullLevelParameter N).left where
  abelian := A.pullback (A.fullLevelParameter N).hom
  level := A.universalFullLevel N

structure Level.Families.ProjectiveFullLevelConstruction {g : ℕ} {S : Scheme.{u}} (A : Abelian.Schemes.AbelianScheme g S) (N : ℕ) where
  parameter : Over S
  quasiProjective : Projective.ProjectivePresentations.QuasiProjectivePresentation parameter
  family : Level.Data.AbelianSchemeWithFullLevel g N parameter.left
  projective : Projective.ProjectivePresentations.ProjectivePresentation family.abelian.scheme
  points : ∀ T : Over S, (T ⟶ parameter) ≃ (A.pullback T.hom).FullLevel N

def Abelian.Schemes.AbelianScheme.projectiveFullLevelConstruction {g : ℕ} {S : Scheme.{u}} [IsNoetherian S]
    (A : Abelian.Schemes.AbelianScheme g S) (N : ℕ) [NeZero N] (P : Projective.ProjectivePresentations.ProjectivePresentation A.scheme) :
    Level.Families.ProjectiveFullLevelConstruction A N where
  parameter := A.fullLevelParameter N
  quasiProjective := A.fullLevelParameterQuasiProjectivePresentation N P
  family := A.universalFullLevelFamily N
  projective := P.baseChange (A.fullLevelParameter N).hom
  points := A.fullLevelParameterPointEquiv N

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction
