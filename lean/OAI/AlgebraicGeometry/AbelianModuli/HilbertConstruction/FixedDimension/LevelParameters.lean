import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.FixedDimension.PointData
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Projective.LevelParameters
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Level.Families

/-! # Level Parameters -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.FixedDimension.LevelParameters

noncomputable section

/-! The bounded Hilbert abelian parameter admits a concrete quasi-projective full-level parameter, with a universal projective abelian scheme and an actual full level. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

variable (S : Scheme.{u}) [IsNoetherian S] (n : ℕ) (P : Polynomial ℚ) (g : ℕ) (Pm Pi : Polynomial ℚ)

instance fixedDimensionHilbertAbelianParameter_noetherian :
    IsNoetherian (AbelianParameters.fixedDimensionHilbertAbelianParameter S n P g Pm Pi).left :=
  (AbelianParameters.fixedDimensionHilbertAbelianParameterQuasiProjectivePresentation S n P g Pm Pi).noetherian

variable (N : ℕ) [NeZero N]

def fixedDimensionHilbertFullLevelConstruction :
    Level.Families.ProjectiveFullLevelConstruction (AbelianParameters.fixedDimensionHilbertUniversalAbelianScheme S n P g Pm Pi) N :=
  @Abelian.Schemes.AbelianScheme.projectiveFullLevelConstruction g (AbelianParameters.fixedDimensionHilbertAbelianParameter S n P g Pm Pi).left
    (fixedDimensionHilbertAbelianParameter_noetherian S n P g Pm Pi)
    (AbelianParameters.fixedDimensionHilbertUniversalAbelianScheme S n P g Pm Pi) N inferInstance
    (AbelianParameters.fixedDimensionHilbertUniversalAbelianProjectivePresentation S n P g Pm Pi)

def fixedDimensionHilbertFullLevelRelativeParameter :
    Over (AbelianParameters.fixedDimensionHilbertAbelianParameter S n P g Pm Pi).left :=
  (fixedDimensionHilbertFullLevelConstruction S n P g Pm Pi N).parameter

def fixedDimensionHilbertFullLevelParameter : Over S :=
  (Over.map (AbelianParameters.fixedDimensionHilbertAbelianParameter S n P g Pm Pi).hom).obj
    (fixedDimensionHilbertFullLevelRelativeParameter S n P g Pm Pi N)

def fixedDimensionHilbertFullLevelRelativeQuasiProjectivePresentation :
    Projective.ProjectivePresentations.QuasiProjectivePresentation (fixedDimensionHilbertFullLevelRelativeParameter S n P g Pm Pi N) :=
  (fixedDimensionHilbertFullLevelConstruction S n P g Pm Pi N).quasiProjective

def fixedDimensionHilbertFullLevelQuasiProjectivePresentation :
    Projective.ProjectivePresentations.QuasiProjectivePresentation (fixedDimensionHilbertFullLevelParameter S n P g Pm Pi N) :=
  (AbelianParameters.fixedDimensionHilbertAbelianParameterQuasiProjectivePresentation S n P g Pm Pi).composition
    (fixedDimensionHilbertFullLevelRelativeQuasiProjectivePresentation S n P g Pm Pi N)

def fixedDimensionHilbertFullLevelUniversalFamily :
    Level.Data.AbelianSchemeWithFullLevel g N (fixedDimensionHilbertFullLevelParameter S n P g Pm Pi N).left :=
  (fixedDimensionHilbertFullLevelConstruction S n P g Pm Pi N).family

def fixedDimensionHilbertFullLevelUniversalAbelianScheme :
    Abelian.Schemes.AbelianScheme g (fixedDimensionHilbertFullLevelParameter S n P g Pm Pi N).left :=
  (fixedDimensionHilbertFullLevelUniversalFamily S n P g Pm Pi N).abelian

def fixedDimensionHilbertUniversalFullLevel :
    (fixedDimensionHilbertFullLevelUniversalAbelianScheme S n P g Pm Pi N).FullLevel N :=
  (fixedDimensionHilbertFullLevelUniversalFamily S n P g Pm Pi N).level

def fixedDimensionHilbertFullLevelUniversalProjectivePresentation :
    Projective.ProjectivePresentations.ProjectivePresentation (fixedDimensionHilbertFullLevelUniversalAbelianScheme S n P g Pm Pi N).scheme :=
  (fixedDimensionHilbertFullLevelConstruction S n P g Pm Pi N).projective

def fixedDimensionHilbertFullLevelParameterPointEquiv (T : Over S) :
    (T ⟶ fixedDimensionHilbertFullLevelParameter S n P g Pm Pi N) ≃
      Σ a : T ⟶ AbelianParameters.fixedDimensionHilbertAbelianParameter S n P g Pm Pi,
        ((AbelianParameters.fixedDimensionHilbertUniversalAbelianScheme S n P g Pm Pi).pullback a.left).FullLevel N := by
  exact (CompositeParameterPoints.compositeParameterPointEquiv (AbelianParameters.fixedDimensionHilbertAbelianParameter S n P g Pm Pi)
    (fixedDimensionHilbertFullLevelRelativeParameter S n P g Pm Pi N) T).trans
      (Equiv.sigmaCongrRight (fun a =>
        (fixedDimensionHilbertFullLevelConstruction S n P g Pm Pi N).points (Over.mk a.left)))

theorem fixedDimensionHilbertFullLevelParameter_geometric_family :
    Nonempty (Projective.ProjectivePresentations.QuasiProjectivePresentation (fixedDimensionHilbertFullLevelParameter S n P g Pm Pi N)) ∧
    ∃ A : Abelian.Schemes.AbelianScheme g (fixedDimensionHilbertFullLevelParameter S n P g Pm Pi N).left,
      Nonempty (Projective.ProjectivePresentations.ProjectivePresentation A.scheme) ∧ Nonempty (A.FullLevel N) :=
  ⟨⟨fixedDimensionHilbertFullLevelQuasiProjectivePresentation S n P g Pm Pi N⟩,
    fixedDimensionHilbertFullLevelUniversalAbelianScheme S n P g Pm Pi N,
    ⟨fixedDimensionHilbertFullLevelUniversalProjectivePresentation S n P g Pm Pi N⟩,
    ⟨fixedDimensionHilbertUniversalFullLevel S n P g Pm Pi N⟩⟩

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.FixedDimension.LevelParameters
