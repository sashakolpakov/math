import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.FixedDimension.Representation

/-! # Family -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.FixedDimension.Family

noncomputable section

/-! The fixed-dimension Hilbert universal family has an explicit projective presentation and the precise geometric instances needed for bounded operation parameters. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

instance fixedDimensionHilbertParameter_noetherian (S : Scheme.{u}) [IsNoetherian S]
    (n : ℕ) (P : Polynomial ℚ) (g : ℕ) : IsNoetherian (Parameters.fixedDimensionHilbertParameter S n P g).left :=
  (Parameters.fixedDimensionHilbertParameterQuasiProjectivePresentation S n P g).noetherian

instance fixedDimensionHilbertUniversalFamily_proper (S : Scheme.{u}) (n : ℕ) (P : Polynomial ℚ) (g : ℕ) :
    IsProper (Parameters.fixedDimensionHilbertUniversalFamily S n P g).family.scheme.hom :=
  (Parameters.fixedDimensionHilbertUniversalFamily S n P g).family.proper

instance fixedDimensionHilbertUniversalFamily_smooth (S : Scheme.{u}) (n : ℕ) (P : Polynomial ℚ) (g : ℕ) :
    Smooth (Parameters.fixedDimensionHilbertUniversalFamily S n P g).family.scheme.hom := by
  have : SmoothOfRelativeDimension g (Parameters.fixedDimensionHilbertUniversalFamily S n P g).family.scheme.hom :=
    Parameters.fixedDimensionHilbertUniversalFamily_dimension S n P g
  exact SmoothOfRelativeDimension.smooth g _

def fixedDimensionHilbertUniversalProjectivePresentation (S : Scheme.{u}) (n : ℕ) (P : Polynomial ℚ) (g : ℕ) :
    Projective.ProjectivePresentations.ProjectivePresentation (Parameters.fixedDimensionHilbertUniversalFamily S n P g).family.scheme where
  dimension := n
  embedding := (Parameters.fixedDimensionHilbertUniversalFamily S n P g).family.inclusion
  closedImmersion := inferInstance

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.FixedDimension.Family
