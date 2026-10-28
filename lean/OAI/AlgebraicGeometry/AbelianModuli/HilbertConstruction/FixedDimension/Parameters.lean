import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Hilbert.FamilyDimensionOpen
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.SmoothHilbert.HilbertParameterGeometry
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.SmoothHilbert.UniversalProperty

/-! # Parameters -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.FixedDimension.Parameters

noncomputable section

/-! An actual open of the smooth Hilbert parameter carries a universal Hilbert family of the specified smooth relative dimension. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

local instance dimensionHilbertUniversalSmooth (S : Scheme.{u}) (n : ℕ) (P : Polynomial ℚ) :
    Smooth (SmoothHilbert.Parameter.smoothHilbertUniversalFamily S n P).family.scheme.hom := SmoothHilbert.Parameter.smoothHilbertUniversalFamily_smooth S n P

def FixedDimensionRelativeProjectiveHilbertFamily (T : Scheme.{u}) (n : ℕ) (P : Polynomial ℚ) (g : ℕ) :=
  {F : RelativeProjective.Families.RelativeProjectiveHilbertFamily T n P // SmoothOfRelativeDimension g F.family.scheme.hom}

def fixedDimensionSmoothFamilyEquiv (T : Scheme.{u}) (n : ℕ) (P : Polynomial ℚ) (g : ℕ) :
    {F : SmoothHilbert.PointEquivalence.SmoothRelativeProjectiveHilbertFamily T n P // SmoothOfRelativeDimension g F.val.family.scheme.hom} ≃
      FixedDimensionRelativeProjectiveHilbertFamily T n P g where
  toFun F := ⟨F.val.val, F.property⟩
  invFun F := by
    let : SmoothOfRelativeDimension g F.val.family.scheme.hom := F.property
    exact ⟨⟨F.val, SmoothOfRelativeDimension.smooth g _⟩, F.property⟩
  left_inv _ := Subtype.ext rfl
  right_inv _ := Subtype.ext rfl

variable (S : Scheme.{u}) (n : ℕ) (P : Polynomial ℚ) (g : ℕ)

def fixedDimensionHilbertParameter : Over S :=
  Open.ParameterPoints.openParameterScheme (SmoothHilbert.Parameter.smoothHilbertParameter S n P) ((SmoothHilbert.Parameter.smoothHilbertUniversalFamily S n P).dimensionBaseOpen g)

def fixedDimensionHilbertParameterInclusion : fixedDimensionHilbertParameter S n P g ⟶ SmoothHilbert.Parameter.smoothHilbertParameter S n P :=
  Open.ParameterPoints.openParameterInclusion (SmoothHilbert.Parameter.smoothHilbertParameter S n P) ((SmoothHilbert.Parameter.smoothHilbertUniversalFamily S n P).dimensionBaseOpen g)

instance fixedDimensionHilbertParameterInclusion_open :
    IsOpenImmersion (fixedDimensionHilbertParameterInclusion S n P g).left :=
  Open.ParameterPoints.openParameterInclusion_open (SmoothHilbert.Parameter.smoothHilbertParameter S n P) ((SmoothHilbert.Parameter.smoothHilbertUniversalFamily S n P).dimensionBaseOpen g)

def fixedDimensionHilbertUniversalFamily : RelativeProjective.Families.RelativeProjectiveHilbertFamily (fixedDimensionHilbertParameter S n P g).left n P :=
  (SmoothHilbert.Parameter.smoothHilbertUniversalFamily S n P).pullback (fixedDimensionHilbertParameterInclusion S n P g).left

theorem fixedDimensionHilbertUniversalFamily_dimension :
    SmoothOfRelativeDimension g (fixedDimensionHilbertUniversalFamily S n P g).family.scheme.hom := by
  apply ((SmoothHilbert.Parameter.smoothHilbertUniversalFamily S n P).pullback_dimension_iff_range g
    (fixedDimensionHilbertParameterInclusion S n P g).left).mpr
  rintro s ⟨t, rfl⟩
  exact t.property

def fixedDimensionHilbertParameterQuasiProjectivePresentation [IsNoetherian S] :
    Projective.ProjectivePresentations.QuasiProjectivePresentation (fixedDimensionHilbertParameter S n P g) :=
  (SmoothHilbert.QuasiProjectivity.smoothHilbertParameterQuasiProjectivePresentation S n P).openParameter
    ((SmoothHilbert.Parameter.smoothHilbertUniversalFamily S n P).dimensionBaseOpen g)

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.FixedDimension.Parameters
