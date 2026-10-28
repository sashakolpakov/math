import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.FixedDimension.Parameters

/-! # Point Equivalence -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.FixedDimension.PointEquivalence

noncomputable section

/-! Every test-scheme point of the fixed-dimension Hilbert open is equivalent to an actual embedded Hilbert family with the prescribed smooth relative dimension. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

local instance dimensionPointUniversalSmooth (S : Scheme.{u}) (n : ℕ) (P : Polynomial ℚ) :
    Smooth (SmoothHilbert.Parameter.smoothHilbertUniversalFamily S n P).family.scheme.hom := SmoothHilbert.Parameter.smoothHilbertUniversalFamily_smooth S n P

variable (S : Scheme.{u}) (T : Over S) (n : ℕ) (P : Polynomial ℚ) (g : ℕ)

def fixedDimensionHilbertRangeEquiv :
    {c : T ⟶ SmoothHilbert.Parameter.smoothHilbertParameter S n P // Set.range c.left ⊆ (SmoothHilbert.Parameter.smoothHilbertUniversalFamily S n P).dimensionBaseOpen g} ≃
      {c : T ⟶ SmoothHilbert.Parameter.smoothHilbertParameter S n P //
        SmoothOfRelativeDimension g ((SmoothHilbert.Parameter.smoothHilbertUniversalFamily S n P).pullback c.left).family.scheme.hom} where
  toFun c := ⟨c.val, ((SmoothHilbert.Parameter.smoothHilbertUniversalFamily S n P).pullback_dimension_iff_range g c.val.left).mpr c.property⟩
  invFun c := ⟨c.val, ((SmoothHilbert.Parameter.smoothHilbertUniversalFamily S n P).pullback_dimension_iff_range g c.val.left).mp c.property⟩
  left_inv _ := Subtype.ext rfl
  right_inv _ := Subtype.ext rfl

def fixedDimensionHilbertMapFamilyEquiv :
    {c : T ⟶ SmoothHilbert.Parameter.smoothHilbertParameter S n P //
      SmoothOfRelativeDimension g ((SmoothHilbert.Parameter.smoothHilbertUniversalFamily S n P).pullback c.left).family.scheme.hom} ≃
      {F : SmoothHilbert.PointEquivalence.SmoothRelativeProjectiveHilbertFamily T.left n P // SmoothOfRelativeDimension g F.val.family.scheme.hom} :=
  (SmoothHilbert.PointEquivalence.smoothHilbertParameterPointEquiv S T n P).subtypeEquiv (by
    intro c
    rw [SmoothHilbert.UniversalProperty.smoothHilbertUniversalFamily_point S T n P c])

def fixedDimensionHilbertParameterPointEquiv :
    (T ⟶ Parameters.fixedDimensionHilbertParameter S n P g) ≃ Parameters.FixedDimensionRelativeProjectiveHilbertFamily T.left n P g :=
  (Open.ParameterPoints.openParameterPointEquiv (SmoothHilbert.Parameter.smoothHilbertParameter S n P)
    ((SmoothHilbert.Parameter.smoothHilbertUniversalFamily S n P).dimensionBaseOpen g) T).trans
      ((fixedDimensionHilbertRangeEquiv S T n P g).trans
        ((fixedDimensionHilbertMapFamilyEquiv S T n P g).trans (Parameters.fixedDimensionSmoothFamilyEquiv T.left n P g)))

theorem fixedDimensionHilbertParameterPointEquiv_val (y : T ⟶ Parameters.fixedDimensionHilbertParameter S n P g) :
    (fixedDimensionHilbertParameterPointEquiv S T n P g y).val =
      (SmoothHilbert.PointEquivalence.smoothHilbertParameterPointEquiv S T n P (y ≫ Parameters.fixedDimensionHilbertParameterInclusion S n P g)).val := rfl

theorem fixedDimensionHilbertUniversalFamily_point (y : T ⟶ Parameters.fixedDimensionHilbertParameter S n P g) :
    (Parameters.fixedDimensionHilbertUniversalFamily S n P g).pullback y.left =
      (fixedDimensionHilbertParameterPointEquiv S T n P g y).val :=
  ((SmoothHilbert.Parameter.smoothHilbertUniversalFamily S n P).pullback_comp (Parameters.fixedDimensionHilbertParameterInclusion S n P g).left y.left).trans
    (SmoothHilbert.UniversalProperty.smoothHilbertUniversalFamily_point S T n P (y ≫ Parameters.fixedDimensionHilbertParameterInclusion S n P g))

theorem fixedDimensionHilbertUniversalFamily_existsUnique (F : Parameters.FixedDimensionRelativeProjectiveHilbertFamily T.left n P g) :
    ∃! y : T ⟶ Parameters.fixedDimensionHilbertParameter S n P g,
      (Parameters.fixedDimensionHilbertUniversalFamily S n P g).pullback y.left = F.val := by
  let e := fixedDimensionHilbertParameterPointEquiv S T n P g
  refine ⟨e.symm F, (fixedDimensionHilbertUniversalFamily_point S T n P g (e.symm F)).trans
    (congrArg Subtype.val (e.apply_symm_apply F)), ?_⟩
  intro y hy
  apply e.injective
  exact (Subtype.ext ((fixedDimensionHilbertUniversalFamily_point S T n P g y).symm.trans hy)).trans
    (e.apply_symm_apply F).symm

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.FixedDimension.PointEquivalence
