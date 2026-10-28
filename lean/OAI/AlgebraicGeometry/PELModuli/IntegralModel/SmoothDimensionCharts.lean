import OAI.AlgebraicGeometry.PELModuli.IntegralModel.SmoothRelativeDimension

/-! # Smooth Dimension Charts -/

namespace OAI.AlgebraicGeometry.PELModuli.IntegralModel.SmoothDimensionCharts.DimensionSupport

noncomputable section

/-! Smooth charts with a fixed relative dimension around each point. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

/-- A standard smooth affine chart gives a scheme morphism of the same
relative dimension. -/
theorem smoothOfRelativeDimension_resLE_of_appLE
    {X Y : Scheme} (f : X ⟶ Y) (n : ℕ)
    (U : Y.Opens) (V : X.Opens) (hU : IsAffineOpen U) (hV : IsAffineOpen V)
    (e : V ≤ f ⁻¹ᵁ U)
    (hstd : RingHom.IsStandardSmoothOfRelativeDimension n (f.appLE U V e).hom) :
    SmoothOfRelativeDimension n (f.resLE U V e) := by
  have : IsAffine U := hU
  have : IsAffine V := hV
  rw [HasRingHomProperty.iff_of_isAffine (P := @SmoothOfRelativeDimension n)]
  apply RingHom.locally_of (RingHom.isStandardSmoothOfRelativeDimension_respectsIso (n := n))
  have : (RingHom.toMorphismProperty
      (RingHom.IsStandardSmoothOfRelativeDimension n)).RespectsIso :=
    RingHom.toMorphismProperty_respectsIso_iff.mp
      (RingHom.isStandardSmoothOfRelativeDimension_respectsIso (n := n))
  exact (MorphismProperty.arrow_mk_iso_iff
    (RingHom.toMorphismProperty (RingHom.IsStandardSmoothOfRelativeDimension n))
    (arrowResLEAppIso f U V e)).mpr hstd

/-- Every point of a smooth morphism has an affine chart with one fixed
relative dimension. -/
theorem exists_smoothOfRelativeDimension_chart
    {X Y : Scheme} (f : X ⟶ Y) [Smooth f] (x : X) :
    ∃ (n : ℕ) (U : Y.Opens) (V : X.Opens),
      IsAffineOpen U ∧ IsAffineOpen V ∧ x ∈ V ∧
      ∃ e : V ≤ f ⁻¹ᵁ U, SmoothOfRelativeDimension n (f.resLE U V e) := by
  obtain ⟨U, hU, V, hV, hx, e, hstd⟩ := Smooth.exists_isStandardSmooth f x
  let : Algebra Γ(Y, U) Γ(X, V) := (f.appLE U V e).hom.toAlgebra
  change Algebra.IsStandardSmooth Γ(Y, U) Γ(X, V) at hstd
  obtain ⟨ι, σ, hσ, hι, ⟨P⟩⟩ := hstd
  let := hσ
  let := hι
  have hP := P.isStandardSmoothOfRelativeDimension rfl
  refine ⟨P.dimension, U, V, hU, hV, hx, e, ?_⟩
  exact smoothOfRelativeDimension_resLE_of_appLE f P.dimension U V hU hV e hP

end

end OAI.AlgebraicGeometry.PELModuli.IntegralModel.SmoothDimensionCharts.DimensionSupport
