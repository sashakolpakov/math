import Mathlib.AlgebraicGeometry.Geometrically.Integral
import Mathlib.AlgebraicGeometry.Morphisms.SchemeTheoreticallyDominant
import Mathlib.AlgebraicGeometry.Restrict

/-! # Geometric Dense -/

namespace OAI.AlgebraicGeometry.Quotients.FiniteDescent.GeometricDense

noncomputable section

/-! Geometric integrality extends from a dense quasi-compact open in an
integral scheme. Flat base change preserves the schematically dense open. -/

set_option backward.isDefEq.respectTransparency false

open _root_.AlgebraicGeometry _root_.CategoryTheory _root_.CategoryTheory.Limits

universe u

namespace Construction.GeometricDenseOpen

theorem integral_of_schematicallyDominant {X Y : Scheme.{u}} (f : X ⟶ Y)
    [IsSchemeTheoreticallyDominant f] [QuasiCompact f] [IsIntegral X] : IsIntegral Y := by
  have : IsReduced Y := IsSchemeTheoreticallyDominant.isReduced f
  have : IrreducibleSpace Y := by
    apply (irreducibleSpace_def Y).mpr
    have h := (IrreducibleSpace.isIrreducible_univ X).image f f.continuous.continuousOn
    rw [Set.image_univ] at h
    have hc := h.closure
    rw [f.denseRange.closure_range] at hc
    exact hc
  exact isIntegral_of_irreducibleSpace_of_isReduced Y

variable {K : Type u} [Field K] {X : Scheme.{u}} [IsIntegral X]
variable (f : X ⟶ Spec (.of K)) (U : X.Opens) [Nonempty U] [QuasiCompact U.ι]
variable [GeometricallyIntegral (U.ι ≫ f)]

include U

theorem geometricallyIntegral : GeometricallyIntegral f := by
  have : IsDominant U.ι := ⟨U.ι.isOpenMap.denseRange_of_isPreirreducibleSpace U.ι⟩
  have : IsSchemeTheoreticallyDominant U.ι := IsSchemeTheoreticallyDominant.of_isDominant U.ι
  constructor
  intro L _ t Y p q h
  have : Flat t := inferInstance
  have : Flat p := MorphismProperty.of_isPullback h.flip ‹Flat t›
  let V := p ⁻¹ᵁ U
  let H := isPullback_morphismRestrict p U
  have : IsIntegral V.toScheme :=
    GeometricallyIntegral.geometrically_isIntegral t (p ∣_ U) (V.ι ≫ q) (H.paste_vert h)
  have : IsSchemeTheoreticallyDominant V.ι := IsSchemeTheoreticallyDominant.of_isPullback H
  have : QuasiCompact V.ι := MorphismProperty.of_isPullback H ‹QuasiCompact U.ι›
  exact integral_of_schematicallyDominant V.ι

end Construction.GeometricDenseOpen

end

end OAI.AlgebraicGeometry.Quotients.FiniteDescent.GeometricDense
