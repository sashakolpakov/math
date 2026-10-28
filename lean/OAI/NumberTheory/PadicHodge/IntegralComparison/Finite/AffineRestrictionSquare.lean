import Mathlib.AlgebraicGeometry.Morphisms.Finite
import Mathlib.AlgebraicGeometry.Morphisms.Flat

/-! # Affine Restriction Square -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Finite.AffineRestrictionSquare

noncomputable section

/-! The actual cartesian square of section rings over nested affine opens
for an affine morphism. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry Opposite _root_.TopologicalSpace

universe u

variable {X Y : Scheme.{u}} (f : X ⟶ Y) [IsAffineHom f]
  {U V : Y.Opens} (hVU : V ≤ U) (hU : IsAffineOpen U) (hV : IsAffineOpen V)

include hU hV in
theorem isPushout : IsPushout (Y.presheaf.map (homOfLE hVU).op) (f.app U)
    (f.app V) (X.presheaf.map (homOfLE (show f ⁻¹ᵁ V ≤ f ⁻¹ᵁ U from
      (Opens.map f.base).monotone hVU)).op) := by
  let H : IsPullback (𝟙 X) f f (𝟙 Y) := IsPullback.id_horiz f
  have hleft : V ≤ (𝟙 Y) ⁻¹ᵁ U := by simpa using hVU
  have hright : f ⁻¹ᵁ U ≤ f ⁻¹ᵁ U := le_rfl
  have hbot : f ⁻¹ᵁ V = (𝟙 X) ⁻¹ᵁ (f ⁻¹ᵁ U) ⊓ f ⁻¹ᵁ V := by
    simpa using (inf_eq_right.mpr ((Opens.map f.base).monotone hVU)).symm
  let : IsIso (pushoutSection H hleft hright hbot) :=
    isIso_pushoutSection_of_isAffineOpen H hleft hright hbot hU hV (hU.preimage f)
  have hp := ((isIso_pushoutSection_iff H hleft hright hbot).mp inferInstance).flip
  convert hp using 1 <;> ext a <;> first | rfl | simp only [Scheme.Hom.appLE_eq_app]

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Finite.AffineRestrictionSquare
