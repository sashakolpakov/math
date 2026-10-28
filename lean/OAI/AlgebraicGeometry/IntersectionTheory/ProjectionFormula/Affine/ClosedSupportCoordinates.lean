import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Affine.SupportFractions
import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Affine.FiltrationAvoidance

/-! # Closed Support Coordinates -/

namespace OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Affine.ClosedSupportCoordinates

noncomputable section

/-! The kernel of the actual affine coordinate restriction is the
prime whose generic point maps to the original reduced support. -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace

variable {X Y : Scheme} [IsIntegral Y] (f : Y ⟶ X) [IsClosedImmersion f]
  (U : X.Opens) (hU : IsAffineOpen U) [Nonempty (f ⁻¹ᵁ U)]

def prime : PrimeSpectrum Γ(X, U) :=
  ⟨RingHom.ker (f.app U).hom, Ideal.isPrime_bot.comap (f.app U).hom⟩

theorem point : hU.fromSpec (prime f U) = f (genericPoint Y) := by
  let V := f ⁻¹ᵁ U
  let hV := hU.preimage f
  have hs : Spec.map (f.app U) ≫ hU.fromSpec = hV.fromSpec ≫ f := by
    simpa only [Scheme.Hom.appLE_eq_app] using hU.SpecMap_appLE_fromSpec f hV le_rfl
  have hp : (Spec.map (f.app U)) (genericPoint (Spec Γ(Y, V))) = prime f U := by
    rw [genericPoint_eq_bot_of_affine]
    rfl
  have he := congrArg (fun t : Spec Γ(Y, V) ⟶ X => t (genericPoint (Spec Γ(Y, V)))) hs
  change hU.fromSpec ((Spec.map (f.app U)) (genericPoint (Spec Γ(Y, V)))) =
    f (hV.fromSpec (genericPoint (Spec Γ(Y, V)))) at he
  rw [hp, genericPoint_eq_of_isOpenImmersion hV.fromSpec] at he
  exact he

omit [IsClosedImmersion f] in
theorem not_mem (a : Γ(X, U)) (ha : f.app U a ≠ 0) : a ∉ (prime f U).asIdeal := ha

theorem support (W : IrreducibleCloseds X) (hW : f (genericPoint Y) = CycleClass.Thom.IntersectionGeometry.supportPoint W) :
    FiltrationAvoidance.support hU.fromSpec (prime f U) = W := by
  unfold FiltrationAvoidance.support
  rw [point f U hU, hW]
  exact irreducibleSetEquivPoints.symm_apply_apply W

end

end OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Affine.ClosedSupportCoordinates
