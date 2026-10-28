import OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.LocalUnitTest
import OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.PadicIntegralSymplectic

/-! # Local Unit Lift -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.LocalUnitLift

noncomputable section

/-! Every actual metaplectic lift of an integral symplectic matrix
preserves the local unit-ball line, with a nonzero scalar. -/

open scoped Classical _root_.Matrix

variable (q : ℕ) [Fact q.Prime] (n : ℕ)

local instance localUnitLiftMeasurableSpace : MeasurableSpace ℚ_[q] := borel ℚ_[q]
local instance localUnitLiftBorelSpace : BorelSpace ℚ_[q] := ⟨rfl⟩

theorem integral_local_lift_unitTest
    (hq : 2 < q) (ψ : AddChar ℚ_[q] ℂ) (hψ : ∀ x, ψ x = 1 ↔ ‖x‖ ≤ 1)
    (g : RepresentationTheory.Weil.Local.FunctionsMetaplectic.Construction.Metaplectic ℚ_[q] n ψ)
    (hg : ∀ i j, ‖(RepresentationTheory.Weil.Local.FunctionsMetaplectic.Construction.metaplecticProjection ℚ_[q] n ψ g).val i j‖ ≤ 1) :
    ∃ c : ℂ, c ≠ 0 ∧
      RepresentationTheory.Weil.Local.FunctionsMetaplectic.Construction.weilRepresentation ℚ_[q] n ψ g (LocalUnitTest.padicUnitTest q n) = c • LocalUnitTest.padicUnitTest q n := by
  let S := RepresentationTheory.Weil.Local.FunctionsMetaplectic.Construction.metaplecticProjection ℚ_[q] n ψ g
  let U := RepresentationTheory.Weil.Local.FunctionsMetaplectic.Construction.weilRepresentation ℚ_[q] n ψ g
  let f := LocalUnitTest.padicUnitTest q n
  have hinv (v : RepresentationTheory.Weil.Local.FunctionsMetaplectic.Construction.PhaseSpace ℚ_[q] n) (hv : ∀ i, ‖v i‖ ≤ 1) :
      RepresentationTheory.Weil.Local.FunctionsMetaplectic.Construction.heisenbergFunction ψ v (U f).val = (U f).val := by
    let w := RepresentationTheory.Weil.Local.FunctionsMetaplectic.Construction.symplecticAction S⁻¹ v
    have hw : ∀ i, ‖w i‖ ≤ 1 :=
      PadicIntegralSymplectic.Local.padic_matrix_mulVec_integral q (S⁻¹).val (PadicIntegralSymplectic.Local.padic_symplectic_inverse_integral q S hg) v hv
    have hf : RepresentationTheory.Weil.Local.FunctionsMetaplectic.Construction.heisenbergGraph ψ w f f :=
      (LocalUnitTest.padicUnitIndicator_heisenberg q n hq ψ hψ w hw).symm
    have ht := (RepresentationTheory.Weil.Local.FunctionsMetaplectic.Construction.weilRepresentation_intertwines ℚ_[q] n ψ g w f f).mp hf
    change (U f).val = RepresentationTheory.Weil.Local.FunctionsMetaplectic.Construction.heisenbergFunction ψ (RepresentationTheory.Weil.Local.FunctionsMetaplectic.Construction.symplecticAction S w) (U f).val at ht
    have hc : RepresentationTheory.Weil.Local.FunctionsMetaplectic.Construction.symplecticAction S w = v := RepresentationTheory.Weil.Local.FunctionsMetaplectic.Construction.symplecticAction_inv_cancel S v
    rw [hc] at ht
    exact ht.symm
  let c := (U f).val 0
  have heq : U f = c • f := by
    apply Subtype.ext
    funext x
    exact LocalUnitTest.integral_heisenberg_fixed_scalar q n ψ hψ (U f).val hinv x
  have hf0 : f ≠ 0 := by
    intro h
    have h0 := congrArg (fun t : RepresentationTheory.Weil.Local.FunctionsMetaplectic.Construction.schwartzBruhat ℚ_[q] n => t.val 0) h
    change (LocalUnitTest.padicUnitTest q n).val 0 = 0 at h0
    rw [LocalUnitTest.padicUnitTest_zero] at h0
    exact one_ne_zero h0
  refine ⟨c, ?_, heq⟩
  intro hc
  apply hf0
  apply U.injective
  rw [heq, hc, zero_smul, map_zero]

end

end OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.LocalUnitLift
