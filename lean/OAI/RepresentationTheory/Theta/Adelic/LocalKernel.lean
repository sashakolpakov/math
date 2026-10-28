import OAI.RepresentationTheory.Weil.UnitarySplitting.UltraMultiplier
import OAI.RepresentationTheory.Weil.AdelicSplitting.Oscillator

/-! # Local Kernel -/

namespace OAI.RepresentationTheory.Theta.Adelic.LocalKernel

noncomputable section

/-! The scalar kernel of the actual AdelicSplitting local oscillator group.
The proof uses the checked nonarchimedean Heisenberg commutant theorem. -/

open OAI.RepresentationTheory.Weil.UnitarySplitting.UltraMultiplier.Construction
open OAI.RepresentationTheory.Weil.AdelicSplitting.Oscillator.Construction

variable {k : Type} [NormedField k] [IsUltrametricDist k] [CharZero k]
    [LocallyCompactSpace k] [MeasurableSpace k] [BorelSpace k]
    (hk : ¬ DiscreteTopology k) (N : ℕ)
    (ψ : AddChar k ℂ) (hc : Continuous (fun t : k => ψ t))
    (hu : ∀ t : k, ‖ψ t‖ = 1) (hn : ∃ t : k, ψ t ≠ 1)

theorem kernel_commutes (a : Weil.AdelicSplitting.Oscillator.Construction.LocalCover k N ψ)
    (ha : Weil.AdelicSplitting.Oscillator.Construction.localProjection k N ψ a = 1)
    (v : Weil.Local.FunctionsMetaplectic.Construction.PhaseSpace k N) (f : Weil.Local.FunctionsMetaplectic.Construction.schwartzBruhat k N) :
    a.val.2 (Weil.UnitarySplitting.UltraMultiplier.Construction.ultraHeisenbergOperator ψ hc v f) =
      Weil.UnitarySplitting.UltraMultiplier.Construction.ultraHeisenbergOperator ψ hc v (a.val.2 f) := by
  have hgraph : Weil.Local.FunctionsMetaplectic.Construction.heisenbergGraph ψ v f (Weil.UnitarySplitting.UltraMultiplier.Construction.ultraHeisenbergOperator ψ hc v f) := rfl
  have h := (a.property.2 v f (Weil.UnitarySplitting.UltraMultiplier.Construction.ultraHeisenbergOperator ψ hc v f)).mp hgraph
  change (a.val.2 (Weil.UnitarySplitting.UltraMultiplier.Construction.ultraHeisenbergOperator ψ hc v f)).val =
    Weil.Local.FunctionsMetaplectic.Construction.heisenbergFunction ψ (Weil.Local.FunctionsMetaplectic.Construction.symplecticAction a.val.1 v) (a.val.2 f).val at h
  change a.val.1 = 1 at ha
  rw [ha, Weil.Local.FunctionsMetaplectic.Construction.symplecticAction_one] at h
  exact Subtype.ext h

include hk hc hu hn in
theorem local_kernel_scalar (a : Weil.AdelicSplitting.Oscillator.Construction.LocalCover k N ψ)
    (ha : Weil.AdelicSplitting.Oscillator.Construction.localProjection k N ψ a = 1) :
    ∃ z : Circle, Weil.AdelicSplitting.Oscillator.Construction.localScalar k N ψ z = a := by
  obtain ⟨z, hz⟩ := Weil.UnitarySplitting.UltraMultiplier.Construction.ultra_commutant_scalar hk ψ hc hn hu a.val.2.toLinearMap
    (kernel_commutes N ψ hc a ha)
  let : SecondCountableTopology k := Weil.UnitarySplitting.TestSpaceAnalysis.Construction.localField_secondCountable k hk
  let f := Weil.UnitarySplitting.LocalTest.Construction.ultraTestVector k hk N
  have hfn : ‖Weil.UnitarySplitting.Weak.Construction.testToL2 k N f‖ ≠ 0 := by
    intro h
    apply Weil.UnitarySplitting.LocalTest.Construction.ultraTestVector_ne_zero k hk N
    apply Weil.UnitarySplitting.Weak.Construction.testToL2_injective k N
    rw [map_zero]
    exact norm_eq_zero.mp h
  have hnorm : ‖z‖ = 1 := by
    have h : ‖Weil.UnitarySplitting.Weak.Construction.testToL2 k N (a.val.2 f)‖ = ‖Weil.UnitarySplitting.Weak.Construction.testToL2 k N f‖ := by
      rw [Weil.UnitarySplitting.Weak.Construction.testToL2_norm, Weil.UnitarySplitting.Weak.Construction.testToL2_norm, a.property.1]
    rw [show a.val.2 f = z • f from hz f, map_smul, norm_smul] at h
    exact mul_right_cancel₀ hfn (h.trans (one_mul _).symm)
  refine ⟨⟨z, mem_sphere_zero_iff_norm.mpr hnorm⟩, ?_⟩
  apply Subtype.ext
  apply Prod.ext
  · exact ha.symm
  · apply LinearEquiv.ext
    intro f
    exact (hz f).symm

include hk hc hu hn in
theorem same_projection_operators
    (a b : Weil.AdelicSplitting.Oscillator.Construction.LocalCover k N ψ)
    (hab : Weil.AdelicSplitting.Oscillator.Construction.localProjection k N ψ a = Weil.AdelicSplitting.Oscillator.Construction.localProjection k N ψ b) :
    ∃ z : Circle, ∀ f : Weil.Local.FunctionsMetaplectic.Construction.schwartzBruhat k N,
      Weil.AdelicSplitting.Oscillator.Construction.localOperator k N ψ a f = (z : ℂ) • Weil.AdelicSplitting.Oscillator.Construction.localOperator k N ψ b f := by
  have hker : Weil.AdelicSplitting.Oscillator.Construction.localProjection k N ψ (a * b⁻¹) = 1 := by
    rw [map_mul, map_inv, hab, mul_inv_cancel]
  obtain ⟨z, hz⟩ := local_kernel_scalar hk N ψ hc hu hn (a * b⁻¹) hker
  have heq : a = Weil.AdelicSplitting.Oscillator.Construction.localScalar k N ψ z * b := by
    rw [hz]
    simp
  refine ⟨z, fun f => ?_⟩
  rw [heq, map_mul, LinearEquiv.mul_apply, Weil.AdelicSplitting.Oscillator.Construction.localOperator_scalar]

end

end OAI.RepresentationTheory.Theta.Adelic.LocalKernel
