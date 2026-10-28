import OAI.RepresentationTheory.Hecke.RadialDilation.ActiveFinitePhase
import OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.AuxiliaryRadialHecke

/-! # Auxiliary Active Phase -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.AuxiliaryActivePhase.Local

noncomputable section

/-! The active scalar substitution and its actual eighth-root phase hold
uniformly on radial inputs with any fixed auxiliary test function. -/

open scoped Classical _root_.Matrix
open OAI.RepresentationTheory.Hecke.RadialDilation.Cm OAI.RepresentationTheory.Hecke.RadialDilation.ActiveFinitePhase.Realization

variable (q : ℕ) [Fact q.Prime] {Place : Type} [Fintype Place] [DecidableEq Place]
  (μ : Place) (φ : RepresentationTheory.Hecke.RadialDilation.TestSections.Realization.lcCompactSpace (RepresentationTheory.Hecke.RadialDilation.FiniteBlockChart.Realization.FiniteAwayPosition q μ))

omit [DecidableEq Place] in
theorem auxiliary_radial_block_substitution (a : ℚ_[q]ˣ) (M : ℕ)
    (ha : ‖(a : ℚ_[q])‖ = (q : ℝ) ^ (-(M : ℤ))) (b : RepresentationTheory.Hecke.RadialDilation.Cm.radialInput q)
    (x : Place × Fin 3 → RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.AQf) :
    (((Real.sqrt (‖(a : ℚ_[q])‖ ^ 3))⁻¹ : ℝ) : ℂ) *
      (AuxiliaryRadialHecke.Local.auxiliaryFiniteRadialEmbedding q μ φ b).val ((RepresentationTheory.Hecke.RadialDilation.FiniteBlockChart.Realization.finiteBlockChart q μ).symm
        ((fun i => (a : ℚ_[q])⁻¹ * RepresentationTheory.Hecke.RadialDilation.FiniteBlockChart.Realization.finiteBlockProjection q μ x i), (RepresentationTheory.Hecke.RadialDilation.FiniteBlockChart.Realization.finiteBlockChart q μ x).2)) =
    (AuxiliaryRadialHecke.Local.auxiliaryFiniteRadialEmbedding q μ φ
      (RepresentationTheory.Hecke.RadialDilation.Mem.Realization.normalizedScalarSubstitution q (a : ℚ_[q]) M ha b)).val x := by
  change _ * (b.val ((RepresentationTheory.Hecke.RadialDilation.FiniteBlockChart.Realization.finiteBlockChart q μ ((RepresentationTheory.Hecke.RadialDilation.FiniteBlockChart.Realization.finiteBlockChart q μ).symm _)).1) *
      φ.val ((RepresentationTheory.Hecke.RadialDilation.FiniteBlockChart.Realization.finiteBlockChart q μ ((RepresentationTheory.Hecke.RadialDilation.FiniteBlockChart.Realization.finiteBlockChart q μ).symm _)).2)) = _
  rw [Homeomorph.apply_symm_apply]
  change _ * (b.val (fun i => (a : ℚ_[q])⁻¹ * RepresentationTheory.Hecke.RadialDilation.FiniteBlockChart.Realization.finiteBlockProjection q μ x i) *
      φ.val (RepresentationTheory.Hecke.RadialDilation.FiniteBlockChart.Realization.finiteBlockChart q μ x).2) =
    (_ * b.val (fun i => (a : ℚ_[q])⁻¹ * RepresentationTheory.Hecke.RadialDilation.FiniteBlockChart.Realization.finiteBlockProjection q μ x i)) *
      φ.val (RepresentationTheory.Hecke.RadialDilation.FiniteBlockChart.Realization.finiteBlockChart q μ x).2
  rw [Complex.ofReal_inv]
  ring

variable {n : ℕ} (e : (Place × Fin 3) ≃ Fin n)
variable {MpR MpF MpA : Type*} [Group MpR] [Group MpF] [Group MpA]
local instance : MeasurableSpace ℚ_[q] := borel ℚ_[q]
local instance : BorelSpace ℚ_[q] := ⟨rfl⟩

theorem exists_active_prime_lift_auxiliary_substitution
    (hLocalWeil : RepresentationTheory.Hecke.RadialDilation.Prerequisites.Core.LocalWeil.Proposition)
    (D : RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.WeilData (Place × Fin 3) MpR MpF MpA) (a : ℚ_[q]ˣ) (M : ℕ)
    (ha : ‖(a : ℚ_[q])‖ = (q : ℝ) ^ (-(M : ℤ))) :
    ∃ (m : MpF) (ξ : ℂ),
      D.finite.project m = RepresentationTheory.Hecke.RadialDilation.IndexedPrimePhaseAction.Realization.indexedPrimeSymplectic q e (RepresentationTheory.Weil.Local.Generators.Construction.leviSymplectic (RepresentationTheory.Hecke.RadialDilation.ActivePrimeSubstitution.Realization.activePrimeGL q e μ a)) ∧
      ξ ^ 8 = 1 ∧ ∀ b : RepresentationTheory.Hecke.RadialDilation.Cm.radialInput q,
      D.finite.action m (AuxiliaryRadialHecke.Local.auxiliaryFiniteRadialEmbedding q μ φ b) =
        ξ • AuxiliaryRadialHecke.Local.auxiliaryFiniteRadialEmbedding q μ φ
          (RepresentationTheory.Hecke.RadialDilation.Mem.Realization.normalizedScalarSubstitution q (a : ℚ_[q]) M ha b) := by
  have hn : 0 < n := by have hi := (e (μ, 0)).isLt; omega
  let ψ := RepresentationTheory.Hecke.RadialDilation.FiniteSchur.Realization.finiteLocalCharacter q D
  obtain ⟨_, _, hgaussian, _, _, m, _, _, hm, _, _, hlinear, _, _, _⟩ :=
    hLocalWeil ℚ_[q] (RepresentationTheory.Hecke.RadialDilation.LocalLiftChoice.Realization.padic_not_discrete q) n hn ψ (RepresentationTheory.Hecke.RadialDilation.FiniteSchur.Realization.finiteLocalCharacter_continuous q D)
      (RepresentationTheory.Hecke.RadialDilation.FiniteSchur.Realization.finiteLocalCharacter_unitary q D) (RepresentationTheory.Hecke.RadialDilation.FiniteSchur.Realization.finiteLocalCharacter_nontrivial q D)
  let A := RepresentationTheory.Hecke.RadialDilation.ActivePrimeSubstitution.Realization.activePrimeGL q e μ a
  let ξ := RepresentationTheory.Weil.Local.FunctionsMetaplectic.Construction.gaussianIndex ℚ_[q] ψ (RepresentationTheory.Weil.Local.FunctionsMetaplectic.Construction.determinantUnit ℚ_[q] A) / RepresentationTheory.Weil.Local.FunctionsMetaplectic.Construction.gaussianIndex ℚ_[q] ψ 1
  have hphase : ξ ^ 8 = 1 := RepresentationTheory.Weil.Local.Generators.Construction.index_ratio_eighth_power ℚ_[q] ψ _
    (hgaussian _ (RepresentationTheory.Weil.Local.FunctionsMetaplectic.Construction.determinantUnit ℚ_[q] A).ne_zero).2.2 (hgaussian 1 one_ne_zero).2.2
  have hop : ∀ f : RepresentationTheory.Weil.Local.FunctionsMetaplectic.Construction.schwartzBruhat ℚ_[q] n, ∀ x,
      (RepresentationTheory.Weil.Local.FunctionsMetaplectic.Construction.weilRepresentation ℚ_[q] n ψ (m A) f).val x =
        (ξ * ((Real.sqrt (‖(a : ℚ_[q])‖ ^ 3))⁻¹ : ℂ)) * f.val (A⁻¹.val *ᵥ x) := by
    intro f x
    rw [hlinear, RepresentationTheory.Hecke.RadialDilation.ActivePrimeWeil.Realization.activePrimeGL_modulus q e μ a M ha]
  refine ⟨RepresentationTheory.Hecke.RadialDilation.IndexedPrimeBareLift.Realization.indexedPrimeMetaplecticLift q e D (m A), ξ, ?_, hphase, ?_⟩
  · rw [(RepresentationTheory.Hecke.RadialDilation.IndexedPrimeBareLift.Realization.indexedPrimeMetaplecticLift_spec q e D (m A)).1, hm]
  · intro b
    rw [(RepresentationTheory.Hecke.RadialDilation.IndexedPrimeBareLift.Realization.indexedPrimeMetaplecticLift_spec q e D (m A)).2]
    apply Subtype.ext
    funext x
    have hb := auxiliary_radial_block_substitution q μ φ a M ha b x
    rw [Complex.ofReal_inv] at hb
    rw [RepresentationTheory.Hecke.RadialDilation.IndexedPrimeSubstitution.Realization.indexedPrimeOperatorHom_substitution q e _ _ _ hop,
      RepresentationTheory.Hecke.RadialDilation.ActivePrimeSubstitution.Realization.activePrimeGL_inverse_substitution, mul_assoc, hb]
    rfl

theorem every_active_finite_lift_auxiliary_phase
    (hLocalWeil : RepresentationTheory.Hecke.RadialDilation.Prerequisites.Core.LocalWeil.Proposition)
    (D : RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.WeilData (Place × Fin 3) MpR MpF MpA) (a : ℚ_[q]ˣ) (M : ℕ)
    (ha : ‖(a : ℚ_[q])‖ = (q : ℝ) ^ (-(M : ℤ))) (m : MpF)
    (hm : D.finite.project m = RepresentationTheory.Hecke.RadialDilation.ActiveFinitePhase.Realization.activeFiniteSymplectic q μ a) :
    ∃ ξ : ℂ, ξ ^ 8 = 1 ∧ ∀ b : RepresentationTheory.Hecke.RadialDilation.Cm.radialInput q,
      D.finite.action m (AuxiliaryRadialHecke.Local.auxiliaryFiniteRadialEmbedding q μ φ b) =
        ξ • AuxiliaryRadialHecke.Local.auxiliaryFiniteRadialEmbedding q μ φ
          (RepresentationTheory.Hecke.RadialDilation.Mem.Realization.normalizedScalarSubstitution q (a : ℚ_[q]) M ha b) := by
  obtain ⟨u, ξ, hu, hξ, hop⟩ := exists_active_prime_lift_auxiliary_substitution q μ φ
    (Fintype.equivFin (Place × Fin 3)) hLocalWeil D a M ha
  rw [RepresentationTheory.Hecke.RadialDilation.ActiveFinitePhase.Realization.indexed_activePrime_projection] at hu
  obtain ⟨ε, hε, he⟩ := RepresentationTheory.Hecke.RadialDilation.FiniteSchur.Realization.finite_lifts_differ_by_sign D m u (hm.trans hu.symm)
  refine ⟨ε * ξ, ?_, ?_⟩
  · have hε8 : ε ^ 8 = 1 := by
      rw [show (8 : ℕ) = 2 * 4 from rfl, pow_mul, hε, one_pow]
    rw [mul_pow, hε8, hξ, one_mul]
  · intro b
    rw [he, hop, smul_smul]

end

end OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.AuxiliaryActivePhase.Local
