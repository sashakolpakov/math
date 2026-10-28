import OAI.RepresentationTheory.Hecke.RadialDilation.ActivePrimeSubstitution
import OAI.RepresentationTheory.Hecke.RadialDilation.IndexedPrimeBareLift

/-! # Active Prime Weil -/

namespace OAI.RepresentationTheory.Hecke.RadialDilation.ActivePrimeWeil.Realization

noncomputable section

/-! The active three-coordinate dilation has an actual finite-cover lift with the radial formula. -/

open scoped Classical _root_.Matrix

variable (q : ℕ) [Fact q.Prime] {Place : Type*} [Fintype Place] [DecidableEq Place]
  {n : ℕ} (e : (Place × Fin 3) ≃ Fin n) (μ : Place)
local instance c410ActivePrimeWeil_measurable : MeasurableSpace ℚ_[q] := borel ℚ_[q]
local instance c410ActivePrimeWeil_borel : BorelSpace ℚ_[q] := ⟨rfl⟩
variable {MpR MpF MpA : Type*} [Group MpR] [Group MpF] [Group MpA]

theorem activePrimeGL_modulus (a : ℚ_[q]ˣ) (M : ℕ)
    (ha : ‖(a : ℚ_[q])‖ = (q : ℝ) ^ (-(M : ℤ))) :
    Weil.Local.FunctionsMetaplectic.Construction.localModulus ℚ_[q] (Weil.Local.FunctionsMetaplectic.Construction.determinantUnit ℚ_[q] (ActivePrimeSubstitution.Realization.activePrimeGL q e μ a)) = ‖(a : ℚ_[q])‖ ^ 3 := by
  rw [ActivePrimeSubstitution.Realization.activePrimeGL_determinant]
  have hp : Weil.Local.FunctionsMetaplectic.Construction.localModulus ℚ_[q] (a ^ 3) = (Weil.Local.FunctionsMetaplectic.Construction.localModulus ℚ_[q] a) ^ 3 := by
    simp [Weil.Local.FunctionsMetaplectic.Construction.localModulus, map_pow]
  rw [hp, Haar.Realization.haarModulus_of_norm q a M ha]

theorem exists_active_prime_lift_radial_substitution
    (hLocalWeil : Prerequisites.Core.LocalWeil.Proposition)
    (D : Theta.PoissonAutomorphyNormalizationData.WeilData (Place × Fin 3) MpR MpF MpA) (a : ℚ_[q]ˣ) (M : ℕ)
    (ha : ‖(a : ℚ_[q])‖ = (q : ℝ) ^ (-(M : ℤ))) :
    ∃ (m : MpF) (ξ : ℂ),
      D.finite.project m = IndexedPrimePhaseAction.Realization.indexedPrimeSymplectic q e (Weil.Local.Generators.Construction.leviSymplectic (ActivePrimeSubstitution.Realization.activePrimeGL q e μ a)) ∧
      ξ ^ 8 = 1 ∧ ∀ b : Cm.radialInput q,
      D.finite.action m (Canonical.Realization.canonicalFiniteRadialEmbedding q μ b) =
        ξ • Canonical.Realization.canonicalFiniteRadialEmbedding q μ
          (Mem.Realization.normalizedScalarSubstitution q (a : ℚ_[q]) M ha b) := by
  have hn : 0 < n := by have hi := (e (μ, 0)).isLt; omega
  let ψ := FiniteSchur.Realization.finiteLocalCharacter q D
  obtain ⟨_, _, hgaussian, _, _, m, _, _, hm, _, _, hlinear, _, _, _⟩ :=
    hLocalWeil ℚ_[q] (LocalLiftChoice.Realization.padic_not_discrete q) n hn ψ (FiniteSchur.Realization.finiteLocalCharacter_continuous q D)
      (FiniteSchur.Realization.finiteLocalCharacter_unitary q D) (FiniteSchur.Realization.finiteLocalCharacter_nontrivial q D)
  let A := ActivePrimeSubstitution.Realization.activePrimeGL q e μ a
  let ξ := Weil.Local.FunctionsMetaplectic.Construction.gaussianIndex ℚ_[q] ψ (Weil.Local.FunctionsMetaplectic.Construction.determinantUnit ℚ_[q] A) / Weil.Local.FunctionsMetaplectic.Construction.gaussianIndex ℚ_[q] ψ 1
  have hphase : ξ ^ 8 = 1 := Weil.Local.Generators.Construction.index_ratio_eighth_power ℚ_[q] ψ _
    (hgaussian _ (Weil.Local.FunctionsMetaplectic.Construction.determinantUnit ℚ_[q] A).ne_zero).2.2 (hgaussian 1 one_ne_zero).2.2
  have hop : ∀ f : Weil.Local.FunctionsMetaplectic.Construction.schwartzBruhat ℚ_[q] n, ∀ x,
      (Weil.Local.FunctionsMetaplectic.Construction.weilRepresentation ℚ_[q] n ψ (m A) f).val x =
        (ξ * ((Real.sqrt (‖(a : ℚ_[q])‖ ^ 3))⁻¹ : ℂ)) * f.val (A⁻¹.val *ᵥ x) := by
    intro f x
    rw [hlinear, activePrimeGL_modulus q e μ a M ha]
  refine ⟨IndexedPrimeBareLift.Realization.indexedPrimeMetaplecticLift q e D (m A), ξ, ?_, hphase, ?_⟩
  · rw [(IndexedPrimeBareLift.Realization.indexedPrimeMetaplecticLift_spec q e D (m A)).1, hm]
  · intro b
    rw [(IndexedPrimeBareLift.Realization.indexedPrimeMetaplecticLift_spec q e D (m A)).2]
    apply Subtype.ext
    funext x
    have hb := ActivePrimeSubstitution.Realization.canonical_radial_block_substitution q μ a M ha b x
    rw [Complex.ofReal_inv] at hb
    rw [IndexedPrimeSubstitution.Realization.indexedPrimeOperatorHom_substitution q e _ _ _ hop,
      ActivePrimeSubstitution.Realization.activePrimeGL_inverse_substitution, mul_assoc, hb]
    rfl

end

end OAI.RepresentationTheory.Hecke.RadialDilation.ActivePrimeWeil.Realization
