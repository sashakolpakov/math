import OAI.NumberTheory.PadicHodge.IntegralComparison.Witt.RationalTorsion
import OAI.NumberTheory.PadicHodge.GeometricComparison.Finite.PowerTorsion

/-! # Rational Torsion Uniform -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Witt.RationalTorsionUniform

noncomputable section

/-! In a Noetherian Witt module, a family killed by fraction-field
extension has one uniform ordinary p-power annihilator. -/

open scoped TensorProduct

variable (p : ℕ) [Fact p.Prime] (k : Type*) [Field k] [CharP k p] [PerfectRing k p]
  {M : Type*} [AddCommGroup M] [Module (WittVector p k) M]
  [IsNoetherian (WittVector p k) M] {A : Type*}

 theorem exists_power (g : A → M)
    (hg : ∀ x, (1 : FractionRing (WittVector p k)) ⊗ₜ[WittVector p k] g x = 0) :
    ∃ b : ℕ, ∀ x, p^b • g x = 0 := by
  obtain ⟨b, hb⟩ := GeometricComparison.Finite.PowerTorsion.FinitePowerTorsion.bounded (M := M) (p : WittVector p k)
  refine ⟨b, fun x => ?_⟩
  obtain ⟨a, ha⟩ := (RationalTorsion.one_tmul_eq_zero_iff p k M (g x)).mp (hg x)
  have ha' : (p : WittVector p k)^a • g x = 0 := by
    simpa only [← Nat.cast_pow, Nat.cast_smul_eq_nsmul] using ha
  simpa only [← Nat.cast_pow, Nat.cast_smul_eq_nsmul] using hb (g x) ⟨a, ha'⟩

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Witt.RationalTorsionUniform
