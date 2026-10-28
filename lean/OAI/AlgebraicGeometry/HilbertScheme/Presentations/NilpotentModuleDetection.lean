import OAI.AlgebraicGeometry.HilbertScheme.Presentations.Quotient.TensorUnitMap
import Mathlib.RingTheory.Nilpotent.Basic

/-! # Nilpotent Module Detection -/

namespace OAI.AlgebraicGeometry.HilbertScheme.Presentations.NilpotentModuleDetection

noncomputable section

/-! Reduction modulo a nilpotent ideal detects the zero module, without
a finite generation assumption. -/

open TensorProduct

universe u v
variable {R : Type u} [CommRing R]
variable (M : Type v) [AddCommGroup M] [Module R M]

theorem nilpotent_smul_top_eq_top_subsingleton (I : Ideal R) (hI : IsNilpotent I)
    (h : I • (⊤ : Submodule R M) = ⊤) : Subsingleton M := by
  have hp : ∀ n : ℕ, I ^ n • (⊤ : Submodule R M) = ⊤ := by
    intro n
    induction n with
    | zero => simp
    | succ n ih => rw [pow_succ, Submodule.mul_smul, h, ih]
  obtain ⟨n, hn⟩ := hI
  have hz : (⊥ : Submodule R M) = ⊤ := by
    simpa only [hn, Ideal.zero_eq_bot, Submodule.bot_smul] using hp n
  have hm (m : M) : m = 0 := (Submodule.mem_bot R).mp (hz.symm ▸ Submodule.mem_top)
  exact ⟨fun x y => (hm x).trans (hm y).symm⟩

theorem nilpotent_quotientTensor_subsingleton (I : Ideal R) (hI : IsNilpotent I)
    [Subsingleton ((R ⧸ I) ⊗[R] M)] : Subsingleton M := by
  apply nilpotent_smul_top_eq_top_subsingleton M I hI
  apply top_unique
  intro m _
  exact (Quotient.TensorRelations.quotientTensor_one_eq_zero_iff M I m).mp (Subsingleton.elim _ _)

end

end OAI.AlgebraicGeometry.HilbertScheme.Presentations.NilpotentModuleDetection
