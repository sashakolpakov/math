import OAI.AlgebraicGeometry.HilbertScheme.Presentations.CompatibleAdicIdeals
import Mathlib.RingTheory.AdicCompletion.Noetherian

/-! # Adic Ideal Separation -/

namespace OAI.AlgebraicGeometry.HilbertScheme.Presentations.AdicIdealSeparation

noncomputable section

/-! In a Noetherian complete ring, all ideals are separated in the adic
topology. Consequently compatible formal ideals retain their universal
ideal-containment criterion. -/

universe u
variable {R : Type u} [CommRing R] [IsNoetherianRing R]
variable (I : Ideal R) (hI : I ≤ Ideal.jacobson (⊥ : Ideal R))

include hI in
theorem adic_ideal_separated (K : Ideal R) : (⨅ n : ℕ, K ⊔ I ^ n) = K := by
  apply le_antisymm ?_ (le_iInf fun _ => le_sup_left)
  intro x hx
  have hxn : ∀ n, x ∈ K ⊔ I ^ n := Ideal.mem_iInf.mp hx
  let : IsHausdorff I (R ⧸ K) := IsHausdorff.of_le_jacobson I (R ⧸ K) hI
  apply Ideal.Quotient.eq_zero_iff_mem.mp
  apply IsHausdorff.haus (I := I) (M := R ⧸ K) inferInstance
  intro n
  apply SModEq.zero.mpr
  obtain ⟨k, hk, y, hy, hky⟩ := Submodule.mem_sup.mp (hxn n)
  change K.mkQ x ∈ I ^ n • (⊤ : Submodule R (R ⧸ K))
  have hk0 : K.mkQ k = 0 := (Submodule.Quotient.mk_eq_zero K).mpr hk
  rw [← hky, map_add, hk0, zero_add]
  have he : K.mkQ y = y • K.mkQ (1 : R) := by
    rw [← LinearMap.map_smul, smul_eq_mul, mul_one]
  rw [he]
  exact Submodule.smul_mem_smul hy Submodule.mem_top

include hI in
theorem adic_ideal_le_iff (J K : Ideal R) :
    J ≤ K ↔ ∀ n : ℕ, J ≤ K ⊔ I ^ n := by
  constructor
  · exact fun h _ => h.trans le_sup_left
  · intro h
    rw [← adic_ideal_separated I hI K]
    exact le_iInf h

variable [IsAdicComplete I R]

theorem compatibleAdicIdeals_le_iff (J : ℕ → Ideal R)
    (hpow : ∀ n, I ^ n ≤ J n) (hstep : ∀ n, J (n + 1) ⊔ I ^ n = J n)
    (K : Ideal R) :
    (⨅ n, J n) ≤ K ↔ ∀ n, J n ≤ K ⊔ I ^ n := by
  constructor
  · intro h n
    rw [← CompatibleAdicIdeals.compatibleAdicIdeals_intersection I J hpow hstep n]
    exact sup_le_sup_right h _
  · intro h
    apply (adic_ideal_le_iff I (IsAdicComplete.le_jacobson_bot I) _ K).mpr
    intro n
    exact (iInf_le J n).trans (h n)

end

end OAI.AlgebraicGeometry.HilbertScheme.Presentations.AdicIdealSeparation
