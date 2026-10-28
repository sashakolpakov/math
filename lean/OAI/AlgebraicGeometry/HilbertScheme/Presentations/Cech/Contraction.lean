import OAI.AlgebraicGeometry.HilbertScheme.Presentations.Cech.Signs

/-! # Contraction -/

namespace OAI.AlgebraicGeometry.HilbertScheme.Presentations.Cech.Contraction.ProjectiveCech

/-! An explicit contraction of the finite subset Čech cochain complex. -/

universe u v

variable {σ : Type u} [LinearOrder σ]
variable (R : Type v) [CommRing R]

def cechDifferential (f : Finset σ → R) (s : Finset σ) : R :=
  ∑ i ∈ s, Signs.ProjectiveCech.alternatingSign R s i * f (s.erase i)

def cechContraction (j : σ) (f : Finset σ → R) (s : Finset σ) : R :=
  if j ∈ s then 0 else Signs.ProjectiveCech.alternatingSign R s j * f (insert j s)

theorem cechDifferential_contraction_of_mem (j : σ) (f : Finset σ → R)
    (s : Finset σ) (hj : j ∈ s) :
    cechDifferential R (cechContraction R j f) s = f s := by
  unfold cechDifferential
  rw [Finset.sum_eq_single j]
  · simp only [cechContraction, Finset.notMem_erase, ↓reduceIte, Finset.insert_erase hj,
      Signs.ProjectiveCech.alternatingSign_erase_self, ← mul_assoc, Signs.ProjectiveCech.alternatingSign_square, one_mul]
  · intro i hi hij
    have hj' : j ∈ s.erase i := Finset.mem_erase.mpr ⟨hij.symm, hj⟩
    simp only [cechContraction, ite_eq_left hj', mul_zero]
  · exact fun h => (h hj).elim

theorem cechContraction_differential_of_notMem (j : σ) (f : Finset σ → R)
    (s : Finset σ) (hj : j ∉ s) :
    cechContraction R j (cechDifferential R f) s =
      f s - cechDifferential R (cechContraction R j f) s := by
  rw [cechContraction, ite_eq_right hj, cechDifferential, Finset.sum_insert hj, mul_add]
  have hfirst : Signs.ProjectiveCech.alternatingSign R s j *
      (Signs.ProjectiveCech.alternatingSign R (insert j s) j * f ((insert j s).erase j)) = f s := by
    rw [Signs.ProjectiveCech.alternatingSign_insert_self, Finset.erase_insert hj, ← mul_assoc,
      Signs.ProjectiveCech.alternatingSign_square, one_mul]
  rw [hfirst, sub_eq_add_neg]
  congr 1
  rw [Finset.mul_sum, cechDifferential, ← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro i hi
  have hji : j ≠ i := fun h => hj (h ▸ hi)
  have hjs : j ∉ s.erase i := fun h => hj (Finset.mem_of_mem_erase h)
  rw [cechContraction, ite_eq_right hjs, ← mul_assoc, Signs.ProjectiveCech.alternatingSign_insert_erase R hi hj]
  rw [Finset.erase_insert_of_ne hji]
  ring

theorem cech_contraction_identity (j : σ) (f : Finset σ → R) (s : Finset σ) :
    cechDifferential R (cechContraction R j f) s +
      cechContraction R j (cechDifferential R f) s = f s := by
  by_cases hj : j ∈ s
  · rw [cechDifferential_contraction_of_mem R j f s hj, cechContraction, ite_eq_left hj, add_zero]
  · rw [cechContraction_differential_of_notMem R j f s hj]
    ring

theorem cech_cocycle_is_coboundary (j : σ) (f : Finset σ → R)
    (hf : cechDifferential R f = 0) :
    cechDifferential R (cechContraction R j f) = f := by
  funext s
  have h := cech_contraction_identity R j f s
  rw [hf] at h
  simpa only [cechContraction, Pi.zero_apply, mul_zero, ite_self, add_zero] using h

theorem cechContraction_preserves_support (j : σ) (N : Finset σ) (hj : j ∉ N)
    (f : Finset σ → R) (hf : ∀ s, ¬N ⊆ s → f s = 0) :
    ∀ s, ¬N ⊆ s → cechContraction R j f s = 0 := by
  intro s hs
  have hNs : ¬N ⊆ insert j s := by
    intro h
    apply hs
    intro i hi
    rcases Finset.mem_insert.mp (h hi) with hij | his
    · exact (hj (hij ▸ hi)).elim
    · exact his
  simp only [cechContraction, hf _ hNs, mul_zero, ite_self]

theorem cechContraction_card_support (j : σ) (q : ℕ) (f : Finset σ → R)
    (hf : ∀ s, s.card ≠ q + 1 → f s = 0) :
    ∀ s, s.card ≠ q → cechContraction R j f s = 0 := by
  intro s hs
  by_cases hj : j ∈ s
  · simp only [cechContraction, ite_eq_left hj]
  · have hc : (insert j s).card ≠ q + 1 := by
      rw [Finset.card_insert_of_notMem hj]
      exact fun h => hs (Nat.add_right_cancel h)
    simp only [cechContraction, ite_eq_right hj, hf _ hc, mul_zero]

end OAI.AlgebraicGeometry.HilbertScheme.Presentations.Cech.Contraction.ProjectiveCech
