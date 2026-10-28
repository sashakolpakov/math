import OAI.AlgebraicGeometry.HilbertScheme.Presentations.Localized.DegreePieces

/-! # Grading -/

namespace OAI.AlgebraicGeometry.HilbertScheme.Presentations.Localized.Grading.GradedModules

noncomputable section

/-! Localization at a homogeneous element has a genuine integer grading. -/

open DirectSum

universe u v w t

variable {R : Type u} [CommRing R] {A : Type v} [CommRing A] [Algebra R A]
variable {M : Type w} [AddCommGroup M] [Module R M] [Module A M] [IsScalarTower R A M]
variable (𝒜 : ℤ → Submodule R A) [GradedAlgebra 𝒜]
variable (ℳ : ℤ → Submodule R M) [SetLike.GradedSMul 𝒜 ℳ]

theorem localizedDegree_common_numerator {ι : Type t} [Fintype ι]
    (a : A) (e : ℤ) (ha : a ∈ 𝒜 e) (d : ι → ℤ) (f : ι → Presentations.Module.Fractions.GradedModules.AwayModule a M)
    (hf : ∀ i, f i ∈ DegreePieces.GradedModules.localizedDegreePiece ℳ a e (d i)) :
    ∃ (k : ℕ) (m : ι → M), ∀ i,
      m i ∈ ℳ (d i + (k : ℤ) * e) ∧ Presentations.Module.Fractions.GradedModules.moduleFractionMap (R := R) a k (m i) = f i := by
  classical
  choose k m hm he using fun i => (DegreePieces.GradedModules.mem_localizedDegreePiece_iff 𝒜 ℳ a e (ha) (d i) (f i)).mp (hf i)
  let K := ∑ i, k i
  have hK (i : ι) : k i ≤ K := Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ i)
  have hstage (i : ι) : f i ∈ DegreePieces.GradedModules.localizedDegreeStage ℳ a e (d i) K := by
    obtain ⟨l, hl⟩ := Nat.exists_eq_add_of_le (hK i)
    rw [hl]
    exact DegreePieces.GradedModules.localizedDegreeStage_le_add 𝒜 ℳ a e ha (d i) (k i) l ⟨m i, hm i, he i⟩
  choose m' hm' he' using hstage
  exact ⟨K, m', fun i => ⟨hm' i, he' i⟩⟩

variable [Decomposition ℳ]

theorem localizedDegree_finite_sum_zero {ι : Type t} [Fintype ι]
    (a : A) (e : ℤ) (ha : a ∈ 𝒜 e) (d : ι → ℤ) (hd : Function.Injective d)
    (f : ι → Presentations.Module.Fractions.GradedModules.AwayModule a M) (hf : ∀ i, f i ∈ DegreePieces.GradedModules.localizedDegreePiece ℳ a e (d i))
    (hsum : ∑ i, f i = 0) : ∀ i, f i = 0 := by
  obtain ⟨k, m, hm⟩ := localizedDegree_common_numerator 𝒜 ℳ a e ha d f hf
  have hzero : Presentations.Module.Fractions.GradedModules.moduleFractionMap (R := R) a k (∑ i, m i) = 0 := by
    rw [map_sum]
    simpa only [(hm _).2] using hsum
  obtain ⟨l, hl⟩ := (Presentations.Module.Fractions.GradedModules.moduleFractionMap_eq_zero (R := R) a k _).mp hzero
  rw [Finset.smul_sum] at hl
  have hmem (i : ι) : a ^ l • m i ∈ ℳ ((l : ℤ) * e + (d i + (k : ℤ) * e)) :=
    SetLike.GradedSMul.smul_mem (by simpa only [nsmul_eq_mul] using SetLike.pow_mem_graded l ha) (hm i).1
  have hinj : Function.Injective (fun i => (l : ℤ) * e + (d i + (k : ℤ) * e)) := by
    intro i j hij
    exact hd (add_right_cancel (add_left_cancel hij))
  have hind := (Decomposition.isInternal ℳ).submodule_iSupIndep.comp hinj
  have hz := (iSupIndep_iff_finsetSum_eq_zero_imp_eq_zero _).mp hind Finset.univ
    (fun i => a ^ l • m i) (fun i _ => hmem i) hl
  intro i
  rw [← (hm i).2, Presentations.Module.Fractions.GradedModules.moduleFractionMap_eq_zero]
  exact ⟨l, hz i (Finset.mem_univ i)⟩

theorem localizedDegree_iSupIndep (a : A) (e : ℤ) (ha : a ∈ 𝒜 e) :
    iSupIndep (DegreePieces.GradedModules.localizedDegreePiece ℳ a e) := by
  classical
  rw [iSupIndep_iff_finsetSum_eq_zero_imp_eq_zero]
  intro s f hf hsum i hi
  have hs : ∑ j : s, f j.val = 0 := by simpa only [s.sum_coe_sort] using hsum
  exact localizedDegree_finite_sum_zero 𝒜 ℳ a e ha
    (Subtype.val : s → ℤ) Subtype.val_injective (fun j => f j.val)
    (fun j => hf j.val j.property) hs ⟨i, hi⟩

theorem localizedDegree_iSup_eq_top (a : A) (e : ℤ) :
    (⨆ d, DegreePieces.GradedModules.localizedDegreePiece ℳ a e d) = ⊤ := by
  apply top_unique
  intro x hx
  clear hx
  obtain ⟨k, m, rfl⟩ := Presentations.Module.Fractions.GradedModules.moduleFractionMap_surj (R := R) a x
  induction m using Decomposition.inductionOn ℳ with
  | zero =>
    rw [map_zero]
    exact Submodule.zero_mem _
  | homogeneous m =>
    rename_i d
    apply (le_iSup (DegreePieces.GradedModules.localizedDegreePiece ℳ a e) (d - (k : ℤ) * e))
    apply DegreePieces.GradedModules.moduleFractionMap_mem_degree ℳ a e (d - (k : ℤ) * e) k m.val
    simpa only [sub_add_cancel] using m.property
  | add x y hx hy =>
    rw [map_add]
    exact Submodule.add_mem _ hx hy

@[instance_reducible]
def localizedDegreeDecomposition (a : A) (e : ℤ) (ha : a ∈ 𝒜 e) :
    Decomposition (DegreePieces.GradedModules.localizedDegreePiece ℳ a e) :=
  (DirectSum.isInternal_submodule_of_iSupIndep_of_iSup_eq_top
    (localizedDegree_iSupIndep 𝒜 ℳ a e ha) (localizedDegree_iSup_eq_top ℳ a e)).chooseDecomposition

end

end OAI.AlgebraicGeometry.HilbertScheme.Presentations.Localized.Grading.GradedModules
