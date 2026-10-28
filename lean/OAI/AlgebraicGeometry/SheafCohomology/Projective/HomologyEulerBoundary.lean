import OAI.AlgebraicGeometry.SheafCohomology.Projective.ExactSequenceFinrank

/-! # Homology Euler Boundary -/

namespace OAI.AlgebraicGeometry.SheafCohomology.Projective.HomologyEulerBoundary

noncomputable section

/-! The boundary term in the alternating homology sum of a short exact sequence. -/

open _root_.CategoryTheory
universe u v
variable {K : Type u} [Field K]
variable (S : ShortComplex (CochainComplex (ModuleCat.{v} K) ℕ))

def homologyEulerDefect (q : ℕ) : ℤ :=
  (Module.finrank K (S.X₁.homology q) : ℤ) -
    (Module.finrank K (S.X₂.homology q) : ℤ) +
    (Module.finrank K (S.X₃.homology q) : ℤ)

def homologyBoundaryRank (hS : S.ShortExact) (q : ℕ) : ℤ :=
  Module.finrank K (LinearMap.range (hS.δ q (q + 1) (by simp [ComplexShape.up_Rel])).hom)

variable {S}
variable [∀ q, Module.Finite K (S.X₁.homology q)]
variable [∀ q, Module.Finite K (S.X₂.homology q)]
variable [∀ q, Module.Finite K (S.X₃.homology q)]

omit [∀ q, Module.Finite K (S.X₁.homology q)] in
theorem homologyEulerDefect_zero (hS : S.ShortExact) :
    homologyEulerDefect S 0 = homologyBoundaryRank S hS 0 := by
  let : Mono S.f := hS.mono_f
  let : Mono (HomologicalComplex.homologyMap S.f 0) :=
    HomologicalComplex.mono_homologyMap_of_mono_of_not_rel S.f 0
      (by simp [ComplexShape.up_Rel])
  have hA := LinearMap.finrank_range_of_inj
    (f := (HomologicalComplex.homologyMap S.f 0).hom)
    ((ModuleCat.mono_iff_injective (HomologicalComplex.homologyMap S.f 0)).mp inferInstance)
  have hB := ExactSequenceFinrank.shortComplex_finrank_eq_ranges _ (hS.homology_exact₂ 0)
  have hC := ExactSequenceFinrank.shortComplex_finrank_eq_ranges _
    (hS.homology_exact₃ 0 1 (by simp [ComplexShape.up_Rel]))
  dsimp only at hB hC
  change (Module.finrank K (S.X₃.homology 0) : ℤ) =
    (Module.finrank K (LinearMap.range (HomologicalComplex.homologyMap S.g 0).hom) : ℤ) +
      homologyBoundaryRank S hS 0 at hC
  unfold homologyEulerDefect
  omega

theorem homologyEulerDefect_succ (hS : S.ShortExact) (q : ℕ) :
    homologyEulerDefect S (q + 1) =
      homologyBoundaryRank S hS q + homologyBoundaryRank S hS (q + 1) := by
  have hA := ExactSequenceFinrank.shortComplex_finrank_eq_ranges _
    (hS.homology_exact₁ q (q + 1) (by simp [ComplexShape.up_Rel]))
  have hB := ExactSequenceFinrank.shortComplex_finrank_eq_ranges _ (hS.homology_exact₂ (q + 1))
  have hC := ExactSequenceFinrank.shortComplex_finrank_eq_ranges _
    (hS.homology_exact₃ (q + 1) (q + 1 + 1) (by simp [ComplexShape.up_Rel]))
  dsimp only at hA hB hC
  unfold homologyEulerDefect homologyBoundaryRank
  omega

theorem alternating_homology_defect_eq_boundary (hS : S.ShortExact) (m : ℕ) :
    (∑ q ∈ Finset.range (m + 1), (-1 : ℤ) ^ q * homologyEulerDefect S q) =
      (-1 : ℤ) ^ m * homologyBoundaryRank S hS m := by
  induction m with
  | zero => simp [homologyEulerDefect_zero hS]
  | succ m ih =>
      rw [Finset.sum_range_succ, ih, homologyEulerDefect_succ hS m, pow_succ]
      ring

theorem alternating_homology_sum_add_of_vanish (hS : S.ShortExact) (m : ℕ)
    [Subsingleton (S.X₁.homology (m + 1))] :
    (∑ q ∈ Finset.range (m + 1),
      (-1 : ℤ) ^ q * (Module.finrank K (S.X₂.homology q) : ℤ)) =
    (∑ q ∈ Finset.range (m + 1),
      (-1 : ℤ) ^ q * (Module.finrank K (S.X₁.homology q) : ℤ)) +
    (∑ q ∈ Finset.range (m + 1),
      (-1 : ℤ) ^ q * (Module.finrank K (S.X₃.homology q) : ℤ)) := by
  have h := alternating_homology_defect_eq_boundary hS m
  have hboundary : homologyBoundaryRank S hS m = 0 := by
    unfold homologyBoundaryRank
    rw [Module.finrank_zero_of_subsingleton]
    rfl
  rw [hboundary, mul_zero] at h
  simp only [homologyEulerDefect, mul_add, mul_sub,
    Finset.sum_add_distrib, Finset.sum_sub_distrib] at h
  omega

end

end OAI.AlgebraicGeometry.SheafCohomology.Projective.HomologyEulerBoundary
