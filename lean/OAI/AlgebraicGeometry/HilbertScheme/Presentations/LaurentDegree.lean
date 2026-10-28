import OAI.AlgebraicGeometry.HilbertScheme.Presentations.LaurentRestriction

/-! # Laurent Degree -/

namespace OAI.AlgebraicGeometry.HilbertScheme.Presentations.LaurentDegree.ProjectiveCech

noncomputable section

/-! Integer degrees and homogeneous pieces of the projective chart localizations. -/

universe u v

variable {σ : Type u} [Fintype σ] [DecidableEq σ]
variable (R : Type v) [CommRing R]

def exponentDegree (a : σ → ℤ) : ℤ := ∑ i, a i

def negativeSupport (a : σ → ℤ) : Finset σ := Finset.univ.filter (fun i => a i < 0)

omit [DecidableEq σ] in
theorem negativeSupport_subset_iff (a : σ → ℤ) (s : Finset σ) :
    negativeSupport a ⊆ s ↔ ∀ i ∉ s, 0 ≤ a i := by
  constructor
  · intro h i hi
    by_contra hn
    exact hi (h (Finset.mem_filter.mpr ⟨Finset.mem_univ i, lt_of_not_ge hn⟩))
  · intro h i hi
    have ha := (Finset.mem_filter.mp hi).2
    by_contra his
    exact (not_lt_of_ge (h i his)) ha

omit [DecidableEq σ] in
theorem nonnegative_coordinate_exists [Nonempty σ] (a : σ → ℤ) (ha : 0 ≤ exponentDegree a) :
    ∃ i, 0 ≤ a i := by
  by_contra hn
  have hneg : ∀ i, a i < 0 := fun i => lt_of_not_ge (fun h => hn ⟨i, h⟩)
  have hs : ∑ i, a i < ∑ _i : σ, (0 : ℤ) :=
    Finset.sum_lt_sum (fun i _ => (hneg i).le)
      ⟨Classical.arbitrary σ, Finset.mem_univ _, hneg _⟩
  simp only [Finset.sum_const_zero] at hs
  exact (not_lt_of_ge ha) hs

omit [DecidableEq σ] in
theorem exists_outside_negativeSupport [Nonempty σ] (a : σ → ℤ) (ha : 0 ≤ exponentDegree a) :
    ∃ i, i ∉ negativeSupport a := by
  obtain ⟨i, hi⟩ := nonnegative_coordinate_exists a ha
  exact ⟨i, fun h => (not_lt_of_ge hi) (Finset.mem_filter.mp h).2⟩

def laurentDegreeSubmodule (s : Finset σ) (d : ℤ) : Submodule R (LaurentMonomials.ProjectiveCech.ChartLocalization R s) :=
  Submodule.span R ((LaurentBasis.ProjectiveCech.laurentBasis R s) '' {a : LaurentExponents.ProjectiveCech.LaurentExponent s | exponentDegree a.val = d})

theorem mem_laurentDegreeSubmodule_iff (s : Finset σ) (d : ℤ) (x : LaurentMonomials.ProjectiveCech.ChartLocalization R s) :
    x ∈ laurentDegreeSubmodule R s d ↔
      ∀ a, exponentDegree a.val ≠ d → (LaurentBasis.ProjectiveCech.laurentBasis R s).repr x a = 0 := by
  rw [laurentDegreeSubmodule, (LaurentBasis.ProjectiveCech.laurentBasis R s).mem_span_image]
  constructor
  · intro h a ha
    by_contra hn
    exact ha (h (Finsupp.mem_support_iff.mpr hn))
  · intro h a ha
    by_contra hn
    exact (Finsupp.mem_support_iff.mp ha) (h a hn)

theorem laurentMonomial_mem_degree (s : Finset σ) (a : LaurentExponents.ProjectiveCech.LaurentExponent s) :
    LaurentMonomials.ProjectiveCech.laurentMonomial R a ∈ laurentDegreeSubmodule R s (exponentDegree a.val) := by
  rw [← LaurentBasis.ProjectiveCech.laurentBasis_apply R s a]
  exact Submodule.subset_span ⟨a, rfl, rfl⟩

theorem chartRestriction_preserves_degree {s t : Finset σ} (h : s ⊆ t) (d : ℤ)
    (x : LaurentMonomials.ProjectiveCech.ChartLocalization R s) (hx : x ∈ laurentDegreeSubmodule R s d) :
    LaurentRestriction.ProjectiveCech.chartRestriction R h x ∈ laurentDegreeSubmodule R t d := by
  apply Submodule.span_induction (p := fun x _ => LaurentRestriction.ProjectiveCech.chartRestriction R h x ∈ laurentDegreeSubmodule R t d)
    ?_ ?_ ?_ ?_ hx
  · intro y hy
    obtain ⟨a, ha, rfl⟩ := hy
    rw [LaurentBasis.ProjectiveCech.laurentBasis_apply, LaurentRestriction.ProjectiveCech.chartRestriction_laurentMonomial]
    exact ha ▸ laurentMonomial_mem_degree R t (LaurentRestriction.ProjectiveCech.extendExponent h a)
  · rw [map_zero]
    exact Submodule.zero_mem _
  · intro x y _ _ hx hy
    rw [map_add]
    exact Submodule.add_mem _ hx hy
  · intro r x _ hx
    rw [map_smul]
    exact Submodule.smul_mem _ r hx

end

end OAI.AlgebraicGeometry.HilbertScheme.Presentations.LaurentDegree.ProjectiveCech
