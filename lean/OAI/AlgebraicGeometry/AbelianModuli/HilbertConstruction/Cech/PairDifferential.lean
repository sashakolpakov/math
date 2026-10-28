import OAI.AlgebraicGeometry.HilbertScheme.Presentations.ModuleCech.Terms

/-! # Pair Differential -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Cech.PairDifferential

noncomputable section

/-! The first homogeneous Čech differential expresses equality of the two chart restrictions on a pairwise overlap. -/

open OAI.AlgebraicGeometry.HilbertScheme.Presentations.ModuleCech.Terms.ProjectiveCech

universe u v w

variable {σ : Type u} [LinearOrder σ] (R : Type v) [CommRing R]
variable (M : Type w) [AddCommGroup M] [Module R M] [Module (MvPolynomial σ R) M]
  [IsScalarTower R (MvPolynomial σ R) M]

def moduleCechPairRestrictionLeft (i j : σ) : HilbertScheme.Presentations.Graded.ModuleRestriction.ProjectiveCech.ModuleChart R M {i} →ₗ[R] HilbertScheme.Presentations.Graded.ModuleRestriction.ProjectiveCech.ModuleChart R M {i, j} :=
  HilbertScheme.Presentations.Graded.ModuleRestriction.ProjectiveCech.moduleChartRestriction R M (Finset.singleton_subset_iff.mpr (Finset.mem_insert_self i {j}))

def moduleCechPairRestrictionRight (i j : σ) : HilbertScheme.Presentations.Graded.ModuleRestriction.ProjectiveCech.ModuleChart R M {j} →ₗ[R] HilbertScheme.Presentations.Graded.ModuleRestriction.ProjectiveCech.ModuleChart R M {i, j} :=
  HilbertScheme.Presentations.Graded.ModuleRestriction.ProjectiveCech.moduleChartRestriction R M (Finset.singleton_subset_iff.mpr (Finset.mem_insert_of_mem (Finset.mem_singleton_self j)))

theorem moduleCechDifferential_pair (f : HilbertScheme.Presentations.ModuleCech.Card.ProjectiveCech.ModuleCechFamily (σ := σ) R M) {i j : σ} (hij : i < j) :
    HilbertScheme.Presentations.ModuleCech.Card.ProjectiveCech.moduleCechDifferential R M f {i, j} =
      moduleCechPairRestrictionRight R M i j (f {j}) - moduleCechPairRestrictionLeft R M i j (f {i}) := by
  have hi : HilbertScheme.Presentations.Cech.Signs.ProjectiveCech.alternatingSign R {i, j} i = 1 := by
    simp only [HilbertScheme.Presentations.Cech.Signs.ProjectiveCech.alternatingSign, Finset.filter_insert, Finset.filter_singleton,
      lt_irrefl, not_lt.mpr hij.le, ite_false, Finset.card_empty, pow_zero]
  have hj : HilbertScheme.Presentations.Cech.Signs.ProjectiveCech.alternatingSign R {i, j} j = -1 := by
    simp only [HilbertScheme.Presentations.Cech.Signs.ProjectiveCech.alternatingSign, Finset.filter_insert, Finset.filter_singleton,
      hij, lt_irrefl, ite_true, ite_false, Finset.insert_empty, Finset.card_singleton, pow_one]
  change (∑ k ∈ ({i, j} : Finset σ), HilbertScheme.Presentations.Cech.Signs.ProjectiveCech.alternatingSign R {i, j} k •
    HilbertScheme.Presentations.Graded.ModuleRestriction.ProjectiveCech.moduleChartRestriction R M (Finset.erase_subset k {i, j}) (f (({i, j} : Finset σ).erase k))) = _
  rw [Finset.sum_pair hij.ne, hi, hj, one_smul, neg_one_smul]
  have hei : ({i, j} : Finset σ).erase i = {j} := by simp [hij.ne]
  have hej : ({i, j} : Finset σ).erase j = {i} := by
    ext k
    simp only [Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton]
    constructor
    · rintro ⟨hkj, hki | hkj'⟩
      · exact hki
      · exact (hkj hkj').elim
    · intro hki
      exact ⟨fun hkj => hij.ne (hki.symm.trans hkj), Or.inl hki⟩
  rw [sub_eq_add_neg]
  exact congrArg₂ (fun x y : HilbertScheme.Presentations.Graded.ModuleRestriction.ProjectiveCech.ModuleChart R M {i, j} => x + -y)
    (HilbertScheme.Presentations.ModuleCech.Square.ProjectiveCech.moduleCechValue_congr R M f {i, j} (({i, j} : Finset σ).erase i) {j}
      (Finset.erase_subset i {i, j}) _ hei)
    (HilbertScheme.Presentations.ModuleCech.Square.ProjectiveCech.moduleCechValue_congr R M f {i, j} (({i, j} : Finset σ).erase j) {i}
      (Finset.erase_subset j {i, j}) _ hej)

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Cech.PairDifferential
