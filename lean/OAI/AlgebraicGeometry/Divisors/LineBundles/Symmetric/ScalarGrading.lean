import OAI.AlgebraicGeometry.Divisors.LineBundles.SymmetricProjective.Scheme
import OAI.AlgebraicGeometry.Divisors.LineBundles.Symmetric.ScalarMap

/-! # Scalar Grading -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles.Symmetric.ScalarGrading.BundleCycles

noncomputable section

/-! The actual coefficient-change maps of symmetric algebras preserve
grading. A map whose module image spans gives an everywhere-defined Proj map. -/

open _root_.AlgebraicGeometry _root_.CategoryTheory

variable {R S M N : Type} [CommRing R] [CommRing S] [AddCommGroup M] [AddCommGroup N]
    [Module R M] [Module S N] (f : R →+* S) (g : M →ₛₗ[f] N)

theorem symmetricScalarMap_mem_grade (n : ℕ) (x : SymmetricAlgebra R M)
    (hx : x ∈ Grading.BundleCycles.symmetricGrading R M n) : ScalarMap.BundleCycles.symmetricScalarMap f g x ∈ Grading.BundleCycles.symmetricGrading S N n := by
  change x ∈ LinearMap.range (SymmetricAlgebra.ι R M) ^ n at hx
  induction hx using Submodule.pow_induction_on_left' with
  | algebraMap r =>
    rw [ScalarMap.BundleCycles.symmetricScalarMap_algebraMap]
    exact SetLike.algebraMap_mem_graded (Grading.BundleCycles.symmetricGrading S N) (f r)
  | add x y n hx hy ihx ihy =>
    rw [map_add]
    exact (Grading.BundleCycles.symmetricGrading S N n).add_mem ihx ihy
  | mem_mul m hm n x hx ih =>
    obtain ⟨a, rfl⟩ := hm
    rw [map_mul, ScalarMap.BundleCycles.symmetricScalarMap_generator]
    have hg : SymmetricAlgebra.ι S N (g a) ∈ Grading.BundleCycles.symmetricGrading S N 1 := by
      change SymmetricAlgebra.ι S N (g a) ∈ LinearMap.range (SymmetricAlgebra.ι S N) ^ 1
      simpa only [pow_one] using LinearMap.mem_range_self (SymmetricAlgebra.ι S N) (g a)
    simpa only [add_comm 1 n] using SetLike.mul_mem_graded hg ih

def symmetricScalarGradedMap : Grading.BundleCycles.symmetricGrading R M →+*ᵍ Grading.BundleCycles.symmetricGrading S N where
  __ := ScalarMap.BundleCycles.symmetricScalarMap f g
  map_mem {n} {x} hx := symmetricScalarMap_mem_grade f g n x hx

theorem symmetricScalarGradedMap_irrelevant (hgen : Submodule.span S (Set.range g) = ⊤) :
    HomogeneousIdeal.irrelevant (Grading.BundleCycles.symmetricGrading S N) ≤
      (HomogeneousIdeal.irrelevant (Grading.BundleCycles.symmetricGrading R M)).map (symmetricScalarGradedMap f g) := by
  let I := Ideal.map (ScalarMap.BundleCycles.symmetricScalarMap f g) (Ideal.span (Set.range (SymmetricAlgebra.ι R M)))
  have hN : ∀ n : N, SymmetricAlgebra.ι S N n ∈ I := by
    intro n
    have hn : n ∈ Submodule.span S (Set.range g) := by rw [hgen]; trivial
    induction hn using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨m, rfl⟩ := hx
      rw [← ScalarMap.BundleCycles.symmetricScalarMap_generator f g m]
      exact Ideal.mem_map_of_mem _ (Ideal.subset_span ⟨m, rfl⟩)
    | zero => rw [map_zero]; exact I.zero_mem
    | add x y hx hy ihx ihy => rw [map_add]; exact I.add_mem ihx ihy
    | smul s n hn ih => rw [map_smul]; exact (I.restrictScalars S).smul_mem s ih
  change (HomogeneousIdeal.irrelevant (Grading.BundleCycles.symmetricGrading S N)).toIdeal ≤
    Ideal.map (symmetricScalarGradedMap f g) (HomogeneousIdeal.irrelevant (Grading.BundleCycles.symmetricGrading R M)).toIdeal
  rw [GradingIdeals.BundleCycles.symmetricIrrelevant_eq_generatorIdeal, GradingIdeals.BundleCycles.symmetricIrrelevant_eq_generatorIdeal]
  apply Ideal.span_le.mpr
  rintro x ⟨n, rfl⟩
  exact hN n

def symmetricScalarProjectiveMap (hgen : Submodule.span S (Set.range g) = ⊤) :
    SymmetricProjective.Scheme.BundleCycles.symmetricProjectiveScheme S N ⟶ SymmetricProjective.Scheme.BundleCycles.symmetricProjectiveScheme R M :=
  Proj.map (symmetricScalarGradedMap f g) (symmetricScalarGradedMap_irrelevant f g hgen)

end

end OAI.AlgebraicGeometry.Divisors.LineBundles.Symmetric.ScalarGrading.BundleCycles
