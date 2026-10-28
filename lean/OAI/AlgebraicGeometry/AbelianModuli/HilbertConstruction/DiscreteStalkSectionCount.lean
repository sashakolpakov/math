import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.DisjointCoefficientSectionProduct
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Module.StalkExactness
import Mathlib.LinearAlgebra.Dimension.Constructions

/-! # Discrete Stalk Section Count -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.DiscreteStalkSectionCount

noncomputable section

/-! On a finite discrete scheme, every nonzero stalk contributes at
least one dimension to global sections. The proof uses actual sections
on singleton opens and their disjoint gluing. -/
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry _root_.TopologicalSpace
universe u

def singletonSchemeOpen {X : Scheme.{u}} [DiscreteTopology X] (x : X) : X.Opens :=
  ⟨{x}, isOpen_discrete _⟩

theorem nonzero_stalk_exists_nonzero_singleton_section
    {X : Scheme.{u}} [DiscreteTopology X] (M : X.Modules) (x : X)
    (hx : ¬ IsZero ((HilbertConstruction.Module.StalkExactness.moduleStalkFunctor x).obj M)) :
    ∃ s : Γ(M, singletonSchemeOpen x), s ≠ 0 := by
  classical
  have hnt : Nontrivial (M.presheaf.stalk x) := by
    apply not_subsingleton_iff_nontrivial.mp
    intro h
    have : Subsingleton ((HilbertConstruction.Module.StalkExactness.moduleStalkFunctor x).obj M) := h
    exact hx (ModuleCat.isZero_of_subsingleton _)
  let := hnt
  obtain ⟨m, hm⟩ := exists_ne (0 : M.presheaf.stalk x)
  obtain ⟨U, hxU, s, hs⟩ := M.presheaf.exists_germ_eq m
  have hle : singletonSchemeOpen x ≤ U := by
    intro y hy
    have he : y = x := hy
    exact he.symm ▸ hxU
  let t := M.presheaf.map (homOfLE hle).op s
  have ht : M.presheaf.germ (singletonSchemeOpen x) x (Set.mem_singleton x) t = m :=
    (M.presheaf.germ_res_apply (homOfLE hle) x (Set.mem_singleton x) s).trans hs
  refine ⟨t, ?_⟩
  intro hz
  exact hm (ht.symm.trans (by rw [hz, map_zero]))

theorem discrete_stalk_count_le_sectionDimension
    {K : Type u} [Field K] {X : Scheme.{u}} [Finite X] [DiscreteTopology X]
    (c : K →+* Γ(X, ⊤)) (M : X.Modules)
    [Module.Finite K ((Coefficient.SectionEvaluation.coefficientSectionFunctor c ⊤).obj M)]
    (S : Finset X) (hS : ∀ x ∈ S, ¬ IsZero ((HilbertConstruction.Module.StalkExactness.moduleStalkFunctor x).obj M)) :
    S.card ≤ Module.finrank K ((Coefficient.SectionEvaluation.coefficientSectionFunctor c ⊤).obj M) := by
  classical
  let : Fintype X := Fintype.ofFinite X
  let U : X → X.Opens := singletonSchemeOpen
  have hcover : ∀ x : X, ∃ i, x ∈ U i := fun x => ⟨x, Set.mem_singleton x⟩
  have hdis : Pairwise (fun i j => Disjoint (U i) (U j)) := by
    intro i j hij
    apply disjoint_iff.mpr
    apply le_antisymm
    · intro x hx
      exact (hij (hx.1.symm.trans hx.2)).elim
    · exact bot_le
  let V : X → Type u := fun x => (Coefficient.SectionEvaluation.coefficientSectionFunctor c (U x)).obj M
  let e := DisjointCoefficientSectionProduct.disjointCoefficientSectionProductEquiv c M U hcover hdis
  have : Module.Finite K (∀ x, V x) := Module.Finite.equiv e
  have hfin (x : X) : Module.Finite K (V x) :=
    Module.Finite.of_surjective (LinearMap.proj x : (∀ y, V y) →ₗ[K] V x)
      (fun v => ⟨Pi.single x v, by simp⟩)
  have hpos (x : X) (hx : x ∈ S) : 1 ≤ Module.finrank K (V x) := by
    apply Nat.succ_le_of_lt
    apply Module.finrank_pos_iff_exists_ne_zero.mpr
    exact nonzero_stalk_exists_nonzero_singleton_section M x (hS x hx)
  calc
    S.card = ∑ _x ∈ S, 1 := by simp
    _ ≤ ∑ x ∈ S, Module.finrank K (V x) := Finset.sum_le_sum hpos
    _ ≤ ∑ x : X, Module.finrank K (V x) := Finset.sum_le_sum_of_subset (Finset.subset_univ S)
    _ = Module.finrank K ((Coefficient.SectionEvaluation.coefficientSectionFunctor c ⊤).obj M) :=
      (Module.finrank_pi_fintype K).symm.trans e.finrank_eq.symm

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.DiscreteStalkSectionCount
