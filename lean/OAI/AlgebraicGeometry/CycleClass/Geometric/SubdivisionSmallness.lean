import OAI.AlgebraicGeometry.CycleClass.Geometric.IteratedSubdivision
import OAI.AlgebraicGeometry.CycleClass.Geometric.SubdivisionOperator

/-! # Subdivision Smallness -/

namespace OAI.AlgebraicGeometry.CycleClass.Geometric.SubdivisionSmallness.Cycles

noncomputable section

/-!
# Actual iterated subdivision makes finite singular chains small

The support formula for the genuine degreewise signed subdivision operator is
iterated and matched with the actual affine cell maps. Thus the geometric mesh
estimate applies to every simplex that survives in the actual subdivided chain,
including any cancellations of coefficients.
-/

open _root_.CategoryTheory
open scoped Simplicial

/-- Every simplex in the support of an actual iterated subdivision comes from
an original support simplex and an equally long list of actual cell maps. -/
theorem mem_support_iterated_subdivisionDegree (X : TopCat.{0}) (n N : ℕ)
    (c : (LocalHomology.Cycles.integralSingularChains X).X n) (t : SubdivisionOperator.Cycles.SingularSimplex X n)
    (ht : t ∈ SingularChainSupport.Cycles.singularChainSupport ((SubdivisionOperator.Cycles.subdivisionDegree X n)^[N] c)) :
    ∃ s ∈ SingularChainSupport.Cycles.singularChainSupport c, ∃ l : List (Equiv.Perm (Fin (n + 1))),
      l.length = N ∧ X.toSSetObjEquiv (.op ⦋n⦌) t =
        (X.toSSetObjEquiv (.op ⦋n⦌) s).comp (IteratedSubdivision.Cycles.iteratedSubdivisionMap l) := by
  induction N generalizing t with
  | zero =>
      refine ⟨t, ?_, [], rfl, ?_⟩
      · simpa only [Function.iterate_zero_apply] using ht
      · simp
  | succ N ih =>
      rw [Function.iterate_succ_apply'] at ht
      obtain ⟨u, hu, σ, rfl⟩ := SubdivisionOperator.Cycles.mem_support_subdivisionDegree X n _ t ht
      obtain ⟨s, hs, l, hl, heq⟩ := ih u hu
      refine ⟨s, hs, σ :: l, by simp [hl], ?_⟩
      simp only [SubdivisionOperator.Cycles.subdivisionSimplex_toContinuousMap, heq,
        IteratedSubdivision.Cycles.iteratedSubdivisionMap_cons, ContinuousMap.comp_assoc]

/-- For every genuine finite integral chain, some actual iterate of its signed
barycentric subdivision consists entirely of simplices in single cover members. -/
theorem exists_subdivisionDegree_iterate_small {X : TopCat.{0}} {J : Type}
    (U : J → Set X) (hopen : ∀ i, IsOpen (U i))
    (hcover : ∀ x : X, ∃ i, x ∈ U i) {n : ℕ}
    (c : (LocalHomology.Cycles.integralSingularChains X).X n) :
    ∃ N : ℕ, ∀ t ∈ SingularChainSupport.Cycles.singularChainSupport ((SubdivisionOperator.Cycles.subdivisionDegree X n)^[N] c),
      t ∈ (AlgebraicTopology.DeRham.Comparison.SmallSingularSet.smallSingularSubcomplex X U).obj (.op ⦋n⦌) := by
  obtain ⟨N, hN⟩ := IteratedSubdivision.Cycles.singularChain_iteratedSubdivision_small U hopen hcover c
  refine ⟨N, ?_⟩
  intro t ht
  obtain ⟨s, hs, l, hl, heq⟩ := mem_support_iterated_subdivisionDegree X n N c t ht
  change ∃ i, Set.range (X.toSSetObjEquiv (.op ⦋n⦌) t) ⊆ U i
  rw [heq]
  exact hN s hs l hl

end

end OAI.AlgebraicGeometry.CycleClass.Geometric.SubdivisionSmallness.Cycles
