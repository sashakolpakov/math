import OAI.AlgebraicGeometry.PELModuli.IntegralModel.Reduced.LocallyClosedSubscheme

/-! # Reduced Locus Intersection -/

namespace OAI.AlgebraicGeometry.PELModuli.IntegralModel.Finite.ReducedLocusIntersection

noncomputable section

/-! Finitely many constructed reduced immersion loci have an actual
reduced intersection with the simultaneous unique classification property. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace

theorem finite_iInter_locallyClosed {X I : Type} [TopologicalSpace X] [Finite I]
    (W : I → Set X) (hW : ∀ i, IsLocallyClosed (W i)) : IsLocallyClosed (⋂ i, W i) := by
  classical
  let := Fintype.ofFinite I
  have h (s : Finset I) : IsLocallyClosed (⋂ i ∈ (s : Set I), W i) := by
    induction s using Finset.induction_on with
    | empty => simpa using isOpen_univ.isLocallyClosed
    | @insert a s ha ih =>
      rw [Finset.coe_insert, Set.biInter_insert]
      exact (hW a).inter ih
  simpa using h Finset.univ

theorem exists_finite_reduced_locus_intersection
    {S : Scheme.{0}} [NoetherianSpace S] {I : Type} [Finite I]
    (Z : I → Scheme.{0}) (j : ∀ i, Z i ⟶ S) (hj : ∀ i, IsImmersion (j i)) :
    ∃ (L : Scheme.{0}) (a : L ⟶ S), IsReduced L ∧ IsImmersion a ∧ QuasiCompact a ∧
      ∀ (T : Scheme.{0}) [IsReduced T] (x : T ⟶ S),
        (∀ i, ∃! f : T ⟶ Z i, f ≫ j i = x) ↔ ∃! f : T ⟶ L, f ≫ a = x := by
  have hW : IsLocallyClosed (⋂ i, Set.range (j i)) :=
    finite_iInter_locallyClosed _ (fun i => @IsImmersion.isLocallyClosed_range _ _ (j i) (hj i))
  obtain ⟨L, a, hL, ha, hqc, hr⟩ :=
    Reduced.LocallyClosedSubscheme.exists_reduced_quasicompact_immersion_with_range S _ hW
  let := ha
  refine ⟨L, a, hL, ha, hqc, ?_⟩
  intro T hT x
  rw [Reduced.ImmersionFactorization.reduced_immersion_lift_iff_range, hr, Set.subset_iInter_iff]
  apply forall_congr'
  intro i
  let := hj i
  exact Reduced.ImmersionFactorization.reduced_immersion_lift_iff_range (j i) x

end

end OAI.AlgebraicGeometry.PELModuli.IntegralModel.Finite.ReducedLocusIntersection
