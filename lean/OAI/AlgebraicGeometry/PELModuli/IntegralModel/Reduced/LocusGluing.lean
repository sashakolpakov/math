import OAI.AlgebraicGeometry.PELModuli.IntegralModel.LocalLocusPointCriterion
import OAI.AlgebraicGeometry.PELModuli.IntegralModel.Reduced.LocallyClosedSubscheme

/-! # Locus Gluing -/

namespace OAI.AlgebraicGeometry.PELModuli.IntegralModel.Reduced.LocusGluing

noncomputable section

/-! Geometrically detected local reduced classifiers glue to an actual
global reduced immersion. All existence is obtained by constructing the
locally closed subset and its reduced induced scheme. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace

theorem exists_global_reduced_locus_of_local_classifiers
    {S : Scheme.{0}} [NoetherianSpace S] (F : Subfunctor (yoneda.obj S))
    {I : Type} (U : I → S.Opens) (hU : IsOpenCover U)
    (Z : I → Scheme.{0}) (j : ∀ i, Z i ⟶ (U i).toScheme)
    (hj : ∀ i, IsImmersion (j i))
    (hclass : ∀ (i : I) (T : Scheme.{0}) [IsReduced T] (x : T ⟶ (U i).toScheme),
      x ≫ (U i).ι ∈ F.obj (.op T) ↔ Set.range x ⊆ Set.range (j i))
    (hgeo : ∀ (T : Scheme.{0}) [IsReduced T] (x : T ⟶ S),
      (∀ (k : Type) [Field k] [IsAlgClosed k] (p : Spec (.of k) ⟶ T),
        p ≫ x ∈ F.obj (.op (Spec (.of k)))) → x ∈ F.obj (.op T)) :
    ∃ (L : Scheme.{0}) (a : L ⟶ S),
      IsReduced L ∧ IsImmersion a ∧ QuasiCompact a ∧
      ∀ (T : Scheme.{0}) [IsReduced T] (x : T ⟶ S),
        x ∈ F.obj (.op T) ↔ ∃! f : T ⟶ L, f ≫ a = x := by
  obtain ⟨L, a, hL, ha, hqc, hr⟩ := LocallyClosedSubscheme.exists_reduced_quasicompact_immersion_with_range S
    (LocalLocusPointCriterion.ReducedLocusGluing.locusSet U Z j)
    (LocalLocusPointCriterion.ReducedLocusGluing.locusSet_locallyClosed F U hU Z j hclass hj)
  let := ha
  refine ⟨L, a, hL, ha, hqc, ?_⟩
  intro T hT x
  rw [ImmersionFactorization.reduced_immersion_lift_iff_range, hr]
  exact LocalLocusPointCriterion.ReducedLocusGluing.mem_iff_range_locusSet F U hU Z j hclass hgeo T x

end

end OAI.AlgebraicGeometry.PELModuli.IntegralModel.Reduced.LocusGluing
