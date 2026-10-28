import OAI.AlgebraicGeometry.HilbertScheme.Presentations.Intrinsic.GraphTupleOpen

/-! # Natural Graph Open -/

namespace OAI.AlgebraicGeometry.HilbertScheme.Presentations.NaturalGraphOpen.Hom

noncomputable section

/-! An arbitrary natural native Hilbert family on a locally noetherian
parameter scheme has an open graph locus with the exact statement predicate. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

universe u
variable {S : Scheme.{u}} (X Y : Over S) {n : ℕ} {B : Over S}

theorem naturalHilbertTuple_eq_pullback
    (t : yoneda.obj B ⟶ Has.Core.hilbertTuples X Y n) {T : Over S} (a : T ⟶ B) :
    t.app (.op T) a =
      fun i => Hilbert.Functor.pullbackFamily (X ⨯ Y) a (t.app (.op B) (𝟙 B) i) := by
  have h := ConcreteCategory.congr_hom (t.naturality a.op) (𝟙 B)
  change t.app (.op T) (a ≫ 𝟙 B) =
    (fun i => Hilbert.Functor.pullbackFamily (X ⨯ Y) a (t.app (.op B) (𝟙 B) i)) at h
  simpa only [Category.comp_id] using h

variable [IsProper X.hom] [IsLocallyNoetherian B.left]

theorem naturalHilbertTuple_graphOpen
    (t : yoneda.obj B ⟶ Has.Core.hilbertTuples X Y n) :
    ∃ (M : Over S) (j : M ⟶ B), IsOpenImmersion j.left ∧
      (∀ (T : Over S) (a : T ⟶ B),
        Has.Core.IsGraphTuple X Y n (t.app (.op T) a) ↔ ∃! b : T ⟶ M, b ≫ j = a) := by
  let F : Fin n → Hilbert.Functor.Family (X ⨯ Y) B := t.app (.op B) (𝟙 B)
  refine ⟨Intrinsic.GraphTupleOpen.Hom.nativeGraphTupleOver X Y F, Intrinsic.GraphTupleOpen.Hom.nativeGraphTupleInclusion X Y F,
    Intrinsic.GraphTupleOpen.Hom.nativeGraphTupleInclusion_isOpenImmersion X Y F, ?_⟩
  intro T a
  rw [naturalHilbertTuple_eq_pullback]
  exact Intrinsic.GraphTupleOpen.Hom.nativeGraphTupleOpen_iff_unique_lift X Y F a

end

end OAI.AlgebraicGeometry.HilbertScheme.Presentations.NaturalGraphOpen.Hom
