import OAI.AlgebraicGeometry.HilbertScheme.Presentations.Has
import OAI.AlgebraicGeometry.HilbertScheme.Presentations.GraphLocus
import Mathlib.CategoryTheory.Limits.FunctorCategory.EpiMono

/-! # Graph Tuple Recovery -/

namespace OAI.AlgebraicGeometry.HilbertScheme.Presentations.GraphTupleRecovery.Core

noncomputable section

/-! The exact graph-tuple predicate is equivalent to existence of a
unique tuple of actual morphisms; the natural graph transformation is monic. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

universe u
variable {S : Scheme.{u}} (X Y : Over S) (n : ℕ)
variable [Flat X.hom] [IsProper X.hom] [LocallyOfFinitePresentation X.hom]
variable [IsSeparated Y.hom]

theorem graphTuples_injective (T : Over S) :
    Function.Injective ((Has.Core.graphs X Y n).app (.op T)) := by
  intro f g h
  funext i
  apply HomFunctor.Hom.graphIdeal_injective X Y T
  exact congrArg (fun I => (I i).val) h

theorem graphTuples_isGraphTuple {T : Over S} (f : (Has.Core.morphismTuples X Y n).obj (.op T)) :
    Has.Core.IsGraphTuple X Y n ((Has.Core.graphs X Y n).app (.op T) f) := by
  intro i
  exact (isIso_iff_of_reflects_iso
    (GraphLocus.Hom.subschemeProjection X Y (HomFunctor.Hom.graphIdeal X Y (f i))) (Over.forget S)).mpr
    (GraphLocus.Hom.graphIdeal_projection_isIso X Y (f i))

theorem isGraphTuple_iff_existsUnique_morphismTuple {T : Over S}
    (I : (Has.Core.hilbertTuples X Y n).obj (.op T)) :
    Has.Core.IsGraphTuple X Y n I ↔
      ∃! f : (Has.Core.morphismTuples X Y n).obj (.op T), (Has.Core.graphs X Y n).app (.op T) f = I := by
  constructor
  · intro h
    have hi (i : Fin n) : IsIso (GraphLocus.Hom.subschemeProjection X Y (I i).val) :=
      (isIso_iff_of_reflects_iso (GraphLocus.Hom.subschemeProjection X Y (I i).val) (Over.forget S)).mp (h i)
    let f : Fin n → (T ⨯ X ⟶ Y) := fun i =>
      @GraphLocus.Hom.recoverMorphism _ X Y T (I i).val (hi i)
    have hf : (Has.Core.graphs X Y n).app (.op T) f = I := by
      funext i
      apply Subtype.ext
      let := hi i
      exact GraphLocus.Hom.graphIdeal_recoverMorphism X Y (I i).val
    exact ⟨f, hf, fun g hg => graphTuples_injective X Y n T (hg.trans hf.symm)⟩
  · rintro ⟨f, rfl, _⟩
    exact graphTuples_isGraphTuple X Y n f

theorem graphTuples_mono : Mono (Has.Core.graphs X Y n) := by
  apply (NatTrans.mono_iff_mono_app _).mpr
  intro T
  exact (CategoryTheory.mono_iff_injective _).mpr (graphTuples_injective X Y n T.unop)

end

end OAI.AlgebraicGeometry.HilbertScheme.Presentations.GraphTupleRecovery.Core
