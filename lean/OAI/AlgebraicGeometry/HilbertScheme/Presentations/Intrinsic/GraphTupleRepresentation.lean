import OAI.AlgebraicGeometry.HilbertScheme.Presentations.Intrinsic.GraphTupleOpen
import OAI.AlgebraicGeometry.HilbertScheme.Presentations.SubfunctorRepresentations

/-! # Graph Tuple Representation -/

namespace OAI.AlgebraicGeometry.HilbertScheme.Presentations.Intrinsic.GraphTupleRepresentation.Hom

noncomputable section

/-! The open graph locus represents the exact native graph-tuple
subfunctor over any locally noetherian parameter scheme. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

universe u
variable {S : Scheme.{u}} (X Y : Over S) [IsProper X.hom]
variable {n : ℕ} {B : Over S} [IsLocallyNoetherian B.left]
variable (F : Fin n → Hilbert.Functor.Family (X ⨯ Y) B)

def nativeGraphTupleSubfunctor : Subfunctor (yoneda.obj B) where
  obj T := {a | Has.Core.IsGraphTuple X Y n (fun i => Hilbert.Functor.pullbackFamily (X ⨯ Y) a (F i))}
  map a b hb := by
    apply (GraphTupleOpen.Hom.nativeGraphTupleOpen_baseChange_iff_range X Y F (a.unop ≫ b)).mpr
    rintro t ⟨s, rfl⟩
    exact (GraphTupleOpen.Hom.nativeGraphTupleOpen_baseChange_iff_range X Y F b).mp hb ⟨a.unop.left s, rfl⟩

theorem nativeGraphTupleSubfunctor_representation :
    ∃ e : yoneda.obj (GraphTupleOpen.Hom.nativeGraphTupleOver X Y F) ≅ (nativeGraphTupleSubfunctor X Y F).toFunctor,
      e.hom ≫ (nativeGraphTupleSubfunctor X Y F).ι = yoneda.map (GraphTupleOpen.Hom.nativeGraphTupleInclusion X Y F) := by
  apply SubfunctorRepresentations.subfunctor_representation_of_lifts (nativeGraphTupleSubfunctor X Y F)
    (GraphTupleOpen.Hom.nativeGraphTupleInclusion X Y F)
  intro T a
  change Has.Core.IsGraphTuple X Y n _ ↔ _
  rw [GraphTupleOpen.Hom.nativeGraphTupleOpen_iff_unique_lift]
  exact ⟨ExistsUnique.exists, fun ⟨b, hb⟩ =>
    ⟨b, hb, fun c hc => (cancel_mono (GraphTupleOpen.Hom.nativeGraphTupleInclusion X Y F)).mp (hc.trans hb.symm)⟩⟩

omit [IsLocallyNoetherian B.left] in
theorem nativeGraphTupleOver_locallyOfFiniteType [LocallyOfFiniteType B.hom] :
    LocallyOfFiniteType (GraphTupleOpen.Hom.nativeGraphTupleOver X Y F).hom := by
  change LocallyOfFiniteType ((GraphTupleOpen.Hom.nativeGraphTupleOpen X Y F).ι ≫ B.hom)
  infer_instance

end

end OAI.AlgebraicGeometry.HilbertScheme.Presentations.Intrinsic.GraphTupleRepresentation.Hom
