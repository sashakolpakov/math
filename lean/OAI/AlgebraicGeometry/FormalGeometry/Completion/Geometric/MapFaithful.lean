import OAI.AlgebraicGeometry.FormalGeometry.Completion.Geometric.MapBaseChange
import Mathlib.AlgebraicGeometry.Sites.Fpqc

/-! # Map Faithful -/

namespace OAI.AlgebraicGeometry.FormalGeometry.Completion.Geometric.MapFaithful.Construction

noncomputable section

/-! Actual geometric base change faithfully detects scheme morphisms over a field. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

universe u

variable (k : Type u) [Field k]

/-- The actual algebraic-closure base morphism is faithfully flat and affine. -/
theorem algebraicClosureBase_flat_surjective :
    Flat (Frobenius.Construction.algebraicClosureBase k) ∧ Surjective (Frobenius.Construction.algebraicClosureBase k) := by
  have : Flat (Frobenius.Construction.algebraicClosureBase k) := by
    change Flat (Spec.map (CommRingCat.ofHom (algebraMap k (AlgebraicClosure k))))
    infer_instance
  refine ⟨this, ⟨fun x => ⟨IsLocalRing.closedPoint (AlgebraicClosure k), Subsingleton.elim _ _⟩⟩⟩

/-- The actual projection from a geometric fiber is an fpqc epimorphism. -/
theorem geometricFiberProjection_epi (A : Over (Spec (CommRingCat.of k))) :
    Epi (pullback.fst A.hom (Frobenius.Construction.algebraicClosureBase k)) := by
  have := (algebraicClosureBase_flat_surjective k).1
  have := (algebraicClosureBase_flat_surjective k).2
  have : Flat (pullback.fst A.hom (Frobenius.Construction.algebraicClosureBase k)) := inferInstance
  have : Surjective (pullback.fst A.hom (Frobenius.Construction.algebraicClosureBase k)) := inferInstance
  have : IsAffineHom (Frobenius.Construction.algebraicClosureBase k) := inferInstance
  have : QuasiCompact (Frobenius.Construction.algebraicClosureBase k) := inferInstance
  have : QuasiCompact (pullback.fst A.hom (Frobenius.Construction.algebraicClosureBase k)) := inferInstance
  infer_instance

/-- Equality after the actual geometric base change implies equality over the original field. -/
theorem geometricFiberMap_injective {A B : Over (Spec (CommRingCat.of k))} :
    Function.Injective (Frobenius.Construction.geometricFiberMap k (A := A) (B := B)) := by
  intro f g h
  have := geometricFiberProjection_epi k A
  apply Over.OverMorphism.ext
  apply (cancel_epi (pullback.fst A.hom (Frobenius.Construction.algebraicClosureBase k))).mp
  rw [← Frobenius.Construction.geometricFiberMap_fst, ← Frobenius.Construction.geometricFiberMap_fst, h]

end

end OAI.AlgebraicGeometry.FormalGeometry.Completion.Geometric.MapFaithful.Construction
