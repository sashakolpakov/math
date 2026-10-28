import OAI.RepresentationTheory.Theta.Geometric.RegularFunctionDescent
import Mathlib.AlgebraicGeometry.Morphisms.Flat

/-! # Structure Coordinates -/

namespace OAI.RepresentationTheory.Theta.Geometric.Affine.StructureCoordinates

noncomputable section

/-! Native affine coordinates over any parameter algebra, including
flatness of those coordinates over the specified structure morphism. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
open scoped TensorProduct

@[instance_reducible] def affineStructureAlgebra {A : Type} [CommRing A] {X : Scheme}
    [IsAffine X] (h : X ⟶ Spec (.of A)) : Algebra A Γ(X, ⊤) :=
  (Spec.preimage (X.isoSpec.inv ≫ h)).hom.toAlgebra

theorem affineStructure_specMap {A : Type} [CommRing A] {X : Scheme} [IsAffine X]
    (h : X ⟶ Spec (.of A)) :
    let : Algebra A Γ(X, ⊤) := affineStructureAlgebra h
    Spec.map (CommRingCat.ofHom (algebraMap A Γ(X, ⊤))) = X.isoSpec.inv ≫ h := by
  let : Algebra A Γ(X, ⊤) := affineStructureAlgebra h
  change Spec.map (Spec.preimage (X.isoSpec.inv ≫ h)) = _
  exact Spec.map_preimage _

theorem affineStructure_flat {A : Type} [CommRing A] {X : Scheme} [IsAffine X]
    (h : X ⟶ Spec (.of A)) [Flat h] :
    let : Algebra A Γ(X, ⊤) := affineStructureAlgebra h
    Module.Flat A Γ(X, ⊤) := by
  let : Algebra A Γ(X, ⊤) := affineStructureAlgebra h
  have H : Flat (Spec.map (CommRingCat.ofHom (algebraMap A Γ(X, ⊤)))) := by
    rw [affineStructure_specMap h]
    infer_instance
  exact RingHom.flat_algebraMap_iff.mp (Flat.SpecMap_iff.mp H)

end

end OAI.RepresentationTheory.Theta.Geometric.Affine.StructureCoordinates
