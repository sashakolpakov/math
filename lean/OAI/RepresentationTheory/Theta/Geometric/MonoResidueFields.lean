import Mathlib.AlgebraicGeometry.ResidueField
import Mathlib.AlgebraicGeometry.Morphisms.FlatMono

/-! # Mono Residue Fields -/

namespace OAI.RepresentationTheory.Theta.Geometric.MonoResidueFields

noncomputable section

/-! A monomorphism identifies the actual residue fields of its points.
The residue-field morphism is a faithfully flat monomorphism of affine schemes. -/

set_option backward.isDefEq.respectTransparency false
open _root_.AlgebraicGeometry _root_.CategoryTheory

universe u

theorem spec_residueFieldMap_isIso {X Y : Scheme.{u}} (f : X ⟶ Y) [Mono f] (x : X) :
    IsIso (Spec.map (f.residueFieldMap x)) := by
  have : Mono (Spec.map (f.residueFieldMap x) ≫ Y.fromSpecResidueField (f x)) := by
    rw [f.SpecMap_residueFieldMap_fromSpecResidueField]
    infer_instance
  have : Mono (Spec.map (f.residueFieldMap x)) :=
    mono_of_mono (Spec.map (f.residueFieldMap x)) (Y.fromSpecResidueField (f x))
  have : Surjective (Spec.map (f.residueFieldMap x)) := by
    constructor
    intro y
    exact ⟨IsLocalRing.closedPoint (X.residueField x), Subsingleton.elim _ _⟩
  exact Flat.isIso_of_surjective_of_mono (Spec.map (f.residueFieldMap x))

def residuePointLift {X Y : Scheme.{u}} (f : X ⟶ Y) [Mono f] (x : X) :
    Spec (Y.residueField (f x)) ⟶ X :=
  letI := spec_residueFieldMap_isIso f x
  inv (Spec.map (f.residueFieldMap x)) ≫ X.fromSpecResidueField x

theorem residuePointLift_comp {X Y : Scheme.{u}} (f : X ⟶ Y) [Mono f] (x : X) :
    residuePointLift f x ≫ f = Y.fromSpecResidueField (f x) := by
  let := spec_residueFieldMap_isIso f x
  rw [residuePointLift, Category.assoc, ← f.SpecMap_residueFieldMap_fromSpecResidueField,
    IsIso.inv_hom_id_assoc]

theorem residuePoint_hasLift {Z B T : Scheme.{u}} (i : Z ⟶ B) [Mono i]
    (a : T ⟶ B) (y : T) (z : Z) (h : a y = i z) :
    ∃ w : Spec (T.residueField y) ⟶ Z, w ≫ i = T.fromSpecResidueField y ≫ a := by
  refine ⟨Spec.map (a.residueFieldMap y) ≫ Spec.map (B.residueFieldCongr h).inv ≫
    residuePointLift i z, ?_⟩
  simp only [Category.assoc, residuePointLift_comp, Scheme.residueFieldCongr_inv,
    Scheme.residueFieldCongr_fromSpecResidueField,
    Scheme.Hom.SpecMap_residueFieldMap_fromSpecResidueField]

end

end OAI.RepresentationTheory.Theta.Geometric.MonoResidueFields
