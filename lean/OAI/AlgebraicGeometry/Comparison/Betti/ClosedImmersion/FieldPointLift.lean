import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
import Mathlib.AlgebraicGeometry.ResidueField

/-! # Field Point Lift -/

namespace OAI.AlgebraicGeometry.Comparison.Betti.ClosedImmersion.FieldPointLift

noncomputable section

/-! Field-valued points lift through a closed immersion exactly when their underlying point lies in its image. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

theorem closedImmersion_residueFieldMap_bijective
    {X Y : Scheme.{0}} (f : X ⟶ Y) [IsClosedImmersion f] (x : X) :
    Function.Bijective (f.residueFieldMap x) := by
  refine ⟨(f.residueFieldMap x).hom.injective, ?_⟩
  intro b
  obtain ⟨s, rfl⟩ := X.residue_surjective x b
  obtain ⟨a, rfl⟩ := f.stalkMap_surjective x s
  exact ⟨Y.residue (f x) a, ConcreteCategory.congr_hom (Scheme.residue_residueFieldMap f x) a⟩

theorem closedImmersion_fieldPoint_lift
    {X Y : Scheme.{0}} (f : X ⟶ Y) [IsClosedImmersion f]
    (K : Type) [Field K] (g : Spec (CommRingCat.of K) ⟶ Y)
    (x : X) (hx : f x = g (IsLocalRing.closedPoint K)) :
    ∃ l : Spec (CommRingCat.of K) ⟶ X, l ≫ f = g := by
  have : IsIso (f.residueFieldMap x) :=
    (ConcreteCategory.isIso_iff_bijective _).mpr (closedImmersion_residueFieldMap_bijective f x)
  let c := (Y.residueFieldCongr hx).hom ≫
    Y.descResidueField (Scheme.stalkClosedPointTo g)
  let l := Spec.map (inv (f.residueFieldMap x) ≫ c) ≫ X.fromSpecResidueField x
  refine ⟨l, ?_⟩
  change (Spec.map (inv (f.residueFieldMap x) ≫ c) ≫ X.fromSpecResidueField x) ≫ f = g
  rw [Category.assoc, ← f.SpecMap_residueFieldMap_fromSpecResidueField x,
    ← Spec.map_comp_assoc, IsIso.hom_inv_id_assoc]
  change Spec.map ((Y.residueFieldCongr hx).hom ≫
    Y.descResidueField (Scheme.stalkClosedPointTo g)) ≫ Y.fromSpecResidueField (f x) = g
  rw [Spec.map_comp, Category.assoc, Scheme.residueFieldCongr_fromSpecResidueField]
  exact Scheme.descResidueField_stalkClosedPointTo_fromSpecResidueField K Y g

end

end OAI.AlgebraicGeometry.Comparison.Betti.ClosedImmersion.FieldPointLift
