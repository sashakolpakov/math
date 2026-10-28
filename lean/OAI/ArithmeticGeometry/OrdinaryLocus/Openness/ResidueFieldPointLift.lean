import Mathlib.AlgebraicGeometry.ResidueField
import Mathlib.AlgebraicGeometry.Morphisms.SurjectiveOnStalks

/-! # Residue Field Point Lift -/

namespace OAI.ArithmeticGeometry.OrdinaryLocus.Openness.ResidueFieldPointLift.Construction

noncomputable section

/-! A map surjective on stalks identifies the residue fields and lifts the target residue-field point. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

theorem residueFieldMap_isIso_of_surjectiveOnStalks
    {X Y : Scheme.{u}} (f : X ⟶ Y) [SurjectiveOnStalks f] (x : X) : IsIso (f.residueFieldMap x) := by
  apply (ConcreteCategory.isIso_iff_bijective _).mpr
  refine ⟨(f.residueFieldMap x).hom.injective, ?_⟩
  intro y
  obtain ⟨a, ha⟩ := IsLocalRing.residue_surjective (R := X.presheaf.stalk x) y
  obtain ⟨b, hb⟩ := f.stalkMap_surjective x a
  refine ⟨Y.residue (f x) b, ?_⟩
  have h := ConcreteCategory.congr_hom (Scheme.residue_residueFieldMap f x) b
  exact h.trans ((congrArg (X.residue x) hb).trans ha)

def residueFieldPointLift
    {X Y : Scheme.{u}} (f : X ⟶ Y) [SurjectiveOnStalks f] (x : X) :
    Spec (Y.residueField (f x)) ⟶ X :=
  have := residueFieldMap_isIso_of_surjectiveOnStalks f x
  inv (Spec.map (f.residueFieldMap x)) ≫ X.fromSpecResidueField x

theorem residueFieldPointLift_comp
    {X Y : Scheme.{u}} (f : X ⟶ Y) [SurjectiveOnStalks f] (x : X) :
    residueFieldPointLift f x ≫ f = Y.fromSpecResidueField (f x) := by
  have := residueFieldMap_isIso_of_surjectiveOnStalks f x
  change (inv (Spec.map (f.residueFieldMap x)) ≫ X.fromSpecResidueField x) ≫ f = _
  rw [Category.assoc, ← f.SpecMap_residueFieldMap_fromSpecResidueField,
    ← Category.assoc, IsIso.inv_hom_id, Category.id_comp]

end

end OAI.ArithmeticGeometry.OrdinaryLocus.Openness.ResidueFieldPointLift.Construction
