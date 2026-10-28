import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Normalization.Scheme
import OAI.AlgebraicGeometry.Divisors.LineBundles.SpecFieldOf

/-! # Generic Point -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles.GenericPoint.BundleCycles.GenericPointField

noncomputable section

/-! The native generic-point morphism induces the canonical identification
between the original function field and the function field of its spectrum. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

open OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Normalization.Scheme

universe u

variable (X : Scheme.{u}) [IsIntegral X]

theorem genericMap_appLE (U : X.Opens) [Nonempty U] :
    (IntersectionTheory.ProjectionFormula.Normalization.Scheme.genericMap X).appLE U ⊤ (IntersectionTheory.ProjectionFormula.Normalization.Scheme.genericMap_preimage X U).ge ≫ (Scheme.ΓSpecIso X.functionField).hom =
      X.germToFunctionField U := by
  rw [Scheme.Hom.appLE, IntersectionTheory.ProjectionFormula.Normalization.Scheme.genericMap_app]
  simp only [IntersectionTheory.ProjectionFormula.Normalization.Scheme.preimageFieldIso, Iso.trans_inv, Functor.mapIso_inv, Iso.op_inv, Category.assoc]
  rw [← Category.assoc _ _ (Scheme.ΓSpecIso X.functionField).hom, ← Functor.map_comp]
  have he : (eqToIso (IntersectionTheory.ProjectionFormula.Normalization.Scheme.genericMap_preimage X U).symm).inv.op ≫
      (homOfLE (IntersectionTheory.ProjectionFormula.Normalization.Scheme.genericMap_preimage X U).ge).op = 𝟙 (Opposite.op (⊤ : (Spec X.functionField).Opens)) :=
    Subsingleton.elim _ _
  rw [he, (Spec X.functionField).presheaf.map_id, Category.id_comp, Iso.inv_hom_id, Category.comp_id]

theorem genericMap_fieldMap :
    Cycles.Functoriality.FunctionFields.Construction.genericFieldMap (IntersectionTheory.ProjectionFormula.Normalization.Scheme.genericMap X) (IntersectionTheory.ProjectionFormula.Normalization.Scheme.genericMap_apply X _) =
      (SpecFieldOf.BundleCycles.SpecField.fieldIso X.functionField).hom := by
  let U : X.Opens := (X.affineCover.f (X.affineCover.idx (genericPoint X))).opensRange
  have hU : IsAffineOpen U := isAffineOpen_opensRange (X.affineCover.f _)
  let : Nonempty U := ⟨⟨genericPoint X, X.affineCover.covers _⟩⟩
  let : Nonempty (⊤ : (Spec X.functionField).Opens) := ⟨⟨genericPoint _, trivial⟩⟩
  let := functionField_isFractionRing_of_isAffineOpen X U hU
  have h := GenericFieldComposition.BundleCycles.genericFieldMap_germ_appLE (IntersectionTheory.ProjectionFormula.Normalization.Scheme.genericMap X) (IntersectionTheory.ProjectionFormula.Normalization.Scheme.genericMap_apply X _) U ⊤
    (IntersectionTheory.ProjectionFormula.Normalization.Scheme.genericMap_preimage X U).ge
  have hspec : (Spec X.functionField).germToFunctionField ⊤ =
      (Scheme.ΓSpecIso X.functionField).hom ≫ (SpecFieldOf.BundleCycles.SpecField.fieldIso X.functionField).hom :=
    (SpecFieldOf.BundleCycles.SpecField.fieldIso_germ X.functionField).symm
  rw [hspec, ← Category.assoc, genericMap_appLE] at h
  apply CommRingCat.hom_ext
  apply IsFractionRing.ringHom_ext (A := Γ(X, U))
  intro a
  exact congrArg (fun t : Γ(X, U) ⟶ (Spec X.functionField).functionField => t a) h

end

end OAI.AlgebraicGeometry.Divisors.LineBundles.GenericPoint.BundleCycles.GenericPointField
