import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Affine.FractionField
import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Affine.Order

/-! # Branch Stalk Field -/

namespace OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.BranchStalkField

noncomputable section

/-! The native stalk at a normal affine branch embeds in the specified
fraction field. This supplies the actual valuation rings used to place
normalized parameter branches on the proper curve. -/

set_option backward.isDefEq.respectTransparency false

open _root_.CategoryTheory _root_.AlgebraicGeometry IsDedekindDomain

open OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Affine.Order OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Affine.FractionField

universe u

variable (A : Type u) [CommRing A] [IsDedekindDomain A]
  (L : Type u) [Field L] [Algebra A L] [IsFractionRing A L]

local instance : Algebra A (Spec (.of A)).functionField :=
  (StructureSheaf.toStalk A (genericPoint (Spec (.of A)))).hom.toAlgebra

local instance (x : Spec (.of A)) : Algebra A ((Spec (.of A)).presheaf.stalk x) :=
  StructureSheaf.stalkAlgebra A x

abbrev branchStalk (P : HeightOneSpectrum A) := (Spec (.of A)).presheaf.stalk (Affine.Order.branchPoint A P)

theorem branchStalk_isDVR (P : HeightOneSpectrum A) : IsDiscreteValuationRing (branchStalk A P) := by
  let := IsLocalization.AtPrime.isDiscreteValuationRing_of_dedekind_domain A P.ne_bot (Localization.AtPrime P.asIdeal)
  exact IsDiscreteValuationRing.RingEquivClass.isDiscreteValuationRing
    (Affine.Order.affineStalkIso A (Affine.Order.branchPoint A P)).toRingEquiv

abbrev branchAlgebra (P : HeightOneSpectrum A) : Algebra (branchStalk A P) L :=
  ((Affine.FractionField.fieldIso A L).hom.hom.comp (algebraMap (branchStalk A P) (Spec (.of A)).functionField)).toAlgebra

def branchFieldEquiv (P : HeightOneSpectrum A) :
    letI := branchAlgebra A L P
    (Spec (.of A)).functionField ≃ₐ[branchStalk A P] L := by
  let := branchAlgebra A L P
  exact { (Affine.FractionField.fieldIso A L).commRingCatIsoToRingEquiv with commutes' := fun _ => rfl }

theorem branch_isFractionRing (P : HeightOneSpectrum A) :
    letI := branchAlgebra A L P
    IsFractionRing (branchStalk A P) L := by
  let := branchAlgebra A L P
  exact IsFractionRing.of_algEquiv (branchFieldEquiv A L P)

theorem branch_toStalk (P : HeightOneSpectrum A) :
    letI := branchAlgebra A L P
    StructureSheaf.toStalk A (Affine.Order.branchPoint A P) ≫
      CommRingCat.ofHom (algebraMap (branchStalk A P) L) = CommRingCat.ofHom (algebraMap A L) := by
  let := branchAlgebra A L P
  let := Affine.Order.affine_stalk_functionField_tower A (Affine.Order.branchPoint A P)
  ext a
  have h := congrArg (fun t : CommRingCat.of A ⟶ CommRingCat.of L => t a) (Affine.FractionField.toStalk_fieldIso A L)
  change (Affine.FractionField.fieldIso A L).hom
    (algebraMap (branchStalk A P) (Spec (.of A)).functionField
      (algebraMap A (branchStalk A P) a)) = algebraMap A L a
  rw [← IsScalarTower.algebraMap_apply]
  exact h

theorem generic_branch_comp (P : HeightOneSpectrum A) :
    letI := branchAlgebra A L P
    Spec.map (CommRingCat.ofHom (algebraMap (branchStalk A P) L)) ≫
      (Spec (.of A)).fromSpecStalk (Affine.Order.branchPoint A P) =
        Spec.map (CommRingCat.ofHom (algebraMap A L)) := by
  let := branchAlgebra A L P
  rw [Spec.fromSpecStalk_eq', ← Spec.map_comp, branch_toStalk]

end

end OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.BranchStalkField
