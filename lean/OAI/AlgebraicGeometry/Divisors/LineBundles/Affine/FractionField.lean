import OAI.AlgebraicGeometry.Divisors.LineBundles.SpecFieldOf

/-! # Fraction Field -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles.Affine.FractionField.BundleCycles.AffineFractionField

noncomputable section

/-! Canonical comparison of an affine scheme's native function field with
any specified fraction field, including the actual generic-stalk pullback. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

variable (A : Type u) [CommRing A] [IsDomain A]
  (L : Type u) [Field L] [Algebra A L] [IsFractionRing A L]

local instance (B : Type u) [CommRing B] [IsDomain B] :
    Algebra B (Spec (.of B)).functionField :=
  (StructureSheaf.toStalk B (genericPoint (Spec (.of B)))).hom.toAlgebra

local instance : IsFractionRing A (Spec (.of A)).functionField :=
  functionField_isFractionRing_of_affine (.of A)

def fieldIso : (Spec (.of A)).functionField ≅ CommRingCat.of L :=
  (IsLocalization.algEquiv (nonZeroDivisors A) (Spec (.of A)).functionField L).toRingEquiv.toCommRingCatIso

theorem toStalk_fieldIso :
    StructureSheaf.toStalk A (genericPoint (Spec (.of A))) ≫ (fieldIso A L).hom =
      CommRingCat.ofHom (algebraMap A L) := by
  ext a
  exact (IsLocalization.algEquiv (nonZeroDivisors A) (Spec (.of A)).functionField L).commutes a

theorem genericMap_genericPoint :
    (Spec.map (CommRingCat.ofHom (algebraMap A L))) (genericPoint (Spec (.of L))) =
      genericPoint (Spec (.of A)) := by
  rw [genericPoint_eq_bot_of_affine, genericPoint_eq_bot_of_affine]
  apply PrimeSpectrum.ext
  exact (RingHom.injective_iff_ker_eq_bot (algebraMap A L)).mp (IsFractionRing.injective A L)

theorem genericMap_fieldMap :
    Cycles.Functoriality.FunctionFields.Construction.genericFieldMap (Spec.map (CommRingCat.ofHom (algebraMap A L)))
      (genericMap_genericPoint A L) = (fieldIso A L).hom ≫ (SpecFieldOf.BundleCycles.SpecField.fieldIso L).hom := by
  apply CommRingCat.hom_ext
  apply IsFractionRing.ringHom_ext (A := A)
  intro a
  have h := Cycles.Functoriality.FunctionFields.Construction.genericFieldMap_germ
    (Spec.map (CommRingCat.ofHom (algebraMap A L))) (genericMap_genericPoint A L)
  have hs : StructureSheaf.toStalk A (genericPoint (Spec (.of A))) ≫
      Cycles.Functoriality.FunctionFields.Construction.genericFieldMap (Spec.map (CommRingCat.ofHom (algebraMap A L)))
        (genericMap_genericPoint A L) =
      CommRingCat.ofHom (algebraMap A L) ≫
        StructureSheaf.toStalk L (genericPoint (Spec (.of L))) := by
    change (Scheme.ΓSpecIso (.of A)).inv ≫
      (Spec (.of A)).presheaf.germ ⊤ (genericPoint (Spec (.of A))) (by trivial) ≫
        Cycles.Functoriality.FunctionFields.Construction.genericFieldMap (Spec.map (CommRingCat.ofHom (algebraMap A L)))
          (genericMap_genericPoint A L) =
      CommRingCat.ofHom (algebraMap A L) ≫ (Scheme.ΓSpecIso (.of L)).inv ≫
        (Spec (.of L)).presheaf.germ ⊤ (genericPoint (Spec (.of L))) (by trivial)
    rw [h, Scheme.ΓSpecIso_inv_naturality_assoc]
  have hr : StructureSheaf.toStalk A (genericPoint (Spec (.of A))) ≫
      (fieldIso A L).hom ≫ (SpecFieldOf.BundleCycles.SpecField.fieldIso L).hom =
      CommRingCat.ofHom (algebraMap A L) ≫
        StructureSheaf.toStalk L (genericPoint (Spec (.of L))) := by
    ext b
    exact (congrArg (SpecFieldOf.BundleCycles.SpecField.fieldIso L).hom
      (ConcreteCategory.congr_hom (toStalk_fieldIso A L) b)).trans
        (ConcreteCategory.congr_hom (SpecFieldOf.BundleCycles.SpecField.fieldIso_hom L) (algebraMap A L b))
  exact congrArg (fun t : CommRingCat.of A ⟶ (Spec (.of L)).functionField => t a) (hs.trans hr.symm)

end

end OAI.AlgebraicGeometry.Divisors.LineBundles.Affine.FractionField.BundleCycles.AffineFractionField
