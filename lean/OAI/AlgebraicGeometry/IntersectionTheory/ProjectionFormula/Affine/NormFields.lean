import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Affine.FractionField
import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Affine.FunctionFields

/-! # Norm Fields -/

namespace OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Affine.NormFields

noncomputable section

/-! The finite affine norm-divisor formula in any specified compatible
fraction fields, retaining the native scheme map and all divisor branches. -/

set_option backward.isDefEq.respectTransparency false

open _root_.CategoryTheory _root_.AlgebraicGeometry

open OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Affine.FractionField OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Affine.DivisorNorm OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Affine.FunctionFields OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.CyclePushforward

universe u

local instance (A : Type u) [CommRing A] [IsDomain A] :
    Algebra A (Spec (.of A)).functionField :=
  (StructureSheaf.toStalk A (genericPoint (Spec (.of A)))).hom.toAlgebra

theorem fractionField_comparison (R : Type u) [CommRing R] [IsDedekindDomain R]
    (K : Type u) [Field K] [Algebra R K] [IsFractionRing R K] (g : FractionRing R) :
    (FractionField.fieldIso R K).hom (Order.affineFunctionFieldIso R g) = FractionRing.algEquiv R K g := by
  have h : (FractionField.fieldIso R K).hom.hom.comp (Order.affineFunctionFieldIso R).toRingHom =
      (FractionRing.algEquiv R K).toRingHom := by
    apply IsFractionRing.ringHom_ext (A := R)
    intro a
    change (FractionField.fieldIso R K).hom
      (Order.affineFunctionFieldIso R (algebraMap R (FractionRing R) a)) =
      FractionRing.algEquiv R K (algebraMap R (FractionRing R) a)
    rw [AlgEquiv.commutes, AlgEquiv.commutes]
    exact congrArg (fun t : CommRingCat.of R ⟶ CommRingCat.of K => t a) (FractionField.toStalk_fieldIso R K)
  exact congrArg (fun t : FractionRing R →+* K => t g) h

theorem schemeOrder_closed (R : Type u) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    (K : Type u) [Field K] [Algebra R K] [IsFractionRing R K]
    (g : (Spec (.of R)).functionField) :
    (Spec (.of R)).ord g (IsLocalRing.closedPoint R) =
      WithZero.log (Ring.ordFrac R ((FractionField.fieldIso R K).hom g)) := by
  obtain ⟨a, rfl⟩ := (Order.affineFunctionFieldIso R).surjective g
  rw [fractionField_comparison]
  change (Spec (.of R)).ord (Order.affineFunctionFieldIso R a)
    (Order.branchPoint R (Order.closedBranch R)) = _
  rw [Order.schemeOrder_closed]
  exact (congrArg WithZero.log (OrderQuotientTransport.ordFrac_equiv (RingEquiv.refl R)
    (FractionRing.algEquiv R K).toRingEquiv (fun r => (FractionRing.algEquiv R K).commutes r) a)).symm

variable (R S : Type u) [CommRing R] [CommRing S] [IsDedekindDomain R] [IsDedekindDomain S]
  [Algebra R S] [Module.IsTorsionFree R S]
  (K L : Type u) [Field K] [Field L] [Algebra R K] [IsFractionRing R K]
  [Algebra S L] [IsFractionRing S L] [Algebra R L] [IsScalarTower R S L]
  [Algebra K L] [IsScalarTower R K L]

theorem fieldMap_square :
    (FractionField.fieldIso R K).hom ≫ CommRingCat.ofHom (algebraMap K L) =
      FunctionFields.affineFieldMap R S ≫ (FractionField.fieldIso S L).hom := by
  let : IsFractionRing R (Spec (.of R)).functionField :=
    functionField_isFractionRing_of_affine (.of R)
  apply CommRingCat.hom_ext
  apply IsFractionRing.ringHom_ext (A := R)
  intro a
  have hs := congrArg (fun t : CommRingCat.of R ⟶ (Spec (.of S)).functionField =>
    (FractionField.fieldIso S L).hom (t a)) (FunctionFields.affineFieldMap_toStalk R S)
  have hr := congrArg (fun t : CommRingCat.of R ⟶ CommRingCat.of K => t a) (FractionField.toStalk_fieldIso R K)
  have ht := congrArg (fun t : CommRingCat.of S ⟶ CommRingCat.of L => t (algebraMap R S a))
    (FractionField.toStalk_fieldIso S L)
  change (FractionField.fieldIso R K).hom (algebraMap R (Spec (.of R)).functionField a) = algebraMap R K a at hr
  change (FractionField.fieldIso S L).hom (FunctionFields.affineFieldMap R S (algebraMap R (Spec (.of R)).functionField a)) =
    (FractionField.fieldIso S L).hom (algebraMap S (Spec (.of S)).functionField (algebraMap R S a)) at hs
  change (FractionField.fieldIso S L).hom (algebraMap S (Spec (.of S)).functionField (algebraMap R S a)) =
    algebraMap S L (algebraMap R S a) at ht
  change algebraMap K L ((FractionField.fieldIso R K).hom (algebraMap R (Spec (.of R)).functionField a)) =
    (FractionField.fieldIso S L).hom (FunctionFields.affineFieldMap R S (algebraMap R (Spec (.of R)).functionField a))
  rw [hr, hs, ht, ← IsScalarTower.algebraMap_apply, ← IsScalarTower.algebraMap_apply]

theorem norm_comparison (g : (Spec (.of S)).functionField) :
    letI := (FunctionFields.affineFieldMap R S).hom.toAlgebra
    (FractionField.fieldIso R K).hom (Algebra.norm (Spec (.of R)).functionField g) =
      Algebra.norm K ((FractionField.fieldIso S L).hom g) := by
  let := (FunctionFields.affineFieldMap R S).hom.toAlgebra
  have h := Algebra.norm_eq_of_equiv_equiv (FractionField.fieldIso R K).commRingCatIsoToRingEquiv
    (FractionField.fieldIso S L).commRingCatIsoToRingEquiv
    (congrArg CommRingCat.Hom.hom (fieldMap_square R S K L)) g
  exact (RingEquiv.eq_symm_apply (FractionField.fieldIso R K).commRingCatIsoToRingEquiv).mp h

/-- Native pushforward has coefficient equal to the order of the norm in
the specified base fraction field. -/
theorem principalDivisor_pushforward [IsDiscreteValuationRing R] [Module.Finite R S]
    [PerfectField (FractionRing R)] (g : (Spec (.of S)).functionField) (hg : g ≠ 0) :
    CyclePushforward.pointPushforward (Spec.map (CommRingCat.ofHom (algebraMap R S)))
      (DivisorNorm.rationalPrincipalDivisor (Spec (.of S)) g) =
        Finsupp.single (IsLocalRing.closedPoint R : Spec (.of R))
          ((WithZero.log (Ring.ordFrac R (Algebra.norm K ((FractionField.fieldIso S L).hom g))) : ℤ) : ℚ) := by
  let := (FunctionFields.affineFieldMap R S).hom.toAlgebra
  rw [FunctionFields.principalDivisor_native_norm R S g hg, DivisorNorm.rationalPrincipalDivisor_local]
  change Finsupp.single (IsLocalRing.closedPoint R : Spec (.of R))
    ((Spec (.of R)).ord (Algebra.norm (Spec (.of R)).functionField g)
      (IsLocalRing.closedPoint R) : ℚ) = _
  rw [schemeOrder_closed R K, norm_comparison R S K L]

end

end OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Affine.NormFields
