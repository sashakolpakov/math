import OAI.AlgebraicGeometry.Cycles.Functoriality.SupportFields
import OAI.AlgebraicGeometry.Foundations.Scheme.ImmersionComplexPoints

/-! # Residue Degree -/

namespace OAI.AlgebraicGeometry.Cycles.Functoriality.ResidueDegree.Construction

noncomputable section

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

/-- Inserting an immersion after a morphism does not change residue degree. -/
theorem residueDegree_post_immersion {A B C : Scheme.{u}}
    (f : A ⟶ B) (i : B ⟶ C) [SurjectiveOnStalks i] (x : A) :
    (f ≫ i).residueDegree x = f.residueDegree x := by
  let : Algebra (C.residueField (i (f x))) (A.residueField x) :=
    ((f ≫ i).residueFieldMap x).hom.toAlgebra
  let : Algebra (B.residueField (f x)) (A.residueField x) :=
    (f.residueFieldMap x).hom.toAlgebra
  apply Algebra.finrank_eq_of_equiv_equiv
    (Foundations.Scheme.ImmersionComplexPoints.residueFieldIsoOfSurjectiveOnStalks i (f x)).commRingCatIsoToRingEquiv
    (RingEquiv.refl (A.residueField x))
  exact congrArg CommRingCat.Hom.hom (Scheme.residueFieldMap_comp f i x).symm

/-- Inserting an immersion before a morphism identifies the source residue
fields and therefore leaves the degree unchanged. -/
theorem residueDegree_pre_immersion {A B C : Scheme.{u}}
    (i : A ⟶ B) (f : B ⟶ C) [SurjectiveOnStalks i] (x : A) :
    (i ≫ f).residueDegree x = f.residueDegree (i x) := by
  let : Algebra (C.residueField (f (i x))) (B.residueField (i x)) :=
    (f.residueFieldMap (i x)).hom.toAlgebra
  let : Algebra (C.residueField (f (i x))) (A.residueField x) :=
    ((i ≫ f).residueFieldMap x).hom.toAlgebra
  symm
  apply Algebra.finrank_eq_of_equiv_equiv
    (RingEquiv.refl (C.residueField (f (i x))))
    (Foundations.Scheme.ImmersionComplexPoints.residueFieldIsoOfSurjectiveOnStalks i x).commRingCatIsoToRingEquiv
  exact congrArg CommRingCat.Hom.hom (Scheme.residueFieldMap_comp i f x)

theorem supportImageMap_residueDegree {X Y : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety}
    (f : X.toOver ⟶ Y.toOver) (hf : IsProper f.left)
    {p : ℕ} (Z : CycleClass.Geometric.DimensionCycles.DimensionCycleSupport X p) :
    (SupportMap.Construction.supportImageMap f hf Z).residueDegree (genericPoint Z.scheme) =
      f.left.residueDegree Z.genericPoint := by
  have h := congrArg
    (fun k : Z.scheme ⟶ Y.carrier => k.residueDegree (genericPoint Z.scheme))
    (SupportMap.Construction.supportImageMap_inclusion f hf Z)
  rw [residueDegree_post_immersion, residueDegree_pre_immersion,
    Z.inclusion_genericPoint] at h
  exact h

/-- At an integral scheme's generic point, quotienting its function-field
stalk by the maximal ideal is a canonical field isomorphism. -/
def functionFieldResidueIso (S : Scheme.{u}) [IsIntegral S] :
    S.functionField ≅ S.residueField (genericPoint S) :=
  (RingEquiv.ofBijective (S.residue (genericPoint S)).hom
    ⟨(show S.functionField →+* S.residueField (genericPoint S) from
      (S.residue (genericPoint S)).hom).injective,
      S.residue_surjective (genericPoint S)⟩).toCommRingCatIso

theorem functionFieldResidueIso_hom (S : Scheme.{u}) [IsIntegral S] :
    (functionFieldResidueIso S).hom = S.residue (genericPoint S) := rfl

/-- Naturality of residue maps identifies generic-field pullback with
the residue-field pullback of the same morphism. -/
theorem genericFieldMap_residue_square {S T : Scheme.{u}}
    [IsIntegral S] [IsIntegral T] (i : S ⟶ T)
    (hη : i (genericPoint S) = genericPoint T) :
    (functionFieldResidueIso T).hom ≫ (T.residueFieldCongr hη.symm).hom ≫
        i.residueFieldMap (genericPoint S) =
      FunctionFields.Construction.genericFieldMap i hη ≫ (functionFieldResidueIso S).hom := by
  change T.residue (genericPoint T) ≫ (T.residueFieldCongr hη.symm).hom ≫
      i.residueFieldMap (genericPoint S) =
    (T.presheaf.stalkCongr (Inseparable.of_eq hη.symm)).hom ≫
      i.stalkMap (genericPoint S) ≫ S.residue (genericPoint S)
  rw [← Category.assoc, Scheme.residue_residueFieldCongr,
    Category.assoc, Scheme.residue_residueFieldMap]

theorem genericFieldMap_finrank_eq_residueDegree {S T : Scheme.{u}}
    [IsIntegral S] [IsIntegral T] (i : S ⟶ T)
    (hη : i (genericPoint S) = genericPoint T) :
    letI := (FunctionFields.Construction.genericFieldMap i hη).hom.toAlgebra
    Module.finrank T.functionField S.functionField = i.residueDegree (genericPoint S) := by
  let := (FunctionFields.Construction.genericFieldMap i hη).hom.toAlgebra
  let := (i.residueFieldMap (genericPoint S)).hom.toAlgebra
  apply Algebra.finrank_eq_of_equiv_equiv
    ((functionFieldResidueIso T) ≪≫ T.residueFieldCongr hη.symm).commRingCatIsoToRingEquiv
    (functionFieldResidueIso S).commRingCatIsoToRingEquiv
  exact congrArg CommRingCat.Hom.hom (genericFieldMap_residue_square i hη)

theorem supportFunctionField_finrank_eq {X Y : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety}
    (f : X.toOver ⟶ Y.toOver) (hf : IsProper f.left)
    {p : ℕ} (Z : CycleClass.Geometric.DimensionCycles.DimensionCycleSupport X p) :
    letI := (SupportFields.Construction.supportFunctionFieldMap f hf Z).hom.toAlgebra
    Module.finrank (CycleClass.Geometric.GenericPoint.reducedSupportScheme (UnitCap.imageSupport f Z)).functionField
      Z.scheme.functionField = f.left.residueDegree Z.genericPoint := by
  exact (genericFieldMap_finrank_eq_residueDegree (SupportMap.Construction.supportImageMap f hf Z)
    (SupportMap.Construction.supportImageMap_genericPoint f hf Z)).trans (supportImageMap_residueDegree f hf Z)

theorem residueDegree_pos_of_dimension_eq {X Y : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety}
    (f : X.toOver ⟶ Y.toOver) (hf : IsProper f.left)
    {p : ℕ} (Z : CycleClass.Geometric.DimensionCycles.DimensionCycleSupport X p)
    (hdim : Foundations.Scheme.SupportDimension.supportTranscendenceDimension (UnitCap.imageSupport f Z) Y.structureMap =
      Foundations.Scheme.SupportDimension.supportTranscendenceDimension Z.1 X.structureMap) :
    0 < f.left.residueDegree Z.genericPoint := by
  let := (SupportFields.Construction.supportFunctionFieldMap f hf Z).hom.toAlgebra
  let := SupportFields.Construction.supportFunctionField_finite f hf Z hdim
  rw [← supportFunctionField_finrank_eq f hf Z]
  exact Module.finrank_pos

end

end OAI.AlgebraicGeometry.Cycles.Functoriality.ResidueDegree.Construction
