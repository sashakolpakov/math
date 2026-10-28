import OAI.AlgebraicGeometry.ComplexMultiplication.GlobalSections
import OAI.AlgebraicGeometry.ComplexMultiplication.HomPostcomp
import OAI.Algebra.Homology.Notation

/-! # Global Naturality -/

namespace OAI.AlgebraicGeometry.ComplexMultiplication.GlobalNaturality

noncomputable section

/-! # Naturality of global sections and hypercohomology -/

open _root_.CategoryTheory Limits _root_.AlgebraicGeometry ComplexPoint
open _root_.CochainComplex.HomComplex

variable (X : Over (Spec ↧ℂ))

local instance CMGlobalNaturality.localInstance1 : HasDerivedCategory (ComplexPoint.Basic.ComplexSchemePoint.AnalyticAdditiveSheaf X) :=
  HasDerivedCategory.standard _

/-- The canonical map from Hom-complex classes to the original hypercohomology. -/
def homComplexClassToHypercohomology
    (K : CochainComplex (ComplexPoint.Basic.ComplexSchemePoint.AnalyticAdditiveSheaf X) ℤ) (n : ℤ) :
    CohomologyClass (Cohomology.GlobalSections.TopCat.Sheaf.integerConstantSingleComplex ↧(ComplexPoint.Basic.ComplexSchemePoint X)) K n →+
      ComplexPoint.Basic.ComplexSchemePoint.Hypercohomology X K n :=
  let e : ComplexPoint.Basic.ComplexSchemePoint.Hypercohomology X K n ≃+
      ShiftedHom (DerivedCategory.Q.obj (ComplexPoint.Basic.ComplexSchemePoint.constantIntegerSheafComplexInt X))
        (DerivedCategory.Q.obj K) n :=
    { toEquiv := Localization.SmallShiftedHom.equiv
        (ComplexPoint.Basic.ComplexSchemePoint.analyticQuasiIsomorphisms X) DerivedCategory.Q
      map_add' := ComplexPoint.Basic.ComplexSchemePoint.hypercohomologyEquiv_add X K n }
  let pre : ShiftedHom
      (DerivedCategory.Q.obj (Cohomology.GlobalSections.TopCat.Sheaf.integerConstantSingleComplex ↧(ComplexPoint.Basic.ComplexSchemePoint X)))
      (DerivedCategory.Q.obj K) n →+
      ShiftedHom (DerivedCategory.Q.obj (ComplexPoint.Basic.ComplexSchemePoint.constantIntegerSheafComplexInt X))
        (DerivedCategory.Q.obj K) n :=
    { toFun f := DerivedCategory.Q.map (ComplexPoint.Basic.ComplexSchemePoint.constantIntegerSheafComplexIntIsoSingle X).hom ≫ f
      map_zero' := by simp
      map_add' _ _ := by simp only [Preadditive.comp_add] }
  e.symm.toAddMonoidHom.comp <| pre.comp
    (HomPostcomp.cohomologyClassToDerived _ K n)

lemma homComplexClassToHypercohomology_equiv
    (K : CochainComplex (ComplexPoint.Basic.ComplexSchemePoint.AnalyticAdditiveSheaf X) ℤ) (n : ℤ)
    (z : CohomologyClass (Cohomology.GlobalSections.TopCat.Sheaf.integerConstantSingleComplex ↧(ComplexPoint.Basic.ComplexSchemePoint X)) K n) :
    (Localization.SmallShiftedHom.equiv (ComplexPoint.Basic.ComplexSchemePoint.analyticQuasiIsomorphisms X) DerivedCategory.Q)
        (homComplexClassToHypercohomology X K n z) =
      DerivedCategory.Q.map (ComplexPoint.Basic.ComplexSchemePoint.constantIntegerSheafComplexIntIsoSingle X).hom ≫
        HomPostcomp.cohomologyClassToDerived _ K n z := by
  dsimp only [homComplexClassToHypercohomology, AddMonoidHom.comp_apply,
    AddEquiv.toAddMonoidHom_eq_coe, AddMonoidHom.coe_mk, ZeroHom.coe_mk]
  exact (Localization.SmallShiftedHom.equiv
    (ComplexPoint.Basic.ComplexSchemePoint.analyticQuasiIsomorphisms X) DerivedCategory.Q).apply_symm_apply _

/-- The canonical class map respects every chain map of target complexes. -/
lemma homComplexClassToHypercohomology_postcomp
    {K L : CochainComplex (ComplexPoint.Basic.ComplexSchemePoint.AnalyticAdditiveSheaf X) ℤ} (f : K ⟶ L) (n : ℤ)
    (z : CohomologyClass (Cohomology.GlobalSections.TopCat.Sheaf.integerConstantSingleComplex ↧(ComplexPoint.Basic.ComplexSchemePoint X)) K n) :
    homComplexClassToHypercohomology X L n
        (HomPostcomp.HomComplex.postcompClass f _ n z) =
      ComplexPoint.Basic.ComplexSchemePoint.hypercohomologyMap X f n (homComplexClassToHypercohomology X K n z) := by
  apply (Localization.SmallShiftedHom.equiv
    (ComplexPoint.Basic.ComplexSchemePoint.analyticQuasiIsomorphisms X) DerivedCategory.Q).injective
  rw [homComplexClassToHypercohomology_equiv]
  rw [HomPostcomp.cohomologyClassToDerived_postcomp]
  simp only [ComplexPoint.Basic.ComplexSchemePoint.hypercohomologyMap, AddMonoidHom.coe_mk, ZeroHom.coe_mk,
    Localization.SmallShiftedHom.equiv_comp, Localization.SmallShiftedHom.equiv_mk₀,
    ShiftedHom.comp_mk₀, homComplexClassToHypercohomology_equiv]
  exact (Category.assoc _ _ _).symm

/-- Evaluation at the constant section one, on Hom-complex classes. -/
def globalSectionsToHomComplexClass
    (K : CochainComplex (ComplexPoint.Basic.ComplexSchemePoint.AnalyticAdditiveSheaf X) ℤ) (n : ℤ) :
    (Cohomology.GlobalSections.TopCat.Sheaf.globalSectionsComplexInt ↧(ComplexPoint.Basic.ComplexSchemePoint X) K).homology n ≃+
      CohomologyClass (Cohomology.GlobalSections.TopCat.Sheaf.integerConstantSingleComplex ↧(ComplexPoint.Basic.ComplexSchemePoint X)) K n :=
  let e := HomologicalComplex.homologyMapIso
    (Cohomology.GlobalSections.TopCat.Sheaf.homComplexSingleIntegerIsoGlobalSections ↧(ComplexPoint.Basic.ComplexSchemePoint X) K) n
  e.symm.addCommGroupIsoToAddEquiv.trans <|
    CochainComplex.HomComplex.homologyAddEquiv _ K n

/-- The canonical map from actual global-section cohomology to hypercohomology. -/
def globalSectionsToHypercohomology
    (K : CochainComplex (ComplexPoint.Basic.ComplexSchemePoint.AnalyticAdditiveSheaf X) ℤ) (n : ℤ) :
    (Cohomology.GlobalSections.TopCat.Sheaf.globalSectionsComplexInt ↧(ComplexPoint.Basic.ComplexSchemePoint X) K).homology n →+
      ComplexPoint.Basic.ComplexSchemePoint.Hypercohomology X K n :=
  (homComplexClassToHypercohomology X K n).comp
    (globalSectionsToHomComplexClass X K n).toAddMonoidHom

set_option backward.isDefEq.respectTransparency false in
/-- Evaluation at one is natural for the actual sheaf complexes. -/
lemma homComplexSingleIntegerIsoGlobalSections_naturality
    {K L : CochainComplex (ComplexPoint.Basic.ComplexSchemePoint.AnalyticAdditiveSheaf X) ℤ} (f : K ⟶ L) :
    HomPostcomp.HomComplex.postcompMap f (Cohomology.GlobalSections.TopCat.Sheaf.integerConstantSingleComplex ↧(ComplexPoint.Basic.ComplexSchemePoint X)) ≫
        (Cohomology.GlobalSections.TopCat.Sheaf.homComplexSingleIntegerIsoGlobalSections ↧(ComplexPoint.Basic.ComplexSchemePoint X) L).hom =
      (Cohomology.GlobalSections.TopCat.Sheaf.homComplexSingleIntegerIsoGlobalSections ↧(ComplexPoint.Basic.ComplexSchemePoint X) K).hom ≫
        ((AlgebraicTopology.Sheaf.FlasqueBoundedBelow.TopCat.IsFlasque.BoundedBelowComplex.globalSectionsFunctor
          ↧(ComplexPoint.Basic.ComplexSchemePoint X)).mapHomologicalComplex ℤᵘᵖ).map f := by
  let : (AlgebraicTopology.Sheaf.FlasqueBoundedBelow.TopCat.IsFlasque.BoundedBelowComplex.globalSectionsFunctor
      ↧(ComplexPoint.Basic.ComplexSchemePoint X)).PreservesZeroMorphisms :=
    Functor.preservesZeroMorphisms_of_additive _
  let B : ComplexPoint.Basic.ComplexSchemePoint.AnalyticAdditiveSheaf X :=
    (AlgebraicTopology.Sheaf.Constant.TopCat.constantFunctor ↧(ComplexPoint.Basic.ComplexSchemePoint X)).obj (AddCommGrpCat.of ℤ)
  let Γ := (AlgebraicTopology.Sheaf.FlasqueBoundedBelow.TopCat.IsFlasque.BoundedBelowComplex.globalSectionsFunctor
    ↧(ComplexPoint.Basic.ComplexSchemePoint X)).mapHomologicalComplex ℤᵘᵖ
  let e : (preadditiveCoyoneda.obj (.op B)).mapHomologicalComplex ℤᵘᵖ ≅ Γ :=
    NatIso.mapHomologicalComplex
      (Cohomology.GlobalSections.TopCat.Sheaf.integerConstantHomIsoGlobalSectionsFunctor ↧(ComplexPoint.Basic.ComplexSchemePoint X)) ℤᵘᵖ
  change HomPostcomp.HomComplex.postcompMap f _ ≫
    (Algebra.Homology.HomComplexSingle.CochainComplex.HomComplex.fromSingleZeroIsoPreadditiveCoyoneda B L).hom ≫ (e.app L).hom =
      ((Algebra.Homology.HomComplexSingle.CochainComplex.HomComplex.fromSingleZeroIsoPreadditiveCoyoneda B K).hom ≫ (e.app K).hom) ≫ _
  rw [← Category.assoc, HomPostcomp.HomComplex.postcompMap_fromSingleZeroIsoPreadditiveCoyoneda,
    Category.assoc]
  have h : ((preadditiveCoyoneda.obj (.op B)).mapHomologicalComplex ℤᵘᵖ).map f ≫
      (e.app L).hom = (e.app K).hom ≫ Γ.map f := e.hom.naturality f
  rw [h]
  exact (Category.assoc _ _ _).symm

set_option backward.isDefEq.respectTransparency false in
/-- The class associated to a global cohomology element commutes with target maps. -/
lemma globalSectionsToHomComplexClass_naturality
    {K L : CochainComplex (ComplexPoint.Basic.ComplexSchemePoint.AnalyticAdditiveSheaf X) ℤ} (f : K ⟶ L) (n : ℤ)
    (x : (Cohomology.GlobalSections.TopCat.Sheaf.globalSectionsComplexInt ↧(ComplexPoint.Basic.ComplexSchemePoint X) K).homology n) :
    globalSectionsToHomComplexClass X L n
        (HomologicalComplex.homologyMap
          (((AlgebraicTopology.Sheaf.FlasqueBoundedBelow.TopCat.IsFlasque.BoundedBelowComplex.globalSectionsFunctor
            ↧(ComplexPoint.Basic.ComplexSchemePoint X)).mapHomologicalComplex ℤᵘᵖ).map f) n x) =
      HomPostcomp.HomComplex.postcompClass f _ n (globalSectionsToHomComplexClass X K n x) := by
  let A := Cohomology.GlobalSections.TopCat.Sheaf.integerConstantSingleComplex ↧(ComplexPoint.Basic.ComplexSchemePoint X)
  let eK := Cohomology.GlobalSections.TopCat.Sheaf.homComplexSingleIntegerIsoGlobalSections ↧(ComplexPoint.Basic.ComplexSchemePoint X) K
  let eL := Cohomology.GlobalSections.TopCat.Sheaf.homComplexSingleIntegerIsoGlobalSections ↧(ComplexPoint.Basic.ComplexSchemePoint X) L
  let Γ := (AlgebraicTopology.Sheaf.FlasqueBoundedBelow.TopCat.IsFlasque.BoundedBelowComplex.globalSectionsFunctor
    ↧(ComplexPoint.Basic.ComplexSchemePoint X)).mapHomologicalComplex ℤᵘᵖ
  have h : eK.inv ≫ HomPostcomp.HomComplex.postcompMap f A = Γ.map f ≫ eL.inv := by
    apply (cancel_mono eL.hom).1
    rw [Category.assoc, homComplexSingleIntegerIsoGlobalSections_naturality X]
    change eK.inv ≫ eK.hom ≫ Γ.map f = (Γ.map f ≫ eL.inv) ≫ eL.hom
    rw [eK.inv_hom_id_assoc, Category.assoc, eL.inv_hom_id]
    change Γ.map f = Γ.map f ≫ 𝟙 (Γ.obj L)
    exact (Category.comp_id _).symm
  have hh : HomologicalComplex.homologyMap (HomPostcomp.HomComplex.postcompMap f A) n
      (HomologicalComplex.homologyMap eK.inv n x) =
    HomologicalComplex.homologyMap eL.inv n
      (HomologicalComplex.homologyMap (Γ.map f) n x) := by
    simpa only [HomologicalComplex.homologyMap_comp, AddCommGrpCat.comp_apply] using!
      ConcreteCategory.congr_hom
        (congrArg (fun g ↦ HomologicalComplex.homologyMap g n) h) x
  change homologyAddEquiv A L n
      (HomologicalComplex.homologyMap eL.inv n (HomologicalComplex.homologyMap (Γ.map f) n x)) =
    HomPostcomp.HomComplex.postcompClass f A n
      (homologyAddEquiv A K n (HomologicalComplex.homologyMap eK.inv n x))
  rw [← hh, HomPostcomp.HomComplex.homologyAddEquiv_postcompMap]

/-- The canonical global-section comparison respects every actual chain map. -/
lemma globalSectionsToHypercohomology_naturality
    {K L : CochainComplex (ComplexPoint.Basic.ComplexSchemePoint.AnalyticAdditiveSheaf X) ℤ} (f : K ⟶ L) (n : ℤ)
    (x : (Cohomology.GlobalSections.TopCat.Sheaf.globalSectionsComplexInt ↧(ComplexPoint.Basic.ComplexSchemePoint X) K).homology n) :
    globalSectionsToHypercohomology X L n
        (HomologicalComplex.homologyMap
          (((AlgebraicTopology.Sheaf.FlasqueBoundedBelow.TopCat.IsFlasque.BoundedBelowComplex.globalSectionsFunctor
            ↧(ComplexPoint.Basic.ComplexSchemePoint X)).mapHomologicalComplex ℤᵘᵖ).map f) n x) =
      ComplexPoint.Basic.ComplexSchemePoint.hypercohomologyMap X f n (globalSectionsToHypercohomology X K n x) := by
  change homComplexClassToHypercohomology X L n
      (globalSectionsToHomComplexClass X L n _) = _
  rw [globalSectionsToHomComplexClass_naturality,
    homComplexClassToHypercohomology_postcomp]
  rfl

end

end OAI.AlgebraicGeometry.ComplexMultiplication.GlobalNaturality
