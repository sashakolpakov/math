import OAI.AlgebraicGeometry.ComplexMultiplication.Reference.RationalCoefficient
import OAI.AlgebraicGeometry.ComplexMultiplication.IntrinsicReferenceGlobalCohomology

/-! # Rational Coefficient Global Units -/

namespace OAI.AlgebraicGeometry.ComplexMultiplication.Reference.RationalCoefficientGlobalUnits

noncomputable section

/-! # Original raw global coefficient classes and sheaf units have the actual normalization -/

open _root_.CategoryTheory _root_.TopologicalSpace Opposite OAI.AlgebraicTopology.Singular

/-- The genuine original coefficient map evaluated on the top open subset. -/
def originalRationalToComplexRawGlobalMap (Y : TopCat.{0}) :
    AlgebraicTopology.Singular.SheafSubdivisionCochain.globalRawSingularCochainComplex ℚ Y ⟶ AlgebraicTopology.Singular.SheafSubdivisionCochain.globalRawSingularCochainComplex ℂ Y :=
  ((((evaluation (Opens Y)ᵒᵖ AddCommGrpCat).obj (op ⊤)).mapHomologicalComplex
    (ComplexShape.up ℕ))).map (RationalCoefficient.originalRationalToComplexSingularPresheafMap Y)

set_option backward.isDefEq.respectTransparency false in
/-- Ambient chain evaluation retains the actual rational-to-complex coefficient map. -/
theorem originalRationalToComplexRawGlobalMap_square (Y : TopCat.{0}) :
    (IntrinsicReferenceGlobalCohomology.nativeSingularRawGlobalBridgeIso ℚ Y).hom ≫ originalRationalToComplexRawGlobalMap Y =
      Coefficient.ConcreteRationalNaturality.actualAdditiveRationalToComplexCochainMap Y ≫ (IntrinsicReferenceGlobalCohomology.nativeSingularRawGlobalBridgeIso ℂ Y).hom := by
  apply HomologicalComplex.hom_ext
  intro n
  rw [HomologicalComplex.comp_f, HomologicalComplex.comp_f,
    IntrinsicReferenceGlobalCohomology.nativeSingularRawGlobalBridgeIso_hom_f, IntrinsicReferenceGlobalCohomology.nativeSingularRawGlobalBridgeIso_hom_f]
  have hp : (forget₂ (ModuleCat ℚ) AddCommGrpCat).map
      ((SingularCochainBridge.singularCochainBridgeIso ℚ (TopCat.of (⊤ : Opens Y))).hom.f n) ≫
        (originalRationalToComplexRawGlobalMap Y).f n =
    (Coefficient.ConcreteRationalNaturality.actualAdditiveRationalToComplexCochainMap (TopCat.of (⊤ : Opens Y))).f n ≫
      (forget₂ (ModuleCat ℂ) AddCommGrpCat).map
        ((SingularCochainBridge.singularCochainBridgeIso ℂ (TopCat.of (⊤ : Opens Y))).hom.f n) :=
    congrArg (fun h => (h.f n).app (op ⊤))
      (RationalCoefficient.originalRationalToComplexSingularPresheafMap_square Y)
  change (forget₂ (ModuleCat ℚ) AddCommGrpCat).map
      ((AlgebraicTopology.Cohomology.Singular.Functor.singularPullback (ModuleCat.of ℚ ℚ) (Opens.inclusion' (⊤ : Opens Y))).f n) ≫
        ((forget₂ (ModuleCat ℚ) AddCommGrpCat).map
          ((SingularCochainBridge.singularCochainBridgeIso ℚ (TopCat.of (⊤ : Opens Y))).hom.f n) ≫
            (originalRationalToComplexRawGlobalMap Y).f n) =
    ((Coefficient.ConcreteRationalNaturality.actualAdditiveRationalToComplexCochainMap Y).f n ≫
      (forget₂ (ModuleCat ℂ) AddCommGrpCat).map
        ((AlgebraicTopology.Cohomology.Singular.Functor.singularPullback (ModuleCat.of ℂ ℂ) (Opens.inclusion' (⊤ : Opens Y))).f n)) ≫
          (forget₂ (ModuleCat ℂ) AddCommGrpCat).map
            ((SingularCochainBridge.singularCochainBridgeIso ℂ (TopCat.of (⊤ : Opens Y))).hom.f n)
  rw [hp, ← Category.assoc]
  exact congrArg (fun h => h ≫ (forget₂ (ModuleCat ℂ) AddCommGrpCat).map
      ((SingularCochainBridge.singularCochainBridgeIso ℂ (TopCat.of (⊤ : Opens Y))).hom.f n))
    (congrArg (fun h => h.f n)
      (Coefficient.ConcreteRationalNaturality.actualAdditiveRationalToComplexCochainMap_naturality (Opens.inclusion' (⊤ : Opens Y))))

set_option backward.isDefEq.respectTransparency false in
/-- The original raw cohomology coefficient map is the actual ordinary coefficient inclusion. -/
theorem originalRationalToComplexRawGlobalMap_homology (Y : TopCat.{0}) (n : ℕ)
    (z : AlgebraicTopology.Cohomology.Singular.Basic.singularCohomology (ModuleCat.of ℚ ℚ) Y n) :
    HomologicalComplex.homologyMap (originalRationalToComplexRawGlobalMap Y) n
        ((Coefficient.SheafComparison.rawSingularHomologyIso ℚ Y n).inv (SingularCochainBridge.singularCohomologyBridgeEquiv ℚ Y n z)) =
      (Coefficient.SheafComparison.rawSingularHomologyIso ℂ Y n).inv
        (SingularCochainBridge.singularCohomologyBridgeEquiv ℂ Y n (AlgebraicTopology.Cohomology.Singular.RationalComplex.rationalToComplexCohomology Y n z)) := by
  let HQ := ((AlgebraicTopology.Cohomology.Singular.Basic.singularCochains (ModuleCat.of ℚ ℚ) Y).sc n).mapHomologyIso
    (forget₂ (ModuleCat ℚ) AddCommGrpCat)
  let HC := ((AlgebraicTopology.Cohomology.Singular.Basic.singularCochains (ModuleCat.of ℂ ℂ) Y).sc n).mapHomologyIso
    (forget₂ (ModuleCat ℂ) AddCommGrpCat)
  let a := HQ.inv z
  have ha : HQ.hom a = z := ConcreteCategory.congr_hom HQ.inv_hom_id z
  have he := ConcreteCategory.congr_hom
    (Coefficient.ConcreteRationalNaturality.actualAdditiveRationalToComplexCochainMap_homology Y n) a
  change HC.hom (HomologicalComplex.homologyMap
      (Coefficient.ConcreteRationalNaturality.actualAdditiveRationalToComplexCochainMap Y) n a) = AlgebraicTopology.Cohomology.Singular.RationalComplex.rationalToComplexCohomology Y n (HQ.hom a) at he
  rw [ha] at he
  have hs := congrArg (fun h => HomologicalComplex.homologyMap h n)
    (originalRationalToComplexRawGlobalMap_square Y)
  simp only [HomologicalComplex.homologyMap_comp] at hs
  have hv := ConcreteCategory.congr_hom hs a
  change HomologicalComplex.homologyMap (originalRationalToComplexRawGlobalMap Y) n
      (HomologicalComplex.homologyMap (IntrinsicReferenceGlobalCohomology.nativeSingularRawGlobalBridgeIso ℚ Y).hom n a) =
    HomologicalComplex.homologyMap (IntrinsicReferenceGlobalCohomology.nativeSingularRawGlobalBridgeIso ℂ Y).hom n
      (HomologicalComplex.homologyMap (Coefficient.ConcreteRationalNaturality.actualAdditiveRationalToComplexCochainMap Y) n a) at hv
  rw [IntrinsicReferenceGlobalCohomology.nativeSingularRawGlobalBridgeIso_homology_apply,
    IntrinsicReferenceGlobalCohomology.nativeSingularRawGlobalBridgeIso_homology_apply] at hv
  change HomologicalComplex.homologyMap (originalRationalToComplexRawGlobalMap Y) n
      ((Coefficient.SheafComparison.rawSingularHomologyIso ℚ Y n).inv (SingularCochainBridge.singularCohomologyBridgeEquiv ℚ Y n (HQ.hom a))) =
    (Coefficient.SheafComparison.rawSingularHomologyIso ℂ Y n).inv (SingularCochainBridge.singularCohomologyBridgeEquiv ℂ Y n
      (HC.hom (HomologicalComplex.homologyMap (Coefficient.ConcreteRationalNaturality.actualAdditiveRationalToComplexCochainMap Y) n a))) at hv
  rwa [ha, he] at hv

set_option backward.isDefEq.respectTransparency false in
/-- The actual raw-to-sheaf global unit commutes with coefficient inclusion. -/
theorem originalRationalToComplexRawGlobalMap_unit (Y : TopCat.{0}) :
    originalRationalToComplexRawGlobalMap Y ≫ AlgebraicTopology.Singular.SheafSubdivisionCochain.topOpenToGlobalSingularCochainSheafComplex ℂ Y =
      AlgebraicTopology.Singular.SheafSubdivisionCochain.topOpenToGlobalSingularCochainSheafComplex ℚ Y ≫
        ((AlgebraicTopology.Sheaf.FlasqueBoundedBelow.TopCat.IsFlasque.BoundedBelowComplex.globalSectionsFunctor Y).mapHomologicalComplex
          (ComplexShape.up ℕ)).map (RationalCoefficient.originalRationalToComplexSingularSheafMap Y) := by
  apply HomologicalComplex.hom_ext
  intro n
  rw [HomologicalComplex.comp_f, HomologicalComplex.comp_f,
    AlgebraicTopology.Singular.GlobalRestriction.topOpenToGlobalSingularCochainSheafComplex_f, AlgebraicTopology.Singular.GlobalRestriction.topOpenToGlobalSingularCochainSheafComplex_f]
  exact NatTrans.congr_app
    (toSheafify_naturality (Opens.grothendieckTopology Y)
      ((RationalCoefficient.originalRationalToComplexSingularPresheafMap Y).f n)) (op ⊤)

end

end OAI.AlgebraicGeometry.ComplexMultiplication.Reference.RationalCoefficientGlobalUnits
