import OAI.AlgebraicGeometry.Comparison.Betti.Analytic.RealizationNaturality
import OAI.AlgebraicGeometry.Comparison.Betti.Algebraic.ExtensionNaturality
import OAI.AlgebraicGeometry.Comparison.Betti.ExtensionCoherence

/-! # Naturality Int -/

namespace OAI.AlgebraicGeometry.Comparison.Betti.Analytic.NaturalityInt

noncomputable section

section

/-! The actual analytic direct-image square on the preserved integer complexes. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry _root_.TopologicalSpace
open scoped _root_.Manifold ContDiff

attribute [local instance] RealizationNaturality.nativePointSpaceCharted RealizationNaturality.nativePointSpaceManifold

abbrev schemeAnalyticFormsNat (Z : Over Foundations.Scheme.ProjectiveSpace.complexBase) [IsIntegral Z.left] [Smooth Z.hom] :
    CochainComplex (Betti.Smooth.SheafMap.AnalyticComplexSheaves Z) ℕ :=
  Analysis.DifferentialForms.Manifold.SheafDeRham.manifoldDeRhamSheafComplex (RegularSmoothness.NativeModel Z) (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints Z)

variable {X Y : Over Foundations.Scheme.ProjectiveSpace.complexBase} [IsIntegral X.left] [Smooth X.hom]
  [IsIntegral Y.left] [Smooth Y.hom] (f : X ⟶ Y)

def schemeAnalyticDeRhamDirectImage :
    (schemeAnalyticFormsNat Y :
      CochainComplex (Betti.Smooth.SheafMap.AnalyticComplexSheaves Y) ℕ) ⟶
    ((TopologicalSheafPullback.sheafDirectImage (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPointsFunctor.map f)).mapHomologicalComplex
      (ComplexShape.up ℕ)).obj (schemeAnalyticFormsNat X) :=
  SheafPullback.Smooth.analyticDeRhamDirectImage (E := RegularSmoothness.NativeModel X) (F := RegularSmoothness.NativeModel Y)
    (M := Betti.Scheme.schemePointSpace X) (N := Betti.Scheme.schemePointSpace Y) (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPointsFunctor.map f)
    (ComplexPoints.Analytic.IntrinsicSmoothSchemeMaps.real_contMDiff_nativeScheme_map f ∞)

def schemeAnalyticDeRhamDirectImageInt : De.analyticDeRhamSheafComplexInt Y ⟶
    ((TopologicalSheafPullback.sheafDirectImage (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPointsFunctor.map f)).mapHomologicalComplex
      (ComplexShape.up ℤ)).obj (De.analyticDeRhamSheafComplexInt X) :=
  HomologicalComplex.extendMap (schemeAnalyticDeRhamDirectImage f) (ComplexShape.embeddingUpIntGE 0) ≫
    (Complex.Extension.mapExtendIso (TopologicalSheafPullback.sheafDirectImage (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPointsFunctor.map f))
      (ComplexShape.embeddingUpIntGE 0)
      (schemeAnalyticFormsNat X)).inv

omit [IsIntegral Y.left] [Smooth Y.hom] in
theorem analyticExtensionOptionSquare (o : Option ℕ) :
    (Complex.Extension.mapXIso (Betti.Smooth.SheafMap.analytificationPushforward Y)
      (((TopologicalSheafPullback.sheafDirectImage (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPointsFunctor.map f)).mapHomologicalComplex
        (ComplexShape.up ℕ)).obj (schemeAnalyticFormsNat X)) o).inv ≫
      (Betti.Smooth.SheafMap.analytificationPushforward Y).map
        (Complex.Extension.mapXIso (TopologicalSheafPullback.sheafDirectImage (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPointsFunctor.map f))
          (schemeAnalyticFormsNat X) o).inv =
    (Complex.Extension.mapXIso (Algebraic.Sheaves.directImage f) (Betti.Smooth.SheafMap.zariskiSmoothSheafComplex X) o).inv ≫
      (Algebraic.Sheaves.directImage f).map
        (Complex.Extension.mapXIso (Betti.Smooth.SheafMap.analytificationPushforward X) (schemeAnalyticFormsNat X) o).inv := by
  cases o with
  | none => exact (isZero_zero (Algebraic.Sheaves.ComplexSheaves Y)).eq_of_src _ _
  | some n =>
    change 𝟙 _ ≫ (Betti.Smooth.SheafMap.analytificationPushforward Y).map
        (𝟙 ((TopologicalSheafPullback.sheafDirectImage (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPointsFunctor.map f)).obj
          ((schemeAnalyticFormsNat X).X n))) =
      𝟙 _ ≫ (Algebraic.Sheaves.directImage f).map (𝟙 ((Betti.Smooth.SheafMap.zariskiSmoothSheafComplex X).X n))
    erw [(Betti.Smooth.SheafMap.analytificationPushforward Y).map_id]
    rfl

omit [IsIntegral Y.left] [Smooth Y.hom] in
theorem analyticExtensionComparisonSquare :
    (Complex.Extension.mapExtendIso (Betti.Smooth.SheafMap.analytificationPushforward Y) (ComplexShape.embeddingUpIntGE 0)
      (((TopologicalSheafPullback.sheafDirectImage (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPointsFunctor.map f)).mapHomologicalComplex
        (ComplexShape.up ℕ)).obj (schemeAnalyticFormsNat X))).inv ≫
      ((Betti.Smooth.SheafMap.analytificationPushforward Y).mapHomologicalComplex (ComplexShape.up ℤ)).map
        (Complex.Extension.mapExtendIso (TopologicalSheafPullback.sheafDirectImage (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPointsFunctor.map f))
          (ComplexShape.embeddingUpIntGE 0) (schemeAnalyticFormsNat X)).inv =
    (Complex.Extension.mapExtendIso (Algebraic.Sheaves.directImage f) (ComplexShape.embeddingUpIntGE 0)
      (Betti.Smooth.SheafMap.zariskiSmoothSheafComplex X)).inv ≫
      ((Algebraic.Sheaves.directImage f).mapHomologicalComplex (ComplexShape.up ℤ)).map
        (Complex.Extension.mapExtendIso (Betti.Smooth.SheafMap.analytificationPushforward X) (ComplexShape.embeddingUpIntGE 0)
          (schemeAnalyticFormsNat X)).inv := by
  apply HomologicalComplex.Hom.ext
  funext i
  exact analyticExtensionOptionSquare f ((ComplexShape.embeddingUpIntGE 0).r i)

theorem analyticExtensionSquare :
    (Complex.Extension.mapExtendIso (Betti.Smooth.SheafMap.analytificationPushforward Y) (ComplexShape.embeddingUpIntGE 0)
      (schemeAnalyticFormsNat Y)).inv ≫
      ((Betti.Smooth.SheafMap.analytificationPushforward Y).mapHomologicalComplex (ComplexShape.up ℤ)).map
        (schemeAnalyticDeRhamDirectImageInt f) =
    HomologicalComplex.extendMap (RealizationNaturality.zariskiAnalyticDirectPullback f) (ComplexShape.embeddingUpIntGE 0) ≫
      (Complex.Extension.mapExtendIso (Algebraic.Sheaves.directImage f) (ComplexShape.embeddingUpIntGE 0)
        (Betti.Smooth.SheafMap.zariskiSmoothSheafComplex X)).inv ≫
      ((Algebraic.Sheaves.directImage f).mapHomologicalComplex (ComplexShape.up ℤ)).map
        (Complex.Extension.mapExtendIso (Betti.Smooth.SheafMap.analytificationPushforward X)
          (ComplexShape.embeddingUpIntGE 0)
          (schemeAnalyticFormsNat X)).inv := by
  let e := ComplexShape.embeddingUpIntGE 0
  let AY := Betti.Smooth.SheafMap.analytificationPushforward Y
  let AX := Betti.Smooth.SheafMap.analytificationPushforward X
  let D := Algebraic.Sheaves.directImage f
  let P : Betti.Smooth.SheafMap.AnalyticComplexSheaves X ⥤ Betti.Smooth.SheafMap.AnalyticComplexSheaves Y :=
    TopologicalSheafPullback.sheafDirectImage (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPointsFunctor.map f)
  let : P.Additive := TopologicalSheafPullback.sheafDirectImageAdditive (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPointsFunctor.map f)
  let K : CochainComplex (Betti.Smooth.SheafMap.AnalyticComplexSheaves X) ℕ :=
    schemeAnalyticFormsNat X
  let L : CochainComplex (Betti.Smooth.SheafMap.AnalyticComplexSheaves Y) ℕ :=
    schemeAnalyticFormsNat Y
  let q := schemeAnalyticDeRhamDirectImage f
  let AYI := AY.mapHomologicalComplex (ComplexShape.up ℤ)
  let DI := D.mapHomologicalComplex (ComplexShape.up ℤ)
  change (Complex.Extension.mapExtendIso AY e L).inv ≫
      AYI.map (HomologicalComplex.extendMap q e ≫ (Complex.Extension.mapExtendIso P e K).inv) =
    HomologicalComplex.extendMap ((AY.mapHomologicalComplex (ComplexShape.up ℕ)).map q) e ≫
      (Complex.Extension.mapExtendIso D e ((AX.mapHomologicalComplex (ComplexShape.up ℕ)).obj K)).inv ≫
      DI.map (Complex.Extension.mapExtendIso AX e K).inv
  erw [AYI.map_comp (HomologicalComplex.extendMap q e),
    ← Category.assoc (Complex.Extension.mapExtendIso AY e L).inv,
    ExtensionCoherence.Complex.mapExtendIso_inv_naturality AY e q,
    Category.assoc]
  exact congrArg
    (fun k => HomologicalComplex.extendMap ((AY.mapHomologicalComplex (ComplexShape.up ℕ)).map q) e ≫ k)
    (analyticExtensionComparisonSquare f)

end

/-! Naturality of the actual algebraic-to-analytic map with its original source. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry _root_.TopologicalSpace

attribute [local instance] AlgebraicTopology.Cohomology.Singular.StalkExactnessAt.stalkModulesForget₂PreservesFilteredColimits
  AlgebraicTopology.Cohomology.Singular.StalkExactnessAt.stalkModulesForgetPreservesFilteredColimits InjectiveFlasque.complexModuleLimits

/-- A component of the original realization, including its canonical zero degrees. -/
def algebraicOptionAnalyticMap (Z : Over Foundations.Scheme.ProjectiveSpace.complexBase) [IsIntegral Z.left] [Smooth Z.hom]
    (o : Option ℕ) :
    (presheafToSheaf (Opens.grothendieckTopology Z.left) (ModuleCat.{0} ℂ)).obj
        (Algebraic.ExtensionNaturality.algebraicOptionPresheaf Z o) ⟶
      (Betti.Smooth.SheafMap.analytificationPushforward Z).obj (HomologicalComplex.extend.X (schemeAnalyticFormsNat Z) o) :=
  Algebraic.ExtensionNaturality.algebraicOptionSheafHom Z o ≫ HomologicalComplex.extend.mapX (Betti.Smooth.SheafMap.algebraicToSmoothSheafMap Z) o ≫
    (Complex.Extension.mapXIso (Betti.Smooth.SheafMap.analytificationPushforward Z) (schemeAnalyticFormsNat Z) o).inv

theorem algebraicOptionAnalyticMap_some (Z : Over Foundations.Scheme.ProjectiveSpace.complexBase) [IsIntegral Z.left] [Smooth Z.hom]
    (n : ℕ) : algebraicOptionAnalyticMap Z (some n) = (Betti.Smooth.SheafMap.algebraicToSmoothSheafMap Z).f n := by
  change Algebraic.ExtensionNaturality.algebraicOptionSheafHom Z (some n) ≫ (Betti.Smooth.SheafMap.algebraicToSmoothSheafMap Z).f n ≫ 𝟙 _ = _
  erw [Algebraic.ExtensionNaturality.algebraicOptionSheafHom_some Z n, Category.id_comp, Category.comp_id]

variable {X Y : Over Foundations.Scheme.ProjectiveSpace.complexBase} [IsIntegral X.left] [Smooth X.hom]
  [IsIntegral Y.left] [Smooth Y.hom] (f : X ⟶ Y)

def analyticOptionDirectImage (o : Option ℕ) :
    HomologicalComplex.extend.X (schemeAnalyticFormsNat Y) o ⟶
      (TopologicalSheafPullback.sheafDirectImage (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPointsFunctor.map f)).obj
        (HomologicalComplex.extend.X (C := Betti.Smooth.SheafMap.AnalyticComplexSheaves X) (schemeAnalyticFormsNat X) o) :=
  HomologicalComplex.extend.mapX (schemeAnalyticDeRhamDirectImage f) o ≫
    (Complex.Extension.mapXIso (TopologicalSheafPullback.sheafDirectImage (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPointsFunctor.map f))
      (schemeAnalyticFormsNat X) o).inv

theorem analyticOptionDirectImage_some (n : ℕ) :
    analyticOptionDirectImage f (some n) = (schemeAnalyticDeRhamDirectImage f).f n := by
  change (schemeAnalyticDeRhamDirectImage f).f n ≫ 𝟙 _ = _
  exact Category.comp_id _

theorem algebraicOptionAnalyticMap_naturality (o : Option ℕ) :
    algebraicOptionAnalyticMap Y o ≫ (Betti.Smooth.SheafMap.analytificationPushforward Y).map (analyticOptionDirectImage f o) =
      Algebraic.ExtensionNaturality.algebraicOptionSheafDirectImage f o ≫ (Algebraic.Sheaves.directImage f).map (algebraicOptionAnalyticMap X o) := by
  cases o with
  | none =>
    exact ((Algebraic.Sheaves.directImage f).map_isZero ((Betti.Smooth.SheafMap.analytificationPushforward X).map_isZero
      (isZero_zero (Betti.Smooth.SheafMap.AnalyticComplexSheaves X)))).eq_of_tgt _ _
  | some n =>
    erw [algebraicOptionAnalyticMap_some Y n, algebraicOptionAnalyticMap_some X n,
      analyticOptionDirectImage_some f n]
    exact congrArg (fun k => k.f n) (RealizationNaturality.algebraicToSmoothSheafMap_analytic_naturality f)

/-- The original integer-indexed comparison commutes with the actual direct images. -/
theorem algebraicToAnalyticDirectImageInt_naturality :
    De.algebraicToAnalyticDirectImageInt Y ≫
      ((Betti.Smooth.SheafMap.analytificationPushforward Y).mapHomologicalComplex (ComplexShape.up ℤ)).map
        (schemeAnalyticDeRhamDirectImageInt f) =
    OpenForms.deRhamSheafDirectImageInt f ≫
      ((Algebraic.Sheaves.directImage f).mapHomologicalComplex (ComplexShape.up ℤ)).map
        (De.algebraicToAnalyticDirectImageInt X) := by
  apply HomologicalComplex.Hom.ext
  funext i
  exact algebraicOptionAnalyticMap_naturality f ((ComplexShape.embeddingUpIntGE 0).r i)

end

end OAI.AlgebraicGeometry.Comparison.Betti.Analytic.NaturalityInt
