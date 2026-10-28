import OAI.AlgebraicGeometry.Comparison.Betti.Analytic.SheafPullback
import OAI.AlgebraicGeometry.Comparison.Betti.Smooth.SheafMap

/-! # Realization Naturality -/

namespace OAI.AlgebraicGeometry.Comparison.Betti.Analytic.RealizationNaturality

noncomputable section

/-! The algebraic realization commutes with actual analytic pullback on Zariski opens. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace Opposite
open scoped _root_.Manifold ContDiff

local instance nativePointSpaceCharted (Z : Over Foundations.Scheme.ProjectiveSpace.complexBase) [IsIntegral Z.left] [Smooth Z.hom] :
    ChartedSpace (RegularSmoothness.NativeModel Z) (Betti.Scheme.schemePointSpace Z) :=
  inferInstanceAs (ChartedSpace (RegularSmoothness.NativeModel Z) (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints Z))

local instance nativePointSpaceManifold (Z : Over Foundations.Scheme.ProjectiveSpace.complexBase) [IsIntegral Z.left] [Smooth Z.hom] :
    IsManifold 𝓘(ℝ, RegularSmoothness.NativeModel Z) ∞ (Betti.Scheme.schemePointSpace Z) :=
  inferInstanceAs (IsManifold 𝓘(ℝ, RegularSmoothness.NativeModel Z) ∞ (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints Z))

variable {X Y : Over Foundations.Scheme.ProjectiveSpace.complexBase} [IsIntegral X.left] [Smooth X.hom]
  [IsIntegral Y.left] [Smooth Y.hom] (f : X ⟶ Y)

def zariskiAnalyticDirectPullback : Betti.Smooth.SheafMap.zariskiSmoothSheafComplex Y ⟶
    ((Algebraic.Sheaves.directImage f).mapHomologicalComplex (ComplexShape.up ℕ)).obj (Betti.Smooth.SheafMap.zariskiSmoothSheafComplex X) :=
  ((Betti.Smooth.SheafMap.analytificationPushforward Y).mapHomologicalComplex (ComplexShape.up ℕ)).map
    (SheafPullback.Smooth.analyticDeRhamDirectImage (E := RegularSmoothness.NativeModel X) (F := RegularSmoothness.NativeModel Y)
      (M := Betti.Scheme.schemePointSpace X) (N := Betti.Scheme.schemePointSpace Y) (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPointsFunctor.map f)
      (ComplexPoints.Analytic.IntrinsicSmoothSchemeMaps.real_contMDiff_nativeScheme_map f ∞))

theorem presheafSmoothCochainMap_direct_naturality :
    Betti.Smooth.SheafMap.presheafSmoothCochainMap Y ≫
      ((sheafToPresheaf (Opens.grothendieckTopology Y.left) (ModuleCat.{0} ℂ)).mapHomologicalComplex
        (ComplexShape.up ℕ)).map (zariskiAnalyticDirectPullback f) =
    Sheaf.CochainPullback.presheafComplexPullback f ≫
      ((Sheaf.CochainPullback.directImagePresheaf f).mapHomologicalComplex (ComplexShape.up ℕ)).map
        (Betti.Smooth.SheafMap.presheafSmoothCochainMap X) := by
  apply HomologicalComplex.Hom.ext
  funext n
  apply NatTrans.ext
  funext U
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro a
  exact (Open.SmoothNaturality.openSmoothFormMap_naturality f U.unop n a).symm

theorem presheafToDirectImageAnalytic_naturality :
    Betti.Smooth.SheafMap.presheafSmoothCochainMap Y ≫
      ((sheafToPresheaf (Opens.grothendieckTopology Y.left) (ModuleCat.{0} ℂ)).mapHomologicalComplex
        (ComplexShape.up ℕ)).map (zariskiAnalyticDirectPullback f) =
    Sheaf.CochainPullback.presheafToDirectImageSheafComplex f ≫
      ((sheafToPresheaf (Opens.grothendieckTopology Y.left) (ModuleCat.{0} ℂ)).mapHomologicalComplex
        (ComplexShape.up ℕ)).map
        (((Algebraic.Sheaves.directImage f).mapHomologicalComplex (ComplexShape.up ℕ)).map (Betti.Smooth.SheafMap.algebraicToSmoothSheafMap X)) := by
  let D := (Sheaf.CochainPullback.directImagePresheaf f).mapHomologicalComplex (ComplexShape.up ℕ)
  have h := Betti.Smooth.SheafMap.algebraicToSmoothSheafMap_normalization X
  erw [Adjunction.homEquiv_unit] at h
  have hm := D.congr_map h
  erw [D.map_comp] at hm
  change _ = (Sheaf.CochainPullback.presheafComplexPullback f ≫
      D.map ((Sheaf.CochainPullback.sheafificationComplexAdjunction X).unit.app (Algebraic.Sheaves.deRhamPresheafComplex X))) ≫
        D.map (((sheafToPresheaf (Opens.grothendieckTopology X.left) (ModuleCat.{0} ℂ)).mapHomologicalComplex
          (ComplexShape.up ℕ)).map (Betti.Smooth.SheafMap.algebraicToSmoothSheafMap X))
  erw [Category.assoc (Sheaf.CochainPullback.presheafComplexPullback f), hm]
  exact presheafSmoothCochainMap_direct_naturality f

theorem algebraicToSmoothSheafMap_analytic_naturality :
    Betti.Smooth.SheafMap.algebraicToSmoothSheafMap Y ≫ zariskiAnalyticDirectPullback f =
      Sheaf.CochainPullback.deRhamSheafDirectImage f ≫
        ((Algebraic.Sheaves.directImage f).mapHomologicalComplex (ComplexShape.up ℕ)).map (Betti.Smooth.SheafMap.algebraicToSmoothSheafMap X) := by
  let D := (Algebraic.Sheaves.directImage f).mapHomologicalComplex (ComplexShape.up ℕ)
  let adj := Sheaf.CochainPullback.sheafificationComplexAdjunction Y
  apply (adj.homEquiv (Algebraic.Sheaves.deRhamPresheafComplex Y) (D.obj (Betti.Smooth.SheafMap.zariskiSmoothSheafComplex X))).injective
  have hd : adj.homEquiv (Algebraic.Sheaves.deRhamPresheafComplex Y) (D.obj (Algebraic.Sheaves.algebraicDeRhamSheafComplex X))
      (Sheaf.CochainPullback.deRhamSheafDirectImage f) = Sheaf.CochainPullback.presheafToDirectImageSheafComplex f :=
    (adj.homEquiv _ _).apply_symm_apply _
  erw [adj.homEquiv_naturality_right (Betti.Smooth.SheafMap.algebraicToSmoothSheafMap Y) (zariskiAnalyticDirectPullback f),
    Betti.Smooth.SheafMap.algebraicToSmoothSheafMap_normalization,
    adj.homEquiv_naturality_right (Sheaf.CochainPullback.deRhamSheafDirectImage f) (D.map (Betti.Smooth.SheafMap.algebraicToSmoothSheafMap X)), hd]
  exact presheafToDirectImageAnalytic_naturality f

end

end OAI.AlgebraicGeometry.Comparison.Betti.Analytic.RealizationNaturality
