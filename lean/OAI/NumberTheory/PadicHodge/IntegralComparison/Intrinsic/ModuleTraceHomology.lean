import OAI.NumberTheory.PadicHodge.GeometricComparison.ExactHomology
import OAI.NumberTheory.PadicHodge.IntegralComparison.Intrinsic.ModuleCechTrace
import OAI.NumberTheory.PadicHodge.IntegralComparison.ModuleCech.PushforwardNaturality

/-! # Module Trace Homology -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Intrinsic.ModuleTraceHomology

noncomputable section

/-! The original native transfer on cohomology is the module trace
under the canonical inverse-cover/pushforward identification. -/
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry _root_.TopologicalSpace
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
variable (R : Type u) [CommRing R]
  (X Y : Over (Spec (CommRingCat.of R))) (f : X ⟶ Y)
  [IsFinite f.left] [Etale f.left] [IsProper Y.hom] [Smooth Y.hom]
  {ι : Type u} (U : ι → Y.left.Opens) (q n : ℕ)
local notation "G" => OAI.NumberTheory.PadicHodge.IntegralComparison.ModuleCech.CohomologyNaturality.forgetCoefficients R
local notation "F" => Opens.map f.left.base
local notation "V" => OAI.NumberTheory.PadicHodge.IntegralComparison.IntrinsicDeRham.CechTransfer.Intrinsic.inverseCover R X Y f U
local notation "M" => OAI.NumberTheory.PadicHodge.GeometricComparison.Integral.FormsModules.IntegralFormsModules.sheaf R X q
local notation "N" => OAI.NumberTheory.PadicHodge.GeometricComparison.Integral.FormsModules.IntegralFormsModules.sheaf R Y q
local notation "T" => CategoryTheory.Functor.obj (Scheme.Modules.pushforward f.left) (M)
local instance opens_finiteLimits : PreservesFiniteLimits (Opens.map f.left.base) := by
  change PreservesFiniteLimits (OrderHom.ofClass f.left.base.frameHom).toFunctor
  infer_instance

def pushforwardIso :
    (G).obj ((ModuleCech.DimensionBound.complex R X M V).homology n) ≅
      (G).obj ((ModuleCech.DimensionBound.complex R Y T U).homology n) :=
  ModuleCech.CohomologyNaturality.forgetHomologyIso R X V M n ≪≫
    (HomologicalComplex.homologyMapIso (AlgebraicGeometry.Crystalline.Cohomology.Cech.BaseChange.CechBaseChange.complexIso (F) U (M).presheaf) n).symm ≪≫
      (ModuleCech.CohomologyNaturality.forgetHomologyIso R Y U T n).symm

theorem forget_comparison :
    (G).map (HomologicalComplex.homologyMap (ModuleCechTrace.trace R X Y f U q) n) ≫
      (ModuleCech.CohomologyNaturality.forgetHomologyIso R Y U N n).hom =
    (ModuleCech.CohomologyNaturality.forgetHomologyIso R X V M n).hom ≫
      HomologicalComplex.homologyMap (AlgebraicGeometry.Crystalline.Cohomology.Cech.BaseChange.CechBaseChange.complexIso (F) U (M).presheaf).inv n ≫
        HomologicalComplex.homologyMap ((cechComplexFunctor U).map
          ((SheafOfModules.toSheaf Y.left.ringCatSheaf).map
            (FiniteEtale.ModuleTrace.trace R X Y f q)).hom) n := by
  have h := GeometricComparison.ExactHomology.ExactHomologyComparison.naturality (G) (.up ℕ)
    (ModuleCech.DimensionBound.forgetIso R X M V)
    (ModuleCech.DimensionBound.forgetIso R Y N U)
    (ModuleCechTrace.trace R X Y f U q)
    ((AlgebraicGeometry.Crystalline.Cohomology.Cech.BaseChange.CechBaseChange.complexIso (F) U (M).presheaf).inv ≫
      (cechComplexFunctor U).map
        ((SheafOfModules.toSheaf Y.left.ringCatSheaf).map
          (FiniteEtale.ModuleTrace.trace R X Y f q)).hom)
    (ModuleCechTrace.comparison R X Y f U q) n
  simpa only [GeometricComparison.ExactHomology.ExactHomologyComparison.iso, Iso.trans_hom, Iso.symm_hom,
    Functor.mapIso_hom, HomologicalComplex.homologyFunctor_map, HomologicalComplex.homologyMap_comp,
    ModuleCech.CohomologyNaturality.forgetHomologyIso, HomologicalComplex.homologyMapIso_hom, Category.assoc] using h

theorem comparison :
    (G).map (HomologicalComplex.homologyMap (ModuleCechTrace.trace R X Y f U q) n) =
    (pushforwardIso R X Y f U q n).hom ≫
      (G).map (HomologicalComplex.homologyMap (ModuleCech.CohomologyNaturality.map R Y U
        (FiniteEtale.ModuleTrace.trace R X Y f q)) n) := by
  have h := ModuleCech.CohomologyNaturality.forget_homology_natural R Y U
    (FiniteEtale.ModuleTrace.trace R X Y f q) n
  apply (cancel_mono (ModuleCech.CohomologyNaturality.forgetHomologyIso R Y U N n).hom).1
  rw [Category.assoc, h]
  change _ = (((ModuleCech.CohomologyNaturality.forgetHomologyIso R X V M n).hom ≫
    HomologicalComplex.homologyMap (AlgebraicGeometry.Crystalline.Cohomology.Cech.BaseChange.CechBaseChange.complexIso (F) U (M).presheaf).inv n) ≫
      (ModuleCech.CohomologyNaturality.forgetHomologyIso R Y U T n).inv) ≫ _
  simp only [Category.assoc, Iso.inv_hom_id_assoc]
  exact forget_comparison R X Y f U q n

variable (g : ℕ) [SmoothOfRelativeDimension g X.hom] [IsProper X.hom]
  [SmoothOfRelativeDimension g Y.hom]

omit [SmoothOfRelativeDimension g X.hom] [IsProper X.hom] in
theorem top_trace (x : IntrinsicDeRham.TopEdge.Intrinsic.source R X V g) :
    HomologicalComplex.homologyMap (ModuleCechTrace.trace R X Y f U g) g x =
      IntrinsicDeRham.TopEdgeTransfer.Intrinsic.trace R X Y f U g x := by
  rw [ModuleCechTrace.trace, HomologicalComplex.homologyMap_comp,
    HomologicalComplex.homologyMap_comp]
  rfl

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Intrinsic.ModuleTraceHomology
