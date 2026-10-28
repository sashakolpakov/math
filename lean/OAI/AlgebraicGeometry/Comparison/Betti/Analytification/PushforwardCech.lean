import OAI.AlgebraicGeometry.Comparison.Betti.Closed.AnalytificationPushforwardAdditiveSquare
import OAI.AlgebraicGeometry.Comparison.Betti.AdditiveCechImage
import OAI.AlgebraicGeometry.Comparison.Betti.Module.AnalytificationCechMap
import Mathlib.Algebra.Homology.QuasiIso

/-! # Pushforward Cech -/

namespace OAI.AlgebraicGeometry.Comparison.Betti.Analytification.PushforwardCech

noncomputable section

section

/-! The ambient Čech comparison followed by the original coefficient comparison equals the Čech map of the original source unit. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace

open OAI.AlgebraicGeometry.Comparison.Betti.AdditiveCechImage

theorem moduleAnalytificationPushforwardCech_left
    {X Y : Over Foundations.Scheme.ProjectiveSpace.complexBase} [IsIntegral X.left] [Smooth X.hom]
    [IsIntegral Y.left] [Smooth Y.hom] (f : X ⟶ Y) (M : X.left.Modules)
    {ι : Type} (U : ι → Y.left.Opens) :
    Module.AnalytificationCechMap.moduleAnalytificationCechMap Y ((Scheme.Modules.pushforward f.left).obj M) U ≫
      (cechComplexFunctor (fun i => Open.AffineIsoEvaluation.analyticOpen Y (U i))).map
        (Closed.AnalytificationPushforwardAdditiveSquare.moduleAnalytificationPushforwardAdditiveMap f M) =
    (cechComplexFunctor U).map
      (Functor.whiskerLeft (Opens.map f.left.base).op (Module.AnalytificationAdditiveUnit.moduleAnalytificationAdditiveUnit X M)) ≫
      (AdditiveCechImage.additiveCechDirectImageIso (Base.analytificationMap Y) U
        ((Opens.map (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPointsFunctor.map f)).op ⋙
          ((Holomorphic.StructureMorphism.algebraicModuleHolomorphicAnalytification X).obj M).val.presheaf)).hom := by
  let Q := ((Holomorphic.StructureMorphism.algebraicModuleHolomorphicAnalytification X).obj M).val.presheaf
  let P := ((Holomorphic.StructureMorphism.algebraicModuleHolomorphicAnalytification Y).obj
    ((Scheme.Modules.pushforward f.left).obj M)).val.presheaf
  let C := cechComplexFunctor (A := AddCommGrpCat) U
  let u : ((Scheme.Modules.pushforward f.left).obj M).val.presheaf ⟶
      (Opens.map (Base.analytificationMap Y)).op ⋙ P :=
    Module.AnalytificationAdditiveUnit.moduleAnalytificationAdditiveUnit Y ((Scheme.Modules.pushforward f.left).obj M)
  let b : P ⟶ (Opens.map (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPointsFunctor.map f)).op ⋙ Q :=
    Closed.AnalytificationPushforwardAdditiveSquare.moduleAnalytificationPushforwardAdditiveMap f M
  let e := (AdditiveCechImage.additiveCechDirectImageIso (Base.analytificationMap Y) U
    ((Opens.map (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPointsFunctor.map f)).op ⋙ Q)).hom
  have hunit : u ≫ Functor.whiskerLeft (Opens.map (Base.analytificationMap Y)).op b =
      Functor.whiskerLeft (Opens.map f.left.base).op (Module.AnalytificationAdditiveUnit.moduleAnalytificationAdditiveUnit X M) :=
    Closed.AnalytificationPushforwardAdditiveSquare.moduleAnalytificationPushforwardAdditiveSquare f M
  have hpost := AdditiveCechImage.additiveCechPullback_postcompose (Base.analytificationMap Y) U u b
  erw [hunit] at hpost
  dsimp only [Module.AnalytificationCechMap.moduleAnalytificationCechMap]
  dsimp only [u, b, P, Q] at hpost
  simp only [Betti.Smooth.SheafMap.analytificationMap_preimage] at hpost
  exact hpost

end

section

/-! The two actual inverse-image routes give the same Čech pullback of the original source unit. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace

open OAI.AlgebraicGeometry.Comparison.Betti.AdditiveCechImage

theorem moduleAnalytificationPushforwardCech_right
    {X Y : Over Foundations.Scheme.ProjectiveSpace.complexBase} [IsIntegral X.left] [Smooth X.hom]
    [IsIntegral Y.left] [Smooth Y.hom] (f : X ⟶ Y) (M : X.left.Modules)
    {ι : Type} (U : ι → Y.left.Opens) :
    (cechComplexFunctor U).map
      (Functor.whiskerLeft (Opens.map f.left.base).op (Module.AnalytificationAdditiveUnit.moduleAnalytificationAdditiveUnit X M)) ≫
      (AdditiveCechImage.additiveCechDirectImageIso (Base.analytificationMap Y) U
        ((Opens.map (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPointsFunctor.map f)).op ⋙
          ((Holomorphic.StructureMorphism.algebraicModuleHolomorphicAnalytification X).obj M).val.presheaf)).hom ≫
      (AdditiveCechImage.additiveCechDirectImageIso (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPointsFunctor.map f)
        (fun i => Open.AffineIsoEvaluation.analyticOpen Y (U i))
        ((Holomorphic.StructureMorphism.algebraicModuleHolomorphicAnalytification X).obj M).val.presheaf).hom =
    (AdditiveCechImage.additiveCechDirectImageIso f.left.base U M.val.presheaf).hom ≫
      Module.AnalytificationCechMap.moduleAnalytificationCechMap X M (fun i => f.left ⁻¹ᵁ U i) := by
  let Q := ((Holomorphic.StructureMorphism.algebraicModuleHolomorphicAnalytification X).obj M).val.presheaf
  let z := Functor.whiskerLeft (Opens.map f.left.base).op (Module.AnalytificationAdditiveUnit.moduleAnalytificationAdditiveUnit X M)
  have hcomp := AdditiveCechImage.additiveCechDirectImageIso_comp (Base.analytificationMap Y)
    (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPointsFunctor.map f) U Q
  change (AdditiveCechImage.additiveCechDirectImageIso (Base.analytificationMap X ≫ f.left.base) U Q).hom = _ at hcomp
  simp only [Betti.Smooth.SheafMap.analytificationMap_preimage] at hcomp
  have hright := AdditiveCechImage.additiveCechPullback_directImage f.left.base (Base.analytificationMap X) U
    (Module.AnalytificationAdditiveUnit.moduleAnalytificationAdditiveUnit X M)
  simp only [Betti.Smooth.SheafMap.analytificationMap_preimage] at hright
  have h := (congrArg ((cechComplexFunctor U).map z ≫ ·) hcomp.symm).trans hright
  exact h

end

section

/-! The original module Čech comparison commutes with the actual algebraic and holomorphic direct-image identifications. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace

open OAI.AlgebraicGeometry.Comparison.Betti.AdditiveCechImage

variable {X Y : Over Foundations.Scheme.ProjectiveSpace.complexBase} [IsIntegral X.left] [Smooth X.hom]
  [IsIntegral Y.left] [Smooth Y.hom] (f : X ⟶ Y)

theorem moduleAnalytificationPushforwardCech_square (M : X.left.Modules)
    {ι : Type} (U : ι → Y.left.Opens) :
    Module.AnalytificationCechMap.moduleAnalytificationCechMap Y ((Scheme.Modules.pushforward f.left).obj M) U ≫
      (cechComplexFunctor (fun i => Open.AffineIsoEvaluation.analyticOpen Y (U i))).map
        (Closed.AnalytificationPushforwardAdditiveSquare.moduleAnalytificationPushforwardAdditiveMap f M) ≫
      (AdditiveCechImage.additiveCechDirectImageIso (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPointsFunctor.map f)
        (fun i => Open.AffineIsoEvaluation.analyticOpen Y (U i))
        ((Holomorphic.StructureMorphism.algebraicModuleHolomorphicAnalytification X).obj M).val.presheaf).hom =
    (AdditiveCechImage.additiveCechDirectImageIso f.left.base U M.val.presheaf).hom ≫
      Module.AnalytificationCechMap.moduleAnalytificationCechMap X M (fun i => f.left ⁻¹ᵁ U i) := by
  let eA := (AdditiveCechImage.additiveCechDirectImageIso (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPointsFunctor.map f)
    (fun i => Open.AffineIsoEvaluation.analyticOpen Y (U i))
    ((Holomorphic.StructureMorphism.algebraicModuleHolomorphicAnalytification X).obj M).val.presheaf).hom
  exact (Category.assoc _ _ _).symm.trans
    ((congrArg (· ≫ eA) (moduleAnalytificationPushforwardCech_left f M U)).trans
      ((Category.assoc _ _ _).trans (moduleAnalytificationPushforwardCech_right f M U)))

end

/-! The original Čech comparison descends through a smooth closed immersion along the inverse-image cover. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace

open OAI.AlgebraicGeometry.Comparison.Betti.AdditiveCechImage

variable {X Y : Over Foundations.Scheme.ProjectiveSpace.complexBase} [IsIntegral X.left] [Smooth X.hom]
  [IsIntegral Y.left] [Smooth Y.hom] (f : X ⟶ Y) [IsClosedImmersion f.left]

theorem moduleAnalytificationCechMap_quasiIso_closed (M : X.left.Modules)
    {ι : Type} (U : ι → Y.left.Opens)
    (hM : QuasiIso (Module.AnalytificationCechMap.moduleAnalytificationCechMap Y ((Scheme.Modules.pushforward f.left).obj M) U)) :
    QuasiIso (Module.AnalytificationCechMap.moduleAnalytificationCechMap X M (fun i => f.left ⁻¹ᵁ U i)) := by
  let F := SheafOfModules.toSheaf (Holomorphic.StructureMorphism.analyticHolomorphicStructureSheaf Y) ⋙
    TopCat.Sheaf.forget AddCommGrpCat (TopCat.of (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints Y)) ⋙
      cechComplexFunctor (fun i => Open.AffineIsoEvaluation.analyticOpen Y (U i))
  let e := F.mapIso ((ClosedImmersion.Module.moduleAnalytificationClosedPushforwardIso f).app M)
  let eA := AdditiveCechImage.additiveCechDirectImageIso (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPointsFunctor.map f)
    (fun i => Open.AffineIsoEvaluation.analyticOpen Y (U i))
    ((Holomorphic.StructureMorphism.algebraicModuleHolomorphicAnalytification X).obj M).val.presheaf
  let eZ := AdditiveCechImage.additiveCechDirectImageIso f.left.base U M.val.presheaf
  let a := Module.AnalytificationCechMap.moduleAnalytificationCechMap Y ((Scheme.Modules.pushforward f.left).obj M) U
  let b := Module.AnalytificationCechMap.moduleAnalytificationCechMap X M (fun i => f.left ⁻¹ᵁ U i)
  have hsq : a ≫ e.hom ≫ eA.hom = eZ.hom ≫ b :=
    moduleAnalytificationPushforwardCech_square f M U
  have he : QuasiIso e.hom := quasiIso_of_isIso e.hom
  have heA : QuasiIso eA.hom := quasiIso_of_isIso eA.hom
  have hleft : QuasiIso (a ≫ e.hom ≫ eA.hom) :=
    quasiIso_comp a (e.hom ≫ eA.hom) (hφ := hM)
      (hφ' := quasiIso_comp e.hom eA.hom (hφ := he) (hφ' := heA))
  have hright : QuasiIso (eZ.hom ≫ b) := hsq ▸ hleft
  exact quasiIso_of_comp_left eZ.hom b
    (hφ := quasiIso_of_isIso eZ.hom) (hφφ' := hright)

end

end OAI.AlgebraicGeometry.Comparison.Betti.Analytification.PushforwardCech
