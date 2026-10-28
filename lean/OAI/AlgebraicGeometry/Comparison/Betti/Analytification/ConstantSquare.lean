import OAI.AlgebraicGeometry.Comparison.Betti.Analytification.MateNaturality
import OAI.AlgebraicGeometry.Comparison.Betti.AdjunctionComposition

/-! # Constant Square -/

namespace OAI.AlgebraicGeometry.Comparison.Betti.Analytification.ConstantSquare

noncomputable section

/-! The canonical constant-coefficient identifications commute around analytification. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry _root_.TopologicalSpace Opposite

def zariskiConstantAdjunction (X : Over Foundations.Scheme.ProjectiveSpace.complexBase) :
    constantSheaf (Opens.grothendieckTopology X.left) (ModuleCat.{0} ℂ) ⊣
      (sheafSections (Opens.grothendieckTopology X.left) (ModuleCat.{0} ℂ)).obj (op ⊤) :=
  constantSheafAdj (Opens.grothendieckTopology X.left) (ModuleCat.{0} ℂ) isTerminalTop

def analyticConstantAdjunction (X : Over Foundations.Scheme.ProjectiveSpace.complexBase) :
    constantSheaf (Opens.grothendieckTopology (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X)) (ModuleCat.{0} ℂ) ⊣
      (sheafSections (Opens.grothendieckTopology (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X)) (ModuleCat.{0} ℂ)).obj (op ⊤) :=
  constantSheafAdj (Opens.grothendieckTopology (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X)) (ModuleCat.{0} ℂ) isTerminalTop

variable {X Y : Over Foundations.Scheme.ProjectiveSpace.complexBase} (f : X ⟶ Y)

def zariskiRouteConstantIso :
    constantSheaf (Opens.grothendieckTopology Y.left) (ModuleCat.{0} ℂ) ⋙
        Algebraic.Sheaves.inverseImage f ⋙ Analytic.De.analytificationInverseImage X ≅
      constantSheaf (Opens.grothendieckTopology (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X)) (ModuleCat.{0} ℂ) :=
  ((zariskiConstantAdjunction Y).comp
    ((Algebraic.Sheaves.imageAdjunction f).comp (Analytic.De.analytificationAdjunction X))).leftAdjointUniq (analyticConstantAdjunction X)

def analyticRouteConstantIso :
    constantSheaf (Opens.grothendieckTopology Y.left) (ModuleCat.{0} ℂ) ⋙
        Analytic.De.analytificationInverseImage Y ⋙ Analytic.ResolutionNaturality.schemeAnalyticInverseImage f ≅
      constantSheaf (Opens.grothendieckTopology (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X)) (ModuleCat.{0} ℂ) :=
  ((zariskiConstantAdjunction Y).comp
    ((Analytic.De.analytificationAdjunction Y).comp (MateNaturality.schemeAnalyticImageAdjunction f))).leftAdjointUniq
      (analyticConstantAdjunction X)

theorem zariskiRouteConstantIso_normalization :
    (zariskiRouteConstantIso f).hom.app (ModuleCat.of ℂ ℂ) =
      (Analytic.De.analytificationInverseImage X).map (Algebraic.Sheaves.inverseImageConstantIso f).hom ≫
        (Analytic.De.analytificationInverseImageConstantIso X).hom := by
  let a := zariskiConstantAdjunction Y
  let b := Algebraic.Sheaves.imageAdjunction f
  let c := Analytic.De.analytificationAdjunction X
  let d := zariskiConstantAdjunction X
  let e := analyticConstantAdjunction X
  let m := ModuleCat.of ℂ ℂ
  have hw := AdjunctionComposition.leftAdjointUniq_whiskerRight (a.comp b) d c m
  have h := (Adjunction.leftAdjointUniq_trans_app ((a.comp b).comp c) (d.comp c) e m).symm.trans
    (congrArg (fun t => t ≫ ((d.comp c).leftAdjointUniq e).hom.app m) hw)
  erw [AdjunctionComposition.comp_assoc a b c] at h
  exact h

theorem analyticRouteConstantIso_normalization :
    (analyticRouteConstantIso f).hom.app (ModuleCat.of ℂ ℂ) =
      (Analytic.ResolutionNaturality.schemeAnalyticInverseImage f).map (Analytic.De.analytificationInverseImageConstantIso Y).hom ≫
        (TopologicalSheafPullback.constantPullbackIso (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPointsFunctor.map f)).hom := by
  let a := zariskiConstantAdjunction Y
  let b := Analytic.De.analytificationAdjunction Y
  let c := MateNaturality.schemeAnalyticImageAdjunction f
  let d := analyticConstantAdjunction Y
  let e := analyticConstantAdjunction X
  let m := ModuleCat.of ℂ ℂ
  have hw := AdjunctionComposition.leftAdjointUniq_whiskerRight (a.comp b) d c m
  have h := (Adjunction.leftAdjointUniq_trans_app ((a.comp b).comp c) (d.comp c) e m).symm.trans
    (congrArg (fun t => t ≫ ((d.comp c).leftAdjointUniq e).hom.app m) hw)
  erw [AdjunctionComposition.comp_assoc a b c] at h
  exact h

theorem analytificationSheafMateIso_constant_route :
    (MateNaturality.analytificationSheafMateIso f).hom.app (Algebraic.Sheaves.constantComplexSheaf Y) ≫
        (analyticRouteConstantIso f).hom.app (ModuleCat.of ℂ ℂ) =
      (zariskiRouteConstantIso f).hom.app (ModuleCat.of ℂ ℂ) := by
  let a := zariskiConstantAdjunction Y
  let b := (Algebraic.Sheaves.imageAdjunction f).comp (Analytic.De.analytificationAdjunction X)
  let c := (Analytic.De.analytificationAdjunction Y).comp (MateNaturality.schemeAnalyticImageAdjunction f)
  let d := analyticConstantAdjunction X
  let m := ModuleCat.of ℂ ℂ
  have hw := AdjunctionComposition.leftAdjointUniq_whiskerLeft a b c m
  have h := Adjunction.leftAdjointUniq_trans_app (a.comp b) (a.comp c) d m
  erw [hw] at h
  exact h

theorem analytificationSheafMateIso_constant :
    (Analytic.De.analytificationInverseImage X).map (Algebraic.Sheaves.inverseImageConstantIso f).hom ≫
        (Analytic.De.analytificationInverseImageConstantIso X).hom =
      (MateNaturality.analytificationSheafMateIso f).hom.app (Algebraic.Sheaves.constantComplexSheaf Y) ≫
        (Analytic.ResolutionNaturality.schemeAnalyticInverseImage f).map (Analytic.De.analytificationInverseImageConstantIso Y).hom ≫
          (TopologicalSheafPullback.constantPullbackIso (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPointsFunctor.map f)).hom :=
  (zariskiRouteConstantIso_normalization f).symm.trans
    ((analytificationSheafMateIso_constant_route f).symm.trans
      (congrArg (fun t => (MateNaturality.analytificationSheafMateIso f).hom.app (Algebraic.Sheaves.constantComplexSheaf Y) ≫ t)
        (analyticRouteConstantIso_normalization f)))

end

end OAI.AlgebraicGeometry.Comparison.Betti.Analytification.ConstantSquare
