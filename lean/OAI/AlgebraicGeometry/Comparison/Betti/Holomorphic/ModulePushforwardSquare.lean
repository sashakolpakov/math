import OAI.AlgebraicGeometry.Comparison.Betti.Holomorphic.RingedMap
import OAI.AlgebraicGeometry.Comparison.Betti.Holomorphic.StructureMorphism
import OAI.AlgebraicGeometry.Comparison.Betti.Open.EvaluationNaturality

/-! # Module Pushforward Square -/

namespace OAI.AlgebraicGeometry.Comparison.Betti.Holomorphic.ModulePushforwardSquare

noncomputable section

section

/-! Native holomorphic module pushforward along the actual map of smooth complex schemes. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace Opposite
open scoped _root_.Manifold ContDiff

variable {X Y : Over Foundations.Scheme.ProjectiveSpace.complexBase} [IsIntegral X.left] [Smooth X.hom]
  [IsIntegral Y.left] [Smooth Y.hom] (f : X ⟶ Y)

instance holomorphicSchemeMapSite_continuous :
    (Opens.map (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPointsFunctor.map f)).IsContinuous
      (Opens.grothendieckTopology (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints Y))
      (Opens.grothendieckTopology (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X)) := by
  apply Functor.isContinuous_of_coverPreserving
  · exact compatiblePreserving_opens_map (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPointsFunctor.map f)
  · exact coverPreserving_opens_map (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPointsFunctor.map f)

def analyticHolomorphicStructurePullback :
    StructureMorphism.analyticHolomorphicStructureSheaf Y ⟶
      (TopCat.Sheaf.pushforward RingCat (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPointsFunctor.map f)).obj
        (StructureMorphism.analyticHolomorphicStructureSheaf X) :=
  RingedMap.manifoldHolomorphicStructureMap (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map f)
    (ComplexPoints.Analytic.IntrinsicSmoothSchemeMaps.contMDiff_nativeScheme_map f ∞)

def analyticHolomorphicModulePushforward :
    SheafOfModules.{0} (StructureMorphism.analyticHolomorphicStructureSheaf X) ⥤
      SheafOfModules.{0} (StructureMorphism.analyticHolomorphicStructureSheaf Y) :=
  SheafOfModules.pushforward (F := Opens.map (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPointsFunctor.map f))
    (analyticHolomorphicStructurePullback f)

abbrev analyticSchemePreimageOpen (U : Opens (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints Y)) :
    Opens (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X) := (Opens.map (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPointsFunctor.map f)).obj U

theorem analyticHolomorphicStructurePullback_apply
    (U : Opens (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints Y))
    (a : C^∞⟮𝓘(ℂ, RegularSmoothness.NativeModel Y), U; 𝓘(ℂ), ℂ⟯)
    (p : analyticSchemePreimageOpen f U) :
    (show C^∞⟮𝓘(ℂ, RegularSmoothness.NativeModel X),
      analyticSchemePreimageOpen f U; 𝓘(ℂ), ℂ⟯ from
      (analyticHolomorphicStructurePullback f).hom.app (op U) a) p =
        a ⟨ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map f p.val, p.property⟩ := rfl

end

section

/-! The original regular-to-holomorphic evaluation commutes with the native ringed scheme map. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace Opposite

variable {X Y : Over Foundations.Scheme.ProjectiveSpace.complexBase} [IsIntegral X.left] [Smooth X.hom]
  [IsIntegral Y.left] [Smooth Y.hom] (f : X ⟶ Y)

omit [IsIntegral X.left] [Smooth X.hom] [IsIntegral Y.left] [Smooth Y.hom] in
theorem analyticSchemePreimageOpen_analyticOpen (U : Y.left.Opens) :
    analyticSchemePreimageOpen f (Open.AffineIsoEvaluation.analyticOpen Y U) = Open.AffineIsoEvaluation.analyticOpen X (f.left ⁻¹ᵁ U) := by
  apply Opens.ext
  ext p
  rfl

theorem holomorphicRingedSquare_normalization :
    f.left.toRingCatSheafHom.hom ≫
      Functor.whiskerLeft (Opens.map f.left.base).op (StructureMorphism.algebraicToHolomorphicStructureSheaf X).hom =
    (StructureMorphism.algebraicToHolomorphicStructureSheaf Y).hom ≫
      Functor.whiskerLeft (Opens.map (Analytification.Base.analytificationMap Y)).op
        (analyticHolomorphicStructurePullback f).hom := by
  apply NatTrans.ext
  funext U
  apply RingCat.hom_ext
  apply RingHom.ext
  intro s
  apply ContMDiffMap.ext
  intro p
  exact Open.EvaluationNaturality.sectionEvaluationOn_pullback f U.unop s p

end

/-! The actual holomorphic and algebraic module direct images commute through regular evaluation. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace

variable {X Y : Over Foundations.Scheme.ProjectiveSpace.complexBase} [IsIntegral X.left] [Smooth X.hom]
  [IsIntegral Y.left] [Smooth Y.hom] (f : X ⟶ Y)

def holomorphicModulePushforwardSquareIso :
    StructureMorphism.holomorphicModuleDirectImage X ⋙ Scheme.Modules.pushforward f.left ≅
      analyticHolomorphicModulePushforward f ⋙ StructureMorphism.holomorphicModuleDirectImage Y := by
  let hfirst : (Opens.map f.left.base ⋙ Opens.map (Analytification.Base.analytificationMap X)).IsContinuous
      (Opens.grothendieckTopology Y.left)
      (Opens.grothendieckTopology (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X)) :=
    Functor.isContinuous_comp _ _ _ (Opens.grothendieckTopology X.left) _
  let : (Opens.map (Analytification.Base.analytificationMap Y) ⋙ Opens.map (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPointsFunctor.map f)).IsContinuous
      (Opens.grothendieckTopology Y.left)
      (Opens.grothendieckTopology (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X)) :=
    hfirst
  refine SheafOfModules.pushforwardComp f.left.toRingCatSheafHom
      (StructureMorphism.algebraicToHolomorphicStructureSheaf X) ≪≫ ?_ ≪≫
    (SheafOfModules.pushforwardComp (StructureMorphism.algebraicToHolomorphicStructureSheaf Y)
      (analyticHolomorphicStructurePullback f)).symm
  apply SheafOfModules.pushforwardCongr
  apply Sheaf.hom_ext
  exact holomorphicRingedSquare_normalization f

end

end OAI.AlgebraicGeometry.Comparison.Betti.Holomorphic.ModulePushforwardSquare
