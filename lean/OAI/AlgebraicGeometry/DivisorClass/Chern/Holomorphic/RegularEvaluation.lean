import OAI.AlgebraicGeometry.DivisorClass.Chern.HolomorphicSection.Modules
import OAI.AlgebraicGeometry.DivisorClass.Chern.AnalyticCover
import OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.HolomorphicSections
import OAI.AlgebraicGeometry.Betti.ProjectiveCohomology

/-! # Regular Evaluation -/

namespace OAI.AlgebraicGeometry.DivisorClass.Chern.Holomorphic.RegularEvaluation

noncomputable section

section

/-! Evaluation of original regular sections in the original holomorphic structure sheaf. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

variable (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety)

local instance : IsIntegral V.toOver.left := inferInstanceAs (IsIntegral V.carrier)
local instance : Smooth V.toOver.hom := inferInstanceAs (Smooth V.presentation.structureMap)

def regularSectionHolomorphicEvaluation (U : V.carrier.Opens) :
    Γ(V.carrier, U) →+*
      Exponential.HolomorphicFunction (E := V.analyticModel) (M := Line.Bundles.AlgebraicLineBundle.analyticOpen V.presentation U) where
  toFun s := ⟨Line.Bundles.AlgebraicLineBundle.sectionEvaluationOn V.presentation U s,
    HodgeConjecture.CMExtraction.HolomorphicSections.Kaehler.sectionEvaluationOn_holomorphic V.toOver U s⟩
  map_zero' := by
    apply ContMDiffMap.ext
    intro p
    exact congrArg (fun f : C(Comparison.Betti.Open.AffineIsoEvaluation.analyticOpen V.toOver U, ℂ) => f p)
      (map_zero (Comparison.Betti.Open.AffineIsoEvaluation.sectionEvaluationOn V.toOver U))
  map_one' := by
    apply ContMDiffMap.ext
    intro p
    exact congrArg (fun f : C(Comparison.Betti.Open.AffineIsoEvaluation.analyticOpen V.toOver U, ℂ) => f p)
      (map_one (Comparison.Betti.Open.AffineIsoEvaluation.sectionEvaluationOn V.toOver U))
  map_add' s t := by
    apply ContMDiffMap.ext
    intro p
    exact congrArg (fun f : C(Comparison.Betti.Open.AffineIsoEvaluation.analyticOpen V.toOver U, ℂ) => f p)
      (map_add (Comparison.Betti.Open.AffineIsoEvaluation.sectionEvaluationOn V.toOver U) s t)
  map_mul' s t := by
    apply ContMDiffMap.ext
    intro p
    exact Line.Bundles.AlgebraicLineBundle.sectionEvaluationOn_mul V.presentation U s t p

theorem regularSectionHolomorphicEvaluation_apply (U : V.carrier.Opens) (s : Γ(V.carrier, U))
    (p : Line.Bundles.AlgebraicLineBundle.analyticOpen V.presentation U) :
    regularSectionHolomorphicEvaluation V U s p = Line.Bundles.AlgebraicLineBundle.sectionEvaluationOn V.presentation U s p := rfl

theorem regularSectionHolomorphicEvaluation_restrict {U W : V.carrier.Opens} (h : W ≤ U)
    (s : Γ(V.carrier, U)) :
    regularSectionHolomorphicEvaluation V W (V.carrier.presheaf.map (homOfLE h).op s) =
      HolomorphicSection.Data.holomorphicOpenRestriction (show Line.Bundles.AlgebraicLineBundle.analyticOpen V.presentation W ≤
        Line.Bundles.AlgebraicLineBundle.analyticOpen V.presentation U from fun _ hx => h hx)
          (regularSectionHolomorphicEvaluation V U s) := by
  apply ContMDiffMap.ext
  intro p
  exact Line.Bundles.AlgebraicLineBundle.sectionEvaluationOn_restrict V.presentation h s p

end

/-! The actual morphism from algebraic structure sheaves to holomorphic functions. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace Opposite

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

variable (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety)

def holomorphicAnalytificationPointMap : TopCat.of V.analyticSpace ⟶ TopCat.of V.carrier :=
  TopCat.ofHom ⟨ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.underlying, ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.continuous_underlying⟩

instance holomorphicAnalytificationSite_continuous :
    (Opens.map (holomorphicAnalytificationPointMap V)).IsContinuous
      (Opens.grothendieckTopology V.carrier) (Opens.grothendieckTopology (TopCat.of V.analyticSpace)) := by
  apply Functor.isContinuous_of_coverPreserving
  · exact compatiblePreserving_opens_map (holomorphicAnalytificationPointMap V)
  · exact coverPreserving_opens_map (holomorphicAnalytificationPointMap V)

def holomorphicStructureDirectImage : TopCat.Sheaf RingCat.{0} (TopCat.of V.carrier) :=
  (TopCat.Sheaf.pushforward RingCat (holomorphicAnalytificationPointMap V)).obj
    (HolomorphicSection.Modules.holomorphicStructureRingSheaf V.analyticModel V.analyticSpace)

def algebraicToHolomorphicStructureSheaf : V.carrier.ringCatSheaf ⟶ holomorphicStructureDirectImage V where
  hom := {
    app := fun U => RingCat.ofHom (regularSectionHolomorphicEvaluation V U.unop)
    naturality := by
      intro U W i
      apply RingCat.hom_ext
      apply RingHom.ext
      intro s
      exact regularSectionHolomorphicEvaluation_restrict V (leOfHom i.unop) s }

theorem algebraicToHolomorphicStructureSheaf_apply (U : V.carrier.Opens) (s : Γ(V.carrier, U))
    (p : Line.Bundles.AlgebraicLineBundle.analyticOpen V.presentation U) :
    (show Exponential.HolomorphicFunction (E := V.analyticModel) (M := Line.Bundles.AlgebraicLineBundle.analyticOpen V.presentation U) from
      (algebraicToHolomorphicStructureSheaf V).hom.app (op U) s) p =
      Line.Bundles.AlgebraicLineBundle.sectionEvaluationOn V.presentation U s p := rfl

end

end OAI.AlgebraicGeometry.DivisorClass.Chern.Holomorphic.RegularEvaluation
