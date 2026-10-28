import OAI.ArithmeticGeometry.OrdinaryLocus.Openness.SectionRestriction

/-! # Section Evaluation -/

namespace OAI.ArithmeticGeometry.OrdinaryLocus.Openness.SectionEvaluation.Construction

noncomputable section

/-! Evaluate sections of a module along a scheme-theoretic section of its base map. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

variable {X S : Scheme.{u}} (π : X ⟶ S) (s : S ⟶ X) (hs : s ≫ π = 𝟙 S) (L : X.Modules)

def sectionEvaluation : (Scheme.Modules.pushforward π).obj L ⟶ (Scheme.Modules.pullback s).obj L :=
  (Scheme.Modules.pushforward π).map ((Scheme.Modules.pullbackPushforwardAdjunction s).unit.app L) ≫
    (Scheme.Modules.pushforwardComp s π).hom.app ((Scheme.Modules.pullback s).obj L) ≫
    (Scheme.Modules.pushforwardCongr hs).hom.app ((Scheme.Modules.pullback s).obj L) ≫
    (Scheme.Modules.pushforwardId S).hom.app ((Scheme.Modules.pullback s).obj L)

theorem sectionEvaluation_apply (U : S.Opens) (m : Γ(L, π ⁻¹ᵁ U)) :
    (sectionEvaluation π s hs L).app U m =
      PullbackSectionCompatibility.Construction.modulePullbackSectionLE s L (π ⁻¹ᵁ U) U (SectionRestriction.Construction.section_preimage_le π s hs U) m := by
  change ((Scheme.Modules.pullback s).obj L).presheaf.map _
    (OpenPullbackSections.Construction.modulePullbackSection s L (π ⁻¹ᵁ U) m) = _
  rfl

end

end OAI.ArithmeticGeometry.OrdinaryLocus.Openness.SectionEvaluation.Construction
