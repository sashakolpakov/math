import OAI.ArithmeticGeometry.OrdinaryLocus.Openness.SectionEvaluation
import OAI.ArithmeticGeometry.OrdinaryLocus.Openness.TrivialBundleSectionBijectivity
import OAI.AlgebraicGeometry.Quotients.FiniteDescent.PullbackSectionCongr

/-! # Section Evaluation Local -/

namespace OAI.ArithmeticGeometry.OrdinaryLocus.Openness.SectionEvaluationLocal.Construction

noncomputable section

/-! A relative local frame makes evaluation along the section bijective on that base open. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

private theorem bijective_of_bijective_square
    {A B C D : Type*} (f : A → B) (g : C → D) (a : A → C) (b : B → D)
    (ha : Function.Bijective a) (hb : Function.Bijective b) (hg : Function.Bijective g)
    (h : ∀ x, b (f x) = g (a x)) : Function.Bijective f := by
  constructor
  · intro x y hxy
    apply ha.injective
    apply hg.injective
    exact (h x).symm.trans ((congrArg b hxy).trans (h y))
  · intro y
    obtain ⟨z, hz⟩ := hg.surjective (b y)
    obtain ⟨x, hx⟩ := ha.surjective z
    exact ⟨x, hb.injective ((h x).trans ((congrArg g hx).trans hz))⟩

theorem sectionEvaluation_app_bijective_of_frame
    {X S : Scheme.{u}} (π : X ⟶ S) (s : S ⟶ X) (hs : s ≫ π = 𝟙 S)
    (hf : ∀ U : S.Opens, IsIso (π.app U)) (L : X.Modules) (U : S.Opens)
    (e : (Scheme.Modules.pullback (π ⁻¹ᵁ U).ι).obj L ≅ LineBundle.Construction.structureSheafModule (π ⁻¹ᵁ U).toScheme) :
    Function.Bijective ((SectionEvaluation.Construction.sectionEvaluation π s hs L).app U) := by
  let V := π ⁻¹ᵁ U
  let sU := SectionRestriction.Construction.sectionRestrict π s hs U
  let L' := (Scheme.Modules.pullback V.ι).obj L
  let N := (Scheme.Modules.pullback s).obj L
  let E := AlgebraicGeometry.Quotients.FiniteDescent.PullbackSectionCongr.Construction.PullbackSectionSquare.iso s V.ι U.ι sU (SectionRestriction.Construction.sectionRestrict_ι π s hs U).symm L
  have : IsIso sU.appTop := SectionRestriction.Construction.isIso_sectionRestrict_appTop π s hs hf U
  have hE := ConcreteCategory.bijective_of_isIso (E.hom.app ⊤)
  have hG := TrivialBundleSectionBijectivity.Construction.trivialBundle_sections_bijective_of_appTop sU L' e
  apply bijective_of_bijective_square ((SectionEvaluation.Construction.sectionEvaluation π s hs L).app U)
    (PullbackModuleSections.Construction.modulePullbackGlobalSection sU L') (OpenPullbackSections.Construction.moduleOpenPullbackSectionsMap L V)
    (fun z ↦ E.hom.app ⊤ (OpenPullbackSections.Construction.moduleOpenPullbackSectionsMap N U z))
    (OpenPullbackSections.Construction.moduleOpenPullbackSectionsMap_bijective L V)
    (hE.comp (OpenPullbackSections.Construction.moduleOpenPullbackSectionsMap_bijective N U)) hG
  intro m
  have he := AlgebraicGeometry.Quotients.FiniteDescent.PullbackSectionCongr.Construction.PullbackSectionSquare.apply s V.ι U.ι sU
    (SectionRestriction.Construction.sectionRestrict_ι π s hs U).symm L V U ⊤ ⊤
    (SectionRestriction.Construction.section_preimage_le π s hs U) V.ι_preimage_self.ge U.ι_preimage_self.ge le_rfl m
  have hEval := SectionEvaluation.Construction.sectionEvaluation_apply π s hs L U m
  have ht := congrArg (fun z ↦ E.hom.app ⊤ (OpenPullbackSections.Construction.moduleOpenPullbackSectionsMap N U z)) hEval
  exact ht.trans (he.trans (AlgebraicGeometry.Quotients.FiniteDescent.RestrictedPullback.Construction.RestrictedPullbackSections.full sU L' ⊤ _))

end

end OAI.ArithmeticGeometry.OrdinaryLocus.Openness.SectionEvaluationLocal.Construction
