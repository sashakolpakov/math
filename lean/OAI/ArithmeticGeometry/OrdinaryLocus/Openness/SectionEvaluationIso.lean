import OAI.ArithmeticGeometry.OrdinaryLocus.Openness.SectionEvaluationLocal
import OAI.ArithmeticGeometry.OrdinaryLocus.Openness.TensorRestriction
import Mathlib.Topology.Sheaves.SheafCondition.Sites

/-! # Section Evaluation Iso -/

namespace OAI.ArithmeticGeometry.OrdinaryLocus.Openness.SectionEvaluationIso.Construction

noncomputable section

/-! Relative local frames identify the pushforward of a line bundle with its restriction to a section. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace

universe u

theorem sectionEvaluation_isIso_of_local_frames
    {X S : Scheme.{u}} (π : X ⟶ S) (s : S ⟶ X) (hs : s ≫ π = 𝟙 S)
    (hf : ∀ U : S.Opens, IsIso (π.app U)) (L : X.Modules)
    (hloc : ∀ x : S, ∃ U : S.Opens, x ∈ U ∧
      Nonempty ((Scheme.Modules.pullback (π ⁻¹ᵁ U).ι).obj L ≅ LineBundle.Construction.structureSheafModule (π ⁻¹ᵁ U).toScheme)) :
    IsIso (SectionEvaluation.Construction.sectionEvaluation π s hs L) := by
  let B : Set S.Opens := {U | Nonempty ((Scheme.Modules.pullback (π ⁻¹ᵁ U).ι).obj L ≅
    LineBundle.Construction.structureSheafModule (π ⁻¹ᵁ U).toScheme)}
  have hB : Opens.IsBasis B := by
    rw [Opens.isBasis_iff_nbhd]
    intro W x hx
    obtain ⟨U, hxU, ⟨e⟩⟩ := hloc x
    exact ⟨U ⊓ W, ⟨TensorRestriction.Construction.restrictLineBundleTrivialization (π.preimage_mono inf_le_left) e⟩,
      ⟨hxU, hx⟩, inf_le_right⟩
  let q := SectionEvaluation.Construction.sectionEvaluation π s hs L
  have : IsIso ((SheafOfModules.toSheaf S.ringCatSheaf).map q) := by
    apply TopCat.Sheaf.isIso_iff_isIso_basis (B := fun U : B ↦ U.1)
      (by simpa only [Subtype.range_val] using hB)
    intro U
    apply (ConcreteCategory.isIso_iff_bijective _).mpr
    exact SectionEvaluationLocal.Construction.sectionEvaluation_app_bijective_of_frame π s hs hf L U.1 U.2.some
  have : IsIso ((Scheme.Modules.toPresheaf S).map q) :=
    inferInstanceAs (IsIso ((sheafToPresheaf _ _).map ((SheafOfModules.toSheaf S.ringCatSheaf).map q)))
  exact isIso_of_reflects_iso q (Scheme.Modules.toPresheaf S)

theorem sectionEvaluation_top_apply
    {X S : Scheme.{u}} (π : X ⟶ S) (s : S ⟶ X) (hs : s ≫ π = 𝟙 S)
    (L : X.Modules) (m : Γ(L, ⊤)) :
    (SectionEvaluation.Construction.sectionEvaluation π s hs L).app ⊤ m = PullbackModuleSections.Construction.modulePullbackGlobalSection s L m := by
  have h := SectionEvaluation.Construction.sectionEvaluation_apply π s hs L ⊤ m
  change (SectionEvaluation.Construction.sectionEvaluation π s hs L).app ⊤ m =
    ((Scheme.Modules.pullback s).obj L).presheaf.map (𝟙 (.op ⊤)) (PullbackModuleSections.Construction.modulePullbackGlobalSection s L m) at h
  exact h.trans (congrArg (fun f ↦ f (PullbackModuleSections.Construction.modulePullbackGlobalSection s L m))
    (((Scheme.Modules.pullback s).obj L).presheaf.map_id (.op ⊤)))

theorem modulePullback_sections_bijective_of_relative_frames
    {X S : Scheme.{u}} (π : X ⟶ S) (s : S ⟶ X) (hs : s ≫ π = 𝟙 S)
    (hf : ∀ U : S.Opens, IsIso (π.app U)) (L : X.Modules)
    (hloc : ∀ x : S, ∃ U : S.Opens, x ∈ U ∧
      Nonempty ((Scheme.Modules.pullback (π ⁻¹ᵁ U).ι).obj L ≅ LineBundle.Construction.structureSheafModule (π ⁻¹ᵁ U).toScheme)) :
    Function.Bijective (PullbackModuleSections.Construction.modulePullbackGlobalSection s L) := by
  have : IsIso (SectionEvaluation.Construction.sectionEvaluation π s hs L) := sectionEvaluation_isIso_of_local_frames π s hs hf L hloc
  have he : ((SectionEvaluation.Construction.sectionEvaluation π s hs L).app ⊤ : Γ(L, ⊤) → Γ((Scheme.Modules.pullback s).obj L, ⊤)) =
      PullbackModuleSections.Construction.modulePullbackGlobalSection s L := funext (sectionEvaluation_top_apply π s hs L)
  exact he ▸ (ConcreteCategory.bijective_of_isIso ((SectionEvaluation.Construction.sectionEvaluation π s hs L).app ⊤))

end

end OAI.ArithmeticGeometry.OrdinaryLocus.Openness.SectionEvaluationIso.Construction
