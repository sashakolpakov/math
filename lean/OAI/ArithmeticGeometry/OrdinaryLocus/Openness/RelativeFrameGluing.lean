import OAI.ArithmeticGeometry.OrdinaryLocus.Openness.SectionEvaluationIso
import OAI.ArithmeticGeometry.OrdinaryLocus.Openness.ReflectsLineBundleIso
import OAI.ArithmeticGeometry.OrdinaryLocus.Openness.LiftedTrivializingSection

/-! # Relative Frame Gluing -/

namespace OAI.ArithmeticGeometry.OrdinaryLocus.Openness.RelativeFrameGluing.Construction

noncomputable section

/-! Relative local frames glue to a global trivialization after rigidification along a section. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

theorem lineBundle_trivial_of_relative_frames
    {X S : Scheme.{u}} (π : X ⟶ S) (s : S ⟶ X) (hs : s ≫ π = 𝟙 S)
    (hf : ∀ U : S.Opens, IsIso (π.app U)) (L : X.Modules)
    (hloc : ∀ x : S, ∃ U : S.Opens, x ∈ U ∧
      Nonempty ((Scheme.Modules.pullback (π ⁻¹ᵁ U).ι).obj L ≅ LineBundle.Construction.structureSheafModule (π ⁻¹ᵁ U).toScheme))
    (e : (Scheme.Modules.pullback s).obj L ≅ LineBundle.Construction.structureSheafModule S) :
    Nonempty (L ≅ LineBundle.Construction.structureSheafModule X) := by
  have hsec := SectionEvaluationIso.Construction.modulePullback_sections_bijective_of_relative_frames π s hs hf L hloc
  obtain ⟨q, hq⟩ := LiftedTrivializingSection.Construction.exists_isIso_pullback_of_sections_surjective s L e hsec.surjective
  have : IsIso q := ReflectsLineBundleIso.Construction.section_reflects_isIso_of_relative_frames π s hs hf L hloc q
  exact ⟨(asIso q).symm⟩

end

end OAI.ArithmeticGeometry.OrdinaryLocus.Openness.RelativeFrameGluing.Construction
