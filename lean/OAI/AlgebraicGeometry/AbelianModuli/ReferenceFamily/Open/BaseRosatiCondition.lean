import OAI.AlgebraicGeometry.PELModuli.IntegralModel.Open.BaseConditions
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Relative.RosatiBasisPullback
import OAI.AlgebraicGeometry.PELModuli.IntegralModel.RosatiIsoTransport
import OAI.AlgebraicGeometry.PELModuli.IntegralModel.PEL.Iso
import OAI.AlgebraicGeometry.PELModuli.IntegralModel.LieRankPullbackComposition

/-! # Base Rosati Condition -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Open.BaseRosatiCondition

noncomputable section

/-! The literal Rosati and arithmetic Lie-rank predicates are detected
on open base covers. Rosati uses actual finite dual-map equations. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

theorem rosati_of_open_base_cover
    {E : Type} [Field E] [NumberField E] [Algebra ℚ E] [NumberField.IsCMField E]
    {S : Scheme.{0}} [IsNoetherian S] (C : S.OpenCover)
    {g N : ℕ} {δ : Fin g → ℕ} (A : HilbertConstruction.PolarizationData.PolarizedAbelianWithFullLevel g δ N S)
    (ρ : ActionData.IntegralAction (NumberField.RingOfIntegers E) A.abelian)
    (h : ∀ i, ActionData.RosatiConjugation (A.pullback (C.f i)) (ρ.pullback (C.f i))) :
    ActionData.RosatiConjugation A ρ := by
  have hid : ActionData.RosatiConjugation (A.pullback (𝟙 S)) (ρ.pullback (𝟙 S)) := by
    apply (Relative.RosatiBasisPullback.rosati_iff_relative_pulledBack_basis_equations A ρ (𝟙 S)).mpr
    intro b
    apply congrArg ((Over.pullback (𝟙 S)).map)
    apply PELModuli.IntegralModel.Open.BaseGroupReflection.over_hom_ext_of_open_base_cover C
    intro i
    exact (Relative.RosatiBasisPullback.rosati_iff_relative_pulledBack_basis_equations A ρ (C.f i)).mp (h i) b
  let B : PELModuli.IntegralModel.PEL.Has.PolarizedActionData E g δ N S := ⟨A, ρ⟩
  let e := PELModuli.IntegralModel.PEL.Iso.PolarizedActionIso.pullbackId B
  exact PELModuli.IntegralModel.RosatiIsoTransport.rosati_of_polarized_iso e.polarized (ρ.pullback (𝟙 S)) ρ
    (fun a => (e.action a).symm) hid

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Open.BaseRosatiCondition
