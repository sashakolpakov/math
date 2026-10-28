import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.OpenFrame.PullbackCompatibility
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.OpenFrame.SectionGenerators

/-! # Pullback Generators -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.OpenFrame.PullbackGenerators

noncomputable section

/-! Pulling frame coefficients back sends each actual local generator to the corresponding pulled-back generator. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

variable {X Y : Scheme.{u}} {ι : Type u} {U : ι → Y.Opens} (D : Transitions.OpenFrameTransitions U) (f : X ⟶ Y)

theorem openFrameSectionPullback_generator (W : Y.Opens) (i : ι) (hi : W ≤ U i) (r : Γ(Y, W)) :
    PullbackCompatibility.openFrameSectionPullback D f W (SectionGenerators.openFrameGenerator D W i hi r) =
      SectionGenerators.openFrameGenerator (D.pullback f) (f ⁻¹ᵁ W) i ((TopologicalSpace.Opens.map f.base).monotone hi) (f.app W r) := by
  apply Subtype.ext
  funext j
  let Q := W ⊓ U j
  have qi : Q ≤ U i := inf_le_left.trans hi
  have qj : Q ≤ U j := inf_le_right
  have ht := D.pullback_value_on_preimage f Q j i qj qi
  have hr := ConcreteCategory.congr_hom
    (f.naturality (homOfLE (show Q ≤ W from inf_le_left)).op) r
  exact ((f.app Q).hom.map_mul _ _).trans
    (congrArg₂ (fun a b : Γ(X, f ⁻¹ᵁ Q) => a * b) ht.symm hr)

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.OpenFrame.PullbackGenerators
