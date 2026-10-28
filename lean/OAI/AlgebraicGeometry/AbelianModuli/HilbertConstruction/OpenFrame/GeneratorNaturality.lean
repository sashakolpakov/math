import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.OpenFrame.LocalFreeness
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.OpenFrame.RestrictionCompatibility

/-! # Generator Naturality -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.OpenFrame.GeneratorNaturality

noncomputable section

/-! The local rank-one generators commute with actual regular-function and frame-section restriction maps. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

variable {X : Scheme.{u}} {ι : Type u} {U : ι → X.Opens} (D : Transitions.OpenFrameTransitions U)

theorem openFrameGenerator_restriction {V W : X.Opens} (h : W ≤ V) (k : ι) (hV : V ≤ U k) (x : Γ(X, V)) :
    RestrictionCompatibility.openFrameSectionRestriction D h (SectionGenerators.openFrameGenerator D V k hV x) =
      SectionGenerators.openFrameGenerator D W k (h.trans hV) (X.presheaf.map (homOfLE h).op x) := by
  apply Subtype.ext
  funext i
  exact (D.frameValues_restrict V k hV x i (W ⊓ U i) (inf_le_inf h (le_refl (U i)))).trans
    (congrArg (fun z : Γ(X, W ⊓ U i) =>
      (D.value (W ⊓ U i) i k inf_le_right (inf_le_left.trans (h.trans hV))).val * z)
        (Relative.OpenFunctionUnits.openFunction_restriction_comp h (show W ⊓ U i ≤ W from inf_le_left) x).symm)

theorem openFrameGenerator_smul_one (V : X.Opens) (k : ι) (hV : V ≤ U k) (x : Γ(X, V)) :
    x • SectionGenerators.openFrameGenerator D V k hV 1 = SectionGenerators.openFrameGenerator D V k hV x :=
  ((SectionGenerators.openFrameGenerator D V k hV).map_smul x 1).symm.trans
    (congrArg (SectionGenerators.openFrameGenerator D V k hV) (mul_one x))

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.OpenFrame.GeneratorNaturality
