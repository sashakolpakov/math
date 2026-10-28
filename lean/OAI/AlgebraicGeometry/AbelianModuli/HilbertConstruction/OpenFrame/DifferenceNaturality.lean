import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.OpenFrame.RestrictionCompatibility

/-! # Difference Naturality -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.OpenFrame.DifferenceNaturality

noncomputable section

/-! The difference measuring compatibility of two frame coordinates commutes with ordinary regular-function restriction. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

variable {X : Scheme.{u}} {ι : Type u} {U : ι → X.Opens} (D : Transitions.OpenFrameTransitions U)

theorem openFrameDifference_restriction {V W : X.Opens} (h : W ≤ V)
    (x : SectionModules.OpenFrameLocalTuple U V) (i j : ι) :
    SectionModules.openFrameDifference U D W i j (TupleRestrictions.openFrameTupleRestriction U h x) =
      X.presheaf.map (homOfLE (inf_le_inf (inf_le_inf h (le_refl (U i))) (le_refl (U j)))).op
        (SectionModules.openFrameDifference U D V i j x) := by
  let Q := (V ⊓ U i) ⊓ U j
  let Z := (W ⊓ U i) ⊓ U j
  have a : Z ≤ Q := inf_le_inf (inf_le_inf h (le_refl (U i))) (le_refl (U j))
  have qj : Q ≤ V ⊓ U j := le_inf (inf_le_left.trans inf_le_left) inf_le_right
  have zj : Z ≤ W ⊓ U j := le_inf (inf_le_left.trans inf_le_left) inf_le_right
  have hi := (Relative.OpenFunctionUnits.openFunction_restriction_comp (inf_le_inf h (le_refl (U i)))
    (show Z ≤ W ⊓ U i from inf_le_left) (x i)).trans
      (Relative.OpenFunctionUnits.openFunction_restriction_comp (show Q ≤ V ⊓ U i from inf_le_left) a (x i)).symm
  have hj := (Relative.OpenFunctionUnits.openFunction_restriction_comp (inf_le_inf h (le_refl (U j))) zj (x j)).trans
    (Relative.OpenFunctionUnits.openFunction_restriction_comp qj a (x j)).symm
  have ht := D.restrict Q Z a i j (inf_le_left.trans inf_le_right) inf_le_right
  have hm := (congrArg₂ (fun r s : Γ(X, Z) => r * s) ht.symm hj).trans
    ((X.presheaf.map (homOfLE a).op).hom.map_mul _ _).symm
  exact (congrArg₂ (fun r s : Γ(X, Z) => r - s) hi hm).trans
    ((X.presheaf.map (homOfLE a).op).hom.map_sub _ _).symm

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.OpenFrame.DifferenceNaturality
