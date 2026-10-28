import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.OpenFrame.Transitions
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Relative.OpenFunctionUnits

/-! # Coordinate Compatibility -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.OpenFrame

noncomputable section

/-! A regular function on one frame open produces compatible coordinates on every overlap by the transition cocycle. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

variable {X : Scheme.{u}} {ι : Type u} {U : ι → X.Opens} (D : Transitions.OpenFrameTransitions U)

def Transitions.OpenFrameTransitions.frameValues (V : X.Opens) (k : ι) (hV : V ≤ U k) (x : Γ(X, V)) (i : ι) : Γ(X, V ⊓ U i) :=
  (D.value (V ⊓ U i) i k inf_le_right (inf_le_left.trans hV)).val *
    X.presheaf.map (homOfLE (show V ⊓ U i ≤ V from inf_le_left)).op x

theorem Transitions.OpenFrameTransitions.frameValues_restrict (V : X.Opens) (k : ι) (hV : V ≤ U k) (x : Γ(X, V)) (i : ι)
    (W : X.Opens) (hW : W ≤ V ⊓ U i) :
    X.presheaf.map (homOfLE hW).op (D.frameValues V k hV x i) =
      (D.value W i k (hW.trans inf_le_right) (hW.trans (inf_le_left.trans hV))).val *
        X.presheaf.map (homOfLE (hW.trans inf_le_left)).op x := by
  exact ((X.presheaf.map (homOfLE hW).op).hom.map_mul _ _).trans
    (congrArg₂ (fun a b : Γ(X, W) => a * b)
      (D.restrict (V ⊓ U i) W hW i k inf_le_right (inf_le_left.trans hV))
      (Relative.OpenFunctionUnits.openFunction_restriction_comp inf_le_left hW x))

theorem Transitions.OpenFrameTransitions.frameValues_compatible (V : X.Opens) (k : ι) (hV : V ≤ U k) (x : Γ(X, V)) (i j : ι) :
    X.presheaf.map (homOfLE (show (V ⊓ U i) ⊓ U j ≤ V ⊓ U i from inf_le_left)).op
      (D.frameValues V k hV x i) =
        (D.value ((V ⊓ U i) ⊓ U j) i j (inf_le_left.trans inf_le_right) inf_le_right).val *
          X.presheaf.map (homOfLE (show (V ⊓ U i) ⊓ U j ≤ V ⊓ U j from
            le_inf (inf_le_left.trans inf_le_left) inf_le_right)).op (D.frameValues V k hV x j) := by
  let W := (V ⊓ U i) ⊓ U j
  have hi : W ≤ U i := inf_le_left.trans inf_le_right
  have hj : W ≤ U j := inf_le_right
  have hk : W ≤ U k := (inf_le_left.trans inf_le_left).trans hV
  have hc : (D.value W i j hi hj).val * (D.value W j k hj hk).val = (D.value W i k hi hk).val :=
    congrArg Units.val (D.comp W i j k hi hj hk)
  have hl := D.frameValues_restrict V k hV x i W inf_le_left
  have hr := D.frameValues_restrict V k hV x j W (le_inf (inf_le_left.trans inf_le_left) inf_le_right)
  exact hl.trans ((congrArg (fun a : Γ(X, W) => a *
    (X.presheaf.map (homOfLE (show W ≤ V from inf_le_left.trans inf_le_left)).op x)) hc.symm).trans
      ((mul_assoc _ _ _).trans (congrArg (fun a : Γ(X, W) => (D.value W i j hi hj).val * a) hr.symm)))

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.OpenFrame
