import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.OpenFrame.GeneratorNaturality

/-! # Generator Changes -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.OpenFrame.GeneratorChanges

noncomputable section

/-! The local generators of the glued frame module change by the prescribed transition unit. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

variable {X : Scheme.{u}} {ι : Type u} {U : ι → X.Opens} (D : Transitions.OpenFrameTransitions U)

theorem openFrameGenerator_change (V : X.Opens) (i j : ι) (hi : V ≤ U i) (hj : V ≤ U j)
    (x : Γ(X, V)) :
    SectionGenerators.openFrameGenerator D V i hi ((D.value V i j hi hj).val * x) = SectionGenerators.openFrameGenerator D V j hj x := by
  apply Subtype.ext
  funext k
  let W := V ⊓ U k
  have hwi : W ≤ U i := inf_le_left.trans hi
  have hwj : W ≤ U j := inf_le_left.trans hj
  have ht := D.restrict V W inf_le_left i j hi hj
  have hc : (D.value W k i inf_le_right hwi).val * (D.value W i j hwi hwj).val =
      (D.value W k j inf_le_right hwj).val := congrArg Units.val (D.comp W k i j inf_le_right hwi hwj)
  have hm := ((X.presheaf.map (homOfLE (show W ≤ V from inf_le_left)).op).hom.map_mul
    (D.value V i j hi hj).val x).trans
      (congrArg (fun a : Γ(X, W) => a * X.presheaf.map (homOfLE (show W ≤ V from inf_le_left)).op x) ht)
  exact (congrArg (fun a : Γ(X, W) => (D.value W k i inf_le_right hwi).val * a) hm).trans
    ((mul_assoc _ _ _).symm.trans (congrArg (fun a : Γ(X, W) =>
      a * X.presheaf.map (homOfLE (show W ≤ V from inf_le_left)).op x) hc))

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.OpenFrame.GeneratorChanges
