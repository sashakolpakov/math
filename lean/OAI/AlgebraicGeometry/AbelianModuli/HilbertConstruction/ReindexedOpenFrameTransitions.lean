import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.OpenFrame.Transitions

/-! # Reindexed Open Frame Transitions -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction

noncomputable section

/-! Reindexing an actual transition cocycle, including universe lifting of finite coordinate covers. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u v w

variable {X : Scheme.{u}} {ι : Type v} {κ : Type w} {U : ι → X.Opens}

def OpenFrame.Transitions.OpenFrameTransitions.reindex (D : OpenFrame.Transitions.OpenFrameTransitions U) (f : κ → ι) :
    OpenFrame.Transitions.OpenFrameTransitions (fun k => U (f k)) where
  value V i j hi hj := D.value V (f i) (f j) hi hj
  restrict V W h i j hi hj := D.restrict V W h (f i) (f j) hi hj
  self V i hi := D.self V (f i) hi
  comp V i j k hi hj hk := D.comp V (f i) (f j) (f k) hi hj hk

def OpenFrame.Transitions.OpenFrameTransitions.power (D : OpenFrame.Transitions.OpenFrameTransitions U) (d : ℕ) : OpenFrame.Transitions.OpenFrameTransitions U where
  value V i j hi hj := D.value V i j hi hj ^ d
  restrict V W h i j hi hj := by
    change X.presheaf.map (homOfLE h).op ((D.value V i j hi hj).val ^ d) = _
    rw [(X.presheaf.map (homOfLE h).op).hom.map_pow, D.restrict]
    rfl
  self V i hi := by rw [D.self, one_pow]
  comp V i j k hi hj hk := by rw [← mul_pow, D.comp]

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction
