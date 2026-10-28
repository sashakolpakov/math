import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Line.Bundles

/-! # Transitions -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.OpenFrame.Transitions

noncomputable section

/-! Transition units for local frames, expressed on arbitrary common subopens so restriction and cocycle identities have one common section ring. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u v

variable {X : Scheme.{u}} {ι : Type v}

structure OpenFrameTransitions (U : ι → X.Opens) where
  value : ∀ (V : X.Opens) (i j : ι), V ≤ U i → V ≤ U j → Γ(X, V)ˣ
  restrict : ∀ (V W : X.Opens) (h : W ≤ V) (i j : ι) (hi : V ≤ U i) (hj : V ≤ U j),
    X.presheaf.map (homOfLE h).op (value V i j hi hj).val =
      (value W i j (h.trans hi) (h.trans hj)).val
  self : ∀ (V : X.Opens) (i : ι) (hi : V ≤ U i), value V i i hi hi = 1
  comp : ∀ (V : X.Opens) (i j k : ι) (hi : V ≤ U i) (hj : V ≤ U j) (hk : V ≤ U k),
    value V i j hi hj * value V j k hj hk = value V i k hi hk

namespace OpenFrameTransitions

variable {U : ι → X.Opens} (D : OpenFrameTransitions U)

theorem inverse (V : X.Opens) (i j : ι) (hi : V ≤ U i) (hj : V ≤ U j) :
    (D.value V i j hi hj)⁻¹ = D.value V j i hj hi := by
  apply (inv_eq_iff_mul_eq_one).mpr
  exact (D.comp V i j i hi hj hi).trans (D.self V i hi)

def trivial (U : ι → X.Opens) : OpenFrameTransitions U where
  value _ _ _ _ _ := 1
  restrict _ _ _ _ _ _ _ := map_one _
  self _ _ _ := rfl
  comp _ _ _ _ _ _ _ := one_mul 1

end OpenFrameTransitions

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.OpenFrame.Transitions
