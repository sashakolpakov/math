import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.RegularPair.PairPullback
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.RegularPair.CupSymmetry

/-! # Cup Pullback -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Regular.CupPullback

noncomputable section

/-! Original scheme section maps preserve actual cup sections and
literal triple-boundary witnesses on inverse-image covers. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

variable {X Y : Scheme.{0}} (f : X ⟶ Y) {I : Type} (U : I → Y.Opens)

def regularTriplePullback (w : ∀ i j l, Γ(Y, (U i ⊓ U j) ⊓ U l))
    (i j l : I) : Γ(X, ((f ⁻¹ᵁ U i) ⊓ (f ⁻¹ᵁ U j)) ⊓ (f ⁻¹ᵁ U l)) :=
  f.app ((U i ⊓ U j) ⊓ U l) (w i j l)

theorem regularPairCupTriple_pullback (v w : ∀ i j, Γ(Y, U i ⊓ U j)) :
    regularTriplePullback f U (RegularPair.CupSymmetry.regularPairCupTriple Y U v w) =
      RegularPair.CupSymmetry.regularPairCupTriple X (fun i => f ⁻¹ᵁ U i)
        (RegularPair.PairPullback.regularPairPullback f U v) (RegularPair.PairPullback.regularPairPullback f U w) := by
  funext i j l
  let W := (U i ⊓ U j) ⊓ U l
  have h₁ : W ≤ U i ⊓ U j := inf_le_left
  have h₂ : W ≤ U j ⊓ U l := le_inf (inf_le_left.trans inf_le_right) inf_le_right
  change f.app W (Y.presheaf.map (homOfLE h₁).op (v i j) *
    Y.presheaf.map (homOfLE h₂).op (w j l)) = _
  rw [map_mul]
  exact congrArg₂ (· * ·) (RegularPair.PairPullback.regularSectionPullback_restrict f h₁ (v i j))
    (RegularPair.PairPullback.regularSectionPullback_restrict f h₂ (w j l))

theorem regularTripleBoundary_pullback
    (p : ∀ i j, Γ(Y, U i ⊓ U j))
    (w : ∀ i j l, Γ(Y, (U i ⊓ U j) ⊓ U l)) (hp : BoundaryShuffle.RegularTripleBoundary Y U p w) :
    BoundaryShuffle.RegularTripleBoundary X (fun i => f ⁻¹ᵁ U i)
      (RegularPair.PairPullback.regularPairPullback f U p) (regularTriplePullback f U w) := by
  intro i j l
  let W := (U i ⊓ U j) ⊓ U l
  have h₁ : W ≤ U i ⊓ U j := inf_le_left
  have h₂ : W ≤ U j ⊓ U l := le_inf (inf_le_left.trans inf_le_right) inf_le_right
  have h₃ : W ≤ U i ⊓ U l := le_inf (inf_le_left.trans inf_le_left) inf_le_right
  have h := congrArg (f.app W) (hp i j l)
  rw [map_add, map_sub] at h
  exact (congrArg₂ (fun a b : Γ(X, f ⁻¹ᵁ W) => a + b)
    (congrArg₂ (fun a b : Γ(X, f ⁻¹ᵁ W) => a - b) (RegularPair.PairPullback.regularSectionPullback_restrict f h₂ (p j l)).symm
      (RegularPair.PairPullback.regularSectionPullback_restrict f h₃ (p i l)).symm)
    (RegularPair.PairPullback.regularSectionPullback_restrict f h₁ (p i j)).symm).trans h

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Regular.CupPullback
