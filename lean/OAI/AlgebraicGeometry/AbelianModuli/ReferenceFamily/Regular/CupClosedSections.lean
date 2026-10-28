import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Regular.BoundaryShuffle
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.RegularPair.CupSymmetry

/-! # Cup Closed Sections -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Regular.CupClosedSections

noncomputable section

/-! The product of two original regular pair cocycles satisfies the
degree-two cocycle identity on every common algebraic open. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

variable (X : Scheme.{0}) {I : Type} (U : I → X.Opens)

theorem regularPairCocycle_on
    (v : ∀ i j, Γ(X, U i ⊓ U j)) (hv : RegularPair.Closed.RegularPairCocycle X U v)
    (a b c : I) (W : X.Opens) (ha : W ≤ U a) (hb : W ≤ U b) (hc : W ≤ U c) :
    BoundaryShuffle.regularPairSectionOn X U v a b W ha hb + BoundaryShuffle.regularPairSectionOn X U v b c W hb hc =
      BoundaryShuffle.regularPairSectionOn X U v a c W ha hc := by
  have h := congrArg (fun s => X.presheaf.map (homOfLE (le_inf (le_inf ha hb) hc)).op s)
    (hv a b c)
  rw [map_add, RegularPair.Closed.regularSectionRestrict_comp, RegularPair.Closed.regularSectionRestrict_comp,
    RegularPair.Closed.regularSectionRestrict_comp] at h
  exact h

theorem regularPairCupTriple_on
    (v w : ∀ i j, Γ(X, U i ⊓ U j))
    (a b c : I) (W : X.Opens) (ha : W ≤ U a) (hb : W ≤ U b) (hc : W ≤ U c) :
    BoundaryShuffle.regularTripleSectionOn X U (RegularPair.CupSymmetry.regularPairCupTriple X U v w) a b c W ha hb hc =
      BoundaryShuffle.regularPairSectionOn X U v a b W ha hb * BoundaryShuffle.regularPairSectionOn X U w b c W hb hc := by
  dsimp only [BoundaryShuffle.regularTripleSectionOn, RegularPair.CupSymmetry.regularPairCupTriple, BoundaryShuffle.regularPairSectionOn]
  rw [map_mul, RegularPair.Closed.regularSectionRestrict_comp, RegularPair.Closed.regularSectionRestrict_comp]

theorem regularPairCupTriple_quadruple
    (v w : ∀ i j, Γ(X, U i ⊓ U j))
    (hv : RegularPair.Closed.RegularPairCocycle X U v) (hw : RegularPair.Closed.RegularPairCocycle X U w)
    (a b c d : I) (W : X.Opens)
    (ha : W ≤ U a) (hb : W ≤ U b) (hc : W ≤ U c) (hd : W ≤ U d) :
    BoundaryShuffle.regularTripleSectionOn X U (RegularPair.CupSymmetry.regularPairCupTriple X U v w) b c d W hb hc hd -
      BoundaryShuffle.regularTripleSectionOn X U (RegularPair.CupSymmetry.regularPairCupTriple X U v w) a c d W ha hc hd +
      BoundaryShuffle.regularTripleSectionOn X U (RegularPair.CupSymmetry.regularPairCupTriple X U v w) a b d W ha hb hd -
      BoundaryShuffle.regularTripleSectionOn X U (RegularPair.CupSymmetry.regularPairCupTriple X U v w) a b c W ha hb hc = 0 := by
  rw [regularPairCupTriple_on, regularPairCupTriple_on, regularPairCupTriple_on,
    regularPairCupTriple_on, ← regularPairCocycle_on X U v hv a b c W ha hb hc,
    ← regularPairCocycle_on X U w hw b c d W hb hc hd]
  ring

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Regular.CupClosedSections
