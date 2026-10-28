import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.RegularPair.RefinedPullback
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Regular.CupPullback
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Regular.CupRefinement

/-! # Cup Refined Pullback -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Regular.CupRefinedPullback

noncomputable section

/-! The original cup-boundary witness survives scheme pullback
followed by arbitrary cover refinement, including finite cup sums. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped BigOperators

variable {A B : Over Foundations.Scheme.ProjectiveSpace.complexBase} (f : A ⟶ B) {I J : Type}
    (U : I → B.left.Opens) (V : J → A.left.Opens)
    (r : J → I) (hr : ∀ j, V j ≤ f.left ⁻¹ᵁ U (r j))

def regularTripleRefinedPullback (w : ∀ i j l, Γ(B.left, (U i ⊓ U j) ⊓ U l)) :=
  CupRefinement.regularTripleRefinement A.left (fun i => f.left ⁻¹ᵁ U i) V r hr
    (CupPullback.regularTriplePullback f.left U w)

theorem regularTripleRefinedPullback_boundary
    (p : ∀ i j, Γ(B.left, U i ⊓ U j))
    (w : ∀ i j l, Γ(B.left, (U i ⊓ U j) ⊓ U l)) (hp : BoundaryShuffle.RegularTripleBoundary B.left U p w) :
    BoundaryShuffle.RegularTripleBoundary A.left V (RegularPair.RefinedPullback.regularPairRefinedPullback f U V r hr p)
      (regularTripleRefinedPullback f U V r hr w) :=
  CupRefinement.regularTripleRefinement_boundary A.left _ V r hr _ _
    (CupPullback.regularTripleBoundary_pullback f.left U p w hp)

theorem regularTripleRefinedPullback_cup
    (v w : ∀ i j, Γ(B.left, U i ⊓ U j)) :
    regularTripleRefinedPullback f U V r hr (RegularPair.CupSymmetry.regularPairCupTriple B.left U v w) =
      RegularPair.CupSymmetry.regularPairCupTriple A.left V (RegularPair.RefinedPullback.regularPairRefinedPullback f U V r hr v)
        (RegularPair.RefinedPullback.regularPairRefinedPullback f U V r hr w) := by
  unfold regularTripleRefinedPullback RegularPair.RefinedPullback.regularPairRefinedPullback
  rw [CupPullback.regularPairCupTriple_pullback, CupRefinement.regularPairCupTriple_refinement]

theorem regularTripleRefinedPullback_sum {C : Type} (t : Finset C)
    (w : C → ∀ i j l, Γ(B.left, (U i ⊓ U j) ⊓ U l)) :
    regularTripleRefinedPullback f U V r hr (fun i j l => ∑ a ∈ t, w a i j l) =
      fun i j l => ∑ a ∈ t, regularTripleRefinedPullback f U V r hr (w a) i j l := by
  funext i j l
  dsimp only [regularTripleRefinedPullback, CupRefinement.regularTripleRefinement, CupPullback.regularTriplePullback]
  erw [map_sum, map_sum]

theorem regularTripleRefinedPullback_cupSum_boundary {C : Type} [Fintype C]
    (p : ∀ i j, Γ(B.left, U i ⊓ U j))
    (v w : C → ∀ i j, Γ(B.left, U i ⊓ U j))
    (hp : BoundaryShuffle.RegularTripleBoundary B.left U p
      (fun i j l => ∑ a, RegularPair.CupSymmetry.regularPairCupTriple B.left U (v a) (w a) i j l)) :
    BoundaryShuffle.RegularTripleBoundary A.left V (RegularPair.RefinedPullback.regularPairRefinedPullback f U V r hr p)
      (fun i j l => ∑ a, RegularPair.CupSymmetry.regularPairCupTriple A.left V
        (RegularPair.RefinedPullback.regularPairRefinedPullback f U V r hr (v a))
        (RegularPair.RefinedPullback.regularPairRefinedPullback f U V r hr (w a)) i j l) := by
  have h := regularTripleRefinedPullback_boundary f U V r hr p _ hp
  rw [regularTripleRefinedPullback_sum] at h
  simpa only [regularTripleRefinedPullback_cup] using h

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Regular.CupRefinedPullback
