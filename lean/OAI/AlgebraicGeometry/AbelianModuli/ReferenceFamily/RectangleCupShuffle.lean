import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.RectangleBoundaryShuffle
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Regular.CupClosedSections
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.RegularPair.PairPullback
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.RegularPair.Refinement

/-! # Rectangle Cup Shuffle -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.RectangleCupShuffle

noncomputable section

/-! The actual projection pullbacks on a rectangle cover have cup
shuffles equal to the product tensor, with the reverse order negative. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
open scoped TensorProduct

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

theorem regularPairCocycle_self (X : Scheme.{0}) {I : Type} (U : I → X.Opens)
    (v : ∀ i j, Γ(X, U i ⊓ U j)) (hv : RegularPair.Closed.RegularPairCocycle X U v) (i : I) :
    v i i = 0 := by
  have h := Regular.CupClosedSections.regularPairCocycle_on X U v hv i i i (U i ⊓ U i)
    inf_le_left inf_le_left inf_le_left
  change X.presheaf.map (𝟙 _) (v i i) + X.presheaf.map (𝟙 _) (v i i) =
    X.presheaf.map (𝟙 _) (v i i) at h
  simp only [X.presheaf.map_id, CommRingCat.id_apply] at h
  exact add_eq_left.mp h

variable {k : Type} [Field k] {X Y : Scheme.{0}}
    (f : X ⟶ Spec (.of k)) (g : Y ⟶ Spec (.of k))
    {I J : Type} (U : I → X.Opens) (V : J → Y.Opens)

def rectangleLeftRegularPair (v : ∀ i i', Γ(X, U i ⊓ U i')) :
    Quotients.FiniteDescent.CubeProductCechCocycles.Construction.CubeCech.rectangleOrdinaryCech1 f g U V :=
  RegularPair.Refinement.regularPairRefinement (pullback f g) (fun i => (pullback.fst f g) ⁻¹ᵁ U i)
    (Quotients.FiniteDescent.CubeProductCechCocycles.Construction.CubeCech.rectangleOpenCover f g U V) Sigma.fst (fun _ => inf_le_left)
    (RegularPair.PairPullback.regularPairPullback (pullback.fst f g) U v)

def rectangleRightRegularPair (w : ∀ j j', Γ(Y, V j ⊓ V j')) :
    Quotients.FiniteDescent.CubeProductCechCocycles.Construction.CubeCech.rectangleOrdinaryCech1 f g U V :=
  RegularPair.Refinement.regularPairRefinement (pullback f g) (fun j => (pullback.snd f g) ⁻¹ᵁ V j)
    (Quotients.FiniteDescent.CubeProductCechCocycles.Construction.CubeCech.rectangleOpenCover f g U V) (fun p => p.2) (fun _ => inf_le_right)
    (RegularPair.PairPullback.regularPairPullback (pullback.snd f g) V w)

theorem rectangleLeftRegularPair_cocycle
    (v : ∀ i i', Γ(X, U i ⊓ U i')) (hv : RegularPair.Closed.RegularPairCocycle X U v) :
    RegularPair.Closed.RegularPairCocycle (pullback f g) (Quotients.FiniteDescent.CubeProductCechCocycles.Construction.CubeCech.rectangleOpenCover f g U V)
      (rectangleLeftRegularPair f g U V v) :=
  RegularPair.Refinement.regularPairRefinement_cocycle (pullback f g) _ _ _ _ _
    (RegularPair.PairPullback.regularPairPullback_cocycle (pullback.fst f g) U v hv)

theorem rectangleRightRegularPair_cocycle
    (w : ∀ j j', Γ(Y, V j ⊓ V j')) (hw : RegularPair.Closed.RegularPairCocycle Y V w) :
    RegularPair.Closed.RegularPairCocycle (pullback f g) (Quotients.FiniteDescent.CubeProductCechCocycles.Construction.CubeCech.rectangleOpenCover f g U V)
      (rectangleRightRegularPair f g U V w) :=
  RegularPair.Refinement.regularPairRefinement_cocycle (pullback f g) _ _ _ _ _
    (RegularPair.PairPullback.regularPairPullback_cocycle (pullback.snd f g) V w hw)

theorem rectangleLeftRegularPair_on
    (v : ∀ i i', Γ(X, U i ⊓ U i')) (p q : Σ _ : I, J)
    (W : (pullback f g).Opens)
    (hp : W ≤ Quotients.FiniteDescent.CubeProductCechCocycles.Construction.CubeCech.rectangleOpenCover f g U V p) (hq : W ≤ Quotients.FiniteDescent.CubeProductCechCocycles.Construction.CubeCech.rectangleOpenCover f g U V q) :
    Regular.BoundaryShuffle.regularPairSectionOn (pullback f g) (Quotients.FiniteDescent.CubeProductCechCocycles.Construction.CubeCech.rectangleOpenCover f g U V)
      (rectangleLeftRegularPair f g U V v) p q W hp hq =
      (pullback.fst f g).appLE (U p.1 ⊓ U q.1) W
        (le_inf (hp.trans inf_le_left) (hq.trans inf_le_left)) (v p.1 q.1) := by
  dsimp only [Regular.BoundaryShuffle.regularPairSectionOn, rectangleLeftRegularPair, RegularPair.Refinement.regularPairRefinement,
    RegularPair.PairPullback.regularPairPullback, Scheme.Hom.appLE]
  erw [RegularPair.Closed.regularSectionRestrict_comp]
  rfl

theorem rectangleRightRegularPair_on
    (w : ∀ j j', Γ(Y, V j ⊓ V j')) (p q : Σ _ : I, J)
    (W : (pullback f g).Opens)
    (hp : W ≤ Quotients.FiniteDescent.CubeProductCechCocycles.Construction.CubeCech.rectangleOpenCover f g U V p) (hq : W ≤ Quotients.FiniteDescent.CubeProductCechCocycles.Construction.CubeCech.rectangleOpenCover f g U V q) :
    Regular.BoundaryShuffle.regularPairSectionOn (pullback f g) (Quotients.FiniteDescent.CubeProductCechCocycles.Construction.CubeCech.rectangleOpenCover f g U V)
      (rectangleRightRegularPair f g U V w) p q W hp hq =
      (pullback.snd f g).appLE (V p.2 ⊓ V q.2) W
        (le_inf (hp.trans inf_le_right) (hq.trans inf_le_right)) (w p.2 q.2) := by
  dsimp only [Regular.BoundaryShuffle.regularPairSectionOn, rectangleRightRegularPair, RegularPair.Refinement.regularPairRefinement,
    RegularPair.PairPullback.regularPairPullback, Scheme.Hom.appLE]
  erw [RegularPair.Closed.regularSectionRestrict_comp]
  rfl

variable [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]
    (hUU : ∀ i i', IsAffineOpen (U i ⊓ U i'))
    (hVV : ∀ j j', IsAffineOpen (V j ⊓ V j'))

theorem rectangleTripleShuffle_cup_left_right
    (v : ∀ i i', Γ(X, U i ⊓ U i')) (w : ∀ j j', Γ(Y, V j ⊓ V j'))
    (hv : RegularPair.Closed.RegularPairCocycle X U v) :
    RectangleBoundaryShuffle.rectangleTripleShuffle f g U V
      (RegularPair.CupSymmetry.regularPairCupTriple (pullback f g) (Quotients.FiniteDescent.CubeProductCechCocycles.Construction.CubeCech.rectangleOpenCover f g U V)
        (rectangleLeftRegularPair f g U V v) (rectangleRightRegularPair f g U V w)) =
      Quotients.FiniteDescent.CubeProductCechOverlaps.Construction.CubeCech.productCech11Equiv f g U V hUU hVV (v ⊗ₜ[k] w) := by
  funext i i' j j'
  dsimp only [RectangleBoundaryShuffle.rectangleTripleShuffle]
  erw [Regular.CupClosedSections.regularPairCupTriple_on, Regular.CupClosedSections.regularPairCupTriple_on,
    rectangleLeftRegularPair_on, rectangleRightRegularPair_on,
    rectangleLeftRegularPair_on, rectangleRightRegularPair_on,
    regularPairCocycle_self X U v hv i, map_zero, zero_mul, sub_zero,
    Quotients.FiniteDescent.CubeProductCechOverlaps.Construction.CubeCech.productCech11Equiv_tmul]

theorem rectangleTripleShuffle_cup_right_left
    (v : ∀ i i', Γ(X, U i ⊓ U i')) (w : ∀ j j', Γ(Y, V j ⊓ V j'))
    (hw : RegularPair.Closed.RegularPairCocycle Y V w) :
    RectangleBoundaryShuffle.rectangleTripleShuffle f g U V
      (RegularPair.CupSymmetry.regularPairCupTriple (pullback f g) (Quotients.FiniteDescent.CubeProductCechCocycles.Construction.CubeCech.rectangleOpenCover f g U V)
        (rectangleRightRegularPair f g U V w) (rectangleLeftRegularPair f g U V v)) =
      -Quotients.FiniteDescent.CubeProductCechOverlaps.Construction.CubeCech.productCech11Equiv f g U V hUU hVV (v ⊗ₜ[k] w) := by
  funext i i' j j'
  change _ = -(Quotients.FiniteDescent.CubeProductCechOverlaps.Construction.CubeCech.productCech11Equiv f g U V hUU hVV (v ⊗ₜ[k] w) i i' j j')
  dsimp only [RectangleBoundaryShuffle.rectangleTripleShuffle]
  erw [Regular.CupClosedSections.regularPairCupTriple_on, Regular.CupClosedSections.regularPairCupTriple_on,
    rectangleRightRegularPair_on, rectangleLeftRegularPair_on,
    rectangleRightRegularPair_on, rectangleLeftRegularPair_on,
    regularPairCocycle_self Y V w hw j, map_zero, zero_mul, zero_sub,
    Quotients.FiniteDescent.CubeProductCechOverlaps.Construction.CubeCech.productCech11Equiv_tmul, mul_comm]

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.RectangleCupShuffle
