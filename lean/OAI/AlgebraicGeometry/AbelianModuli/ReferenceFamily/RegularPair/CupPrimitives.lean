import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.RegularPair.CupSymmetry
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.RegularPair.Closed

/-! # Cup Primitives -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.RegularPair.CupPrimitives

noncomputable section

/-! Changing a regular H1 representative by an actual primitive
changes its front/back cup product by an explicit regular pair boundary.
Both signs are computed in the original section rings. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

variable (X : Scheme.{0}) {I : Type} (U : I → X.Opens)

def regularCupFrontPair (s : ∀ i, Γ(X, U i)) (w : ∀ i j, Γ(X, U i ⊓ U j))
    (i j : I) : Γ(X, U i ⊓ U j) :=
  X.presheaf.map (homOfLE inf_le_left).op (s i) * w i j

def regularCupBackPair (v : ∀ i j, Γ(X, U i ⊓ U j)) (s : ∀ i, Γ(X, U i))
    (i j : I) : Γ(X, U i ⊓ U j) :=
  v i j * X.presheaf.map (homOfLE inf_le_right).op (s j)

theorem regularPairCup_leftPrimitive (v w : ∀ i j, Γ(X, U i ⊓ U j))
    (s : ∀ i, Γ(X, U i)) (hv : Closed.RegularPairPrimitive X U v s) (hw : Closed.RegularPairCocycle X U w) :
    Regular.BoundaryShuffle.RegularTripleBoundary X U (fun i j => -regularCupFrontPair X U s w i j)
      (CupSymmetry.regularPairCupTriple X U v w) := by
  intro i j l
  dsimp only [regularCupFrontPair, CupSymmetry.regularPairCupTriple]
  rw [map_neg, map_mul, map_neg, map_mul, map_neg, map_mul,
    Closed.regularSectionRestrict_comp, Closed.regularSectionRestrict_comp, Closed.regularSectionRestrict_comp,
    hv i j, map_sub, Closed.regularSectionRestrict_comp, Closed.regularSectionRestrict_comp,
    ← hw i j l]
  ring

theorem regularPairCup_rightPrimitive (v w : ∀ i j, Γ(X, U i ⊓ U j))
    (s : ∀ i, Γ(X, U i)) (hv : Closed.RegularPairCocycle X U v) (hw : Closed.RegularPairPrimitive X U w s) :
    Regular.BoundaryShuffle.RegularTripleBoundary X U (regularCupBackPair X U v s) (CupSymmetry.regularPairCupTriple X U v w) := by
  intro i j l
  dsimp only [regularCupBackPair, CupSymmetry.regularPairCupTriple]
  rw [map_mul, map_mul, map_mul, Closed.regularSectionRestrict_comp,
    Closed.regularSectionRestrict_comp, Closed.regularSectionRestrict_comp,
    hw j l, map_sub, Closed.regularSectionRestrict_comp, Closed.regularSectionRestrict_comp,
    ← hv i j l]
  ring

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.RegularPair.CupPrimitives
