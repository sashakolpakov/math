import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Regular.BoundaryShuffle

/-! # Cup Symmetry -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.RegularPair.CupSymmetry

noncomputable section

/-! The literal front/back product of two original regular pair
cocycles is skew-commutative in native sheaf H2: the symmetric sum
has the explicit pair primitive minus their pointwise product. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace

variable (X : Scheme.{0}) {I : Type} (U : I → X.Opens)

def regularPairCupTriple (v w : ∀ i j : I, Γ(X, U i ⊓ U j)) (i j l : I) :
    Γ(X, (U i ⊓ U j) ⊓ U l) :=
  X.presheaf.map (homOfLE (show (U i ⊓ U j) ⊓ U l ≤ U i ⊓ U j from inf_le_left)).op (v i j) *
    X.presheaf.map (homOfLE (show (U i ⊓ U j) ⊓ U l ≤ U j ⊓ U l from
      le_inf (inf_le_left.trans inf_le_right) inf_le_right)).op (w j l)

theorem regularPairCup_symm_boundary (v w : ∀ i j : I, Γ(X, U i ⊓ U j))
    (hv : Closed.RegularPairCocycle X U v) (hw : Closed.RegularPairCocycle X U w) :
    Regular.BoundaryShuffle.RegularTripleBoundary X U (fun i j => -(v i j * w i j))
      (fun i j l => regularPairCupTriple X U v w i j l + regularPairCupTriple X U w v i j l) := by
  intro i j l
  dsimp only [regularPairCupTriple]
  rw [map_neg, map_mul, map_neg, map_mul, map_neg, map_mul]
  rw [← hv i j l, ← hw i j l]
  ring

theorem regularPairCup_symm_class_zero (hU : iSup U = ⊤) (v w : ∀ i j : I, Γ(X, U i ⊓ U j))
    (hv : Closed.RegularPairCocycle X U v) (hw : Closed.RegularPairCocycle X U w) :
    DivisorClass.Chern.Abelian.CechClasses.abelianCechSheafClass (X := X.toPresheafedSpace.carrier) U (Dual.UnitCechClasses.ringAdditiveSheaf X.sheaf) hU 1
      (Regular.BoundaryShuffle.regularTripleCechCochain X U
        (fun i j l => regularPairCupTriple X U v w i j l + regularPairCupTriple X U w v i j l))
      (Regular.BoundaryShuffle.regularTripleCechCochain_closed X U _ _ (regularPairCup_symm_boundary X U v w hv hw)) =
        (0 : (CategoryTheory.Sheaf.functorH (Opens.grothendieckTopology X.toPresheafedSpace.carrier) 2).obj
          (Dual.UnitCechClasses.ringAdditiveSheaf X.sheaf)) :=
  Regular.BoundaryShuffle.regularTripleCechClass_eq_zero X U hU _ _ (regularPairCup_symm_boundary X U v w hv hw)

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.RegularPair.CupSymmetry
