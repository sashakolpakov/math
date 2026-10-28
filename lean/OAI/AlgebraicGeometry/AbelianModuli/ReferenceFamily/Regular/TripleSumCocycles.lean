import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Regular.CupClassAddition

/-! # Triple Sum Cocycles -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Regular.TripleSumCocycles

noncomputable section

/-! Finite sums of original regular degree-two cocycles remain
closed in the native Cech complex. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace
open scoped BigOperators

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {Y : TopCat.{0}} {I : Type} (U : I → Opens Y)

theorem cechDelta_zero (F : Y.Presheaf AddCommGrpCat.{0}) (n : ℕ) :
    DivisorClass.Chern.Abelian.CechCoordinates.abelianCechDelta F U n 0 = 0 := by
  have h := Cech.Add.cechDelta_sub U F n 0 0
  simpa only [sub_self] using h

theorem cechDelta_finsetSum (F : Y.Presheaf AddCommGrpCat.{0}) (n : ℕ)
    {B : Type} (t : Finset B) (w : B → DivisorClass.Chern.Abelian.CechCoordinates.AbelianCechCochain F U n) :
    DivisorClass.Chern.Abelian.CechCoordinates.abelianCechDelta F U n (∑ a ∈ t, w a) = ∑ a ∈ t, DivisorClass.Chern.Abelian.CechCoordinates.abelianCechDelta F U n (w a) := by
  classical
  induction t using Finset.induction_on with
  | empty => simp only [Finset.sum_empty, cechDelta_zero]
  | @insert a t hat ih => rw [Finset.sum_insert hat, Cech.Add.cechDelta_add, ih, Finset.sum_insert hat]

theorem cechSum_closed (F : Y.Presheaf AddCommGrpCat.{0}) (n : ℕ)
    {B : Type} (t : Finset B) (w : B → DivisorClass.Chern.Abelian.CechCoordinates.AbelianCechCochain F U n)
    (hw : ∀ a ∈ t, DivisorClass.Chern.Abelian.CechCoordinates.abelianCechDelta F U n (w a) = 0) :
    DivisorClass.Chern.Abelian.CechCoordinates.abelianCechDelta F U n (∑ a ∈ t, w a) = 0 := by
  rw [cechDelta_finsetSum]
  exact Finset.sum_eq_zero hw

variable (X : Scheme.{0}) {J : Type} (V : J → X.Opens)

theorem regularTripleCechCochain_sum {B : Type} (t : Finset B)
    (w : B → ∀ i j l, Γ(X, (V i ⊓ V j) ⊓ V l)) :
    BoundaryShuffle.regularTripleCechCochain X V (fun i j l => ∑ a ∈ t, w a i j l) =
      ∑ a ∈ t, BoundaryShuffle.regularTripleCechCochain X V (w a) := by
  funext a
  simp only [BoundaryShuffle.regularTripleCechCochain, map_sum, Finset.sum_apply]

theorem regularTripleCechCochain_sum_closed {B : Type} (t : Finset B)
    (w : B → ∀ i j l, Γ(X, (V i ⊓ V j) ⊓ V l))
    (hw : ∀ a ∈ t, DivisorClass.Chern.Abelian.CechCoordinates.abelianCechDelta (Dual.UnitCechClasses.ringAdditiveSheaf X.sheaf).obj V 2
      (BoundaryShuffle.regularTripleCechCochain X V (w a)) = 0) :
    DivisorClass.Chern.Abelian.CechCoordinates.abelianCechDelta (Dual.UnitCechClasses.ringAdditiveSheaf X.sheaf).obj V 2
      (BoundaryShuffle.regularTripleCechCochain X V (fun i j l => ∑ a ∈ t, w a i j l)) = 0 := by
  rw [regularTripleCechCochain_sum]
  exact cechSum_closed V (Dual.UnitCechClasses.ringAdditiveSheaf X.sheaf).obj 2 t _ hw

theorem regularPairMixedCupSum_cech_closed {B : Type} [Fintype B]
    (v w v' w' : B → ∀ i j, Γ(X, V i ⊓ V j))
    (hv : ∀ a, RegularPair.Closed.RegularPairCocycle X V (v a)) (hw : ∀ a, RegularPair.Closed.RegularPairCocycle X V (w a))
    (hv' : ∀ a, RegularPair.Closed.RegularPairCocycle X V (v' a)) (hw' : ∀ a, RegularPair.Closed.RegularPairCocycle X V (w' a)) :
    DivisorClass.Chern.Abelian.CechCoordinates.abelianCechDelta (Dual.UnitCechClasses.ringAdditiveSheaf X.sheaf).obj V 2
      (BoundaryShuffle.regularTripleCechCochain X V (fun i j l => ∑ a,
        (RegularPair.CupSymmetry.regularPairCupTriple X V (v a) (w a) i j l +
          RegularPair.CupSymmetry.regularPairCupTriple X V (v' a) (w' a) i j l))) = 0 := by
  apply regularTripleCechCochain_sum_closed X V Finset.univ
  intro a _
  rw [CupClassAddition.regularTripleCechCochain_add]
  exact Cech.Add.cechAdd_closed V (Dual.UnitCechClasses.ringAdditiveSheaf X.sheaf).obj 2 _ _
    (CupCechClass.regularPairCupTriple_cech_closed X V (v a) (w a) (hv a) (hw a))
    (CupCechClass.regularPairCupTriple_cech_closed X V (v' a) (w' a) (hv' a) (hw' a))

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Regular.TripleSumCocycles
