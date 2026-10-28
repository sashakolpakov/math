import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Regular.CupCechClass
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.RegularPair.CupPrimitives
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.RegularPair.ClassDifference

/-! # Cup Class Addition -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Regular.CupClassAddition

noncomputable section

section

/-! On any common cover, the native H2 class of an actual regular cup
depends only on the two original H1 classes. Equal representatives give
explicit pair primitives; their cup differences are literal boundaries. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace

local instance cupClassAddCommGroup {Y : TopCat.{0}}
    (F : TopCat.Sheaf AddCommGrpCat.{0} Y) (n : ℕ) :
    AddCommGroup (CategoryTheory.Sheaf.H F n) :=
  inferInstanceAs (AddCommGroup ((CategoryTheory.Sheaf.functorH (Opens.grothendieckTopology Y) n).obj F))

theorem cechSheafClass_eq_of_sub_boundary {Y : TopCat.{0}} {I : Type}
    (U : I → Opens Y) (F : TopCat.Sheaf AddCommGrpCat.{0} Y) (hU : iSup U = ⊤) (n : ℕ)
    (a b : DivisorClass.Chern.Abelian.CechCoordinates.AbelianCechCochain F.obj U (n + 1))
    (ha : DivisorClass.Chern.Abelian.CechCoordinates.abelianCechDelta F.obj U (n + 1) a = 0)
    (hb : DivisorClass.Chern.Abelian.CechCoordinates.abelianCechDelta F.obj U (n + 1) b = 0)
    (p : DivisorClass.Chern.Abelian.CechCoordinates.AbelianCechCochain F.obj U n) (hp : DivisorClass.Chern.Abelian.CechCoordinates.abelianCechDelta F.obj U n p = a - b) :
    DivisorClass.Chern.Abelian.CechClasses.abelianCechSheafClass U F hU n a ha = DivisorClass.Chern.Abelian.CechClasses.abelianCechSheafClass U F hU n b hb := by
  apply sub_eq_zero.mp
  erw [← Cech.Add.cechSheafClass_sub U F hU n a b ha hb]
  exact DivisorClass.Chern.Cech.SheafBoundaries.abelianCechSheafClass_eq_zero_of_boundary U F hU n (a - b)
    (Cech.Add.cechSub_closed U F.obj (n + 1) a b ha hb) p hp

variable (X : Scheme.{0}) {I : Type} (U : I → X.Opens)

theorem regularTripleCechCochain_sub
    (v w : ∀ i j l, Γ(X, (U i ⊓ U j) ⊓ U l)) :
    BoundaryShuffle.regularTripleCechCochain X U (fun i j l => v i j l - w i j l) =
      BoundaryShuffle.regularTripleCechCochain X U v - BoundaryShuffle.regularTripleCechCochain X U w := by
  funext a
  change X.presheaf.map _ (v (a 0) (a 1) (a 2) - w (a 0) (a 1) (a 2)) = _
  exact map_sub _ _ _

theorem regularPairPrimitive_of_sheafClass_eq (hU : iSup U = ⊤)
    (v w : ∀ i j, Γ(X, U i ⊓ U j))
    (hv : RegularPair.Closed.RegularPairCocycle X U v) (hw : RegularPair.Closed.RegularPairCocycle X U w)
    (h : RegularPair.Closed.regularPairSheafClass X U hU v hv = RegularPair.Closed.regularPairSheafClass X U hU w hw) :
    ∃ s : ∀ i, Γ(X, U i), RegularPair.Closed.RegularPairPrimitive X U (fun i j => v i j - w i j) s := by
  apply (RegularPair.ClassZeroCriterion.regularPairSheafClass_eq_zero_iff_primitive X U (fun i j => v i j - w i j)
    hU (RegularPair.ClassDifference.regularPairCocycle_sub X U v w hv hw)).mp
  erw [RegularPair.ClassDifference.regularPairSheafClass_sub X U v w hU hv hw, h, sub_self]
  rfl

theorem regularTripleClass_eq_of_differenceBoundary (hU : iSup U = ⊤)
    (v w : ∀ i j l, Γ(X, (U i ⊓ U j) ⊓ U l))
    (hv : DivisorClass.Chern.Abelian.CechCoordinates.abelianCechDelta (Dual.UnitCechClasses.ringAdditiveSheaf X.sheaf).obj U 2 (BoundaryShuffle.regularTripleCechCochain X U v) = 0)
    (hw : DivisorClass.Chern.Abelian.CechCoordinates.abelianCechDelta (Dual.UnitCechClasses.ringAdditiveSheaf X.sheaf).obj U 2 (BoundaryShuffle.regularTripleCechCochain X U w) = 0)
    (p : ∀ i j, Γ(X, U i ⊓ U j))
    (hp : BoundaryShuffle.RegularTripleBoundary X U p (fun i j l => v i j l - w i j l)) :
    DivisorClass.Chern.Abelian.CechClasses.abelianCechSheafClass U (Dual.UnitCechClasses.ringAdditiveSheaf X.sheaf) hU 1 (BoundaryShuffle.regularTripleCechCochain X U v) hv =
      DivisorClass.Chern.Abelian.CechClasses.abelianCechSheafClass U (Dual.UnitCechClasses.ringAdditiveSheaf X.sheaf) hU 1 (BoundaryShuffle.regularTripleCechCochain X U w) hw := by
  apply cechSheafClass_eq_of_sub_boundary U (Dual.UnitCechClasses.ringAdditiveSheaf X.sheaf) hU 1 _ _ hv hw
    (RegularPair.Closed.regularPairCechCochain X U p)
  exact (BoundaryShuffle.regularPairCechCochain_delta X U p _ hp).trans (regularTripleCechCochain_sub X U v w)

theorem regularPairCupSheafClass_left_congr (hU : iSup U = ⊤)
    (v v' w : ∀ i j, Γ(X, U i ⊓ U j))
    (hv : RegularPair.Closed.RegularPairCocycle X U v) (hv' : RegularPair.Closed.RegularPairCocycle X U v') (hw : RegularPair.Closed.RegularPairCocycle X U w)
    (h : RegularPair.Closed.regularPairSheafClass X U hU v hv = RegularPair.Closed.regularPairSheafClass X U hU v' hv') :
    CupCechClass.regularPairCupSheafClass X U hU v w hv hw = CupCechClass.regularPairCupSheafClass X U hU v' w hv' hw := by
  obtain ⟨s, hs⟩ := regularPairPrimitive_of_sheafClass_eq X U hU v v' hv hv' h
  have hp := RegularPair.CupPrimitives.regularPairCup_leftPrimitive X U (fun i j => v i j - v' i j) w s hs hw
  have he : RegularPair.CupSymmetry.regularPairCupTriple X U (fun i j => v i j - v' i j) w =
      fun i j l => RegularPair.CupSymmetry.regularPairCupTriple X U v w i j l - RegularPair.CupSymmetry.regularPairCupTriple X U v' w i j l := by
    funext i j l
    dsimp only [RegularPair.CupSymmetry.regularPairCupTriple]
    rw [map_sub, sub_mul]
  rw [he] at hp
  exact regularTripleClass_eq_of_differenceBoundary X U hU _ _
    (CupCechClass.regularPairCupTriple_cech_closed X U v w hv hw)
    (CupCechClass.regularPairCupTriple_cech_closed X U v' w hv' hw) _ hp

theorem regularPairCupSheafClass_right_congr (hU : iSup U = ⊤)
    (v w w' : ∀ i j, Γ(X, U i ⊓ U j))
    (hv : RegularPair.Closed.RegularPairCocycle X U v) (hw : RegularPair.Closed.RegularPairCocycle X U w) (hw' : RegularPair.Closed.RegularPairCocycle X U w')
    (h : RegularPair.Closed.regularPairSheafClass X U hU w hw = RegularPair.Closed.regularPairSheafClass X U hU w' hw') :
    CupCechClass.regularPairCupSheafClass X U hU v w hv hw = CupCechClass.regularPairCupSheafClass X U hU v w' hv hw' := by
  obtain ⟨s, hs⟩ := regularPairPrimitive_of_sheafClass_eq X U hU w w' hw hw' h
  have hp := RegularPair.CupPrimitives.regularPairCup_rightPrimitive X U v (fun i j => w i j - w' i j) s hv hs
  have he : RegularPair.CupSymmetry.regularPairCupTriple X U v (fun i j => w i j - w' i j) =
      fun i j l => RegularPair.CupSymmetry.regularPairCupTriple X U v w i j l - RegularPair.CupSymmetry.regularPairCupTriple X U v w' i j l := by
    funext i j l
    dsimp only [RegularPair.CupSymmetry.regularPairCupTriple]
    rw [map_sub, mul_sub]
  rw [he] at hp
  exact regularTripleClass_eq_of_differenceBoundary X U hU _ _
    (CupCechClass.regularPairCupTriple_cech_closed X U v w hv hw)
    (CupCechClass.regularPairCupTriple_cech_closed X U v w' hv hw') _ hp

end

/-! The cup defined by the original regular sections is additive in
each native degree-one class. The proofs compare literal Cech cochains. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace

variable (X : Scheme.{0}) {I : Type} (U : I → X.Opens)

local instance cupAdditionH2Group :
    AddCommGroup (CategoryTheory.Sheaf.H (Dual.UnitCechClasses.ringAdditiveSheaf X.sheaf) 2) :=
  Cech.Add.cechClassAddCommGroup (Dual.UnitCechClasses.ringAdditiveSheaf X.sheaf) 2

theorem regularTripleCechCochain_add
    (v w : ∀ i j l, Γ(X, (U i ⊓ U j) ⊓ U l)) :
    BoundaryShuffle.regularTripleCechCochain X U (fun i j l => v i j l + w i j l) =
      BoundaryShuffle.regularTripleCechCochain X U v + BoundaryShuffle.regularTripleCechCochain X U w := by
  funext a
  change X.presheaf.map _ (v (a 0) (a 1) (a 2) + w (a 0) (a 1) (a 2)) = _
  exact map_add _ _ _

theorem regularPairCupTriple_add_left
    (v v' w : ∀ i j, Γ(X, U i ⊓ U j)) :
    RegularPair.CupSymmetry.regularPairCupTriple X U (fun i j => v i j + v' i j) w =
      fun i j l => RegularPair.CupSymmetry.regularPairCupTriple X U v w i j l +
        RegularPair.CupSymmetry.regularPairCupTriple X U v' w i j l := by
  funext i j l
  dsimp only [RegularPair.CupSymmetry.regularPairCupTriple]
  rw [map_add, add_mul]

theorem regularPairCupTriple_add_right
    (v w w' : ∀ i j, Γ(X, U i ⊓ U j)) :
    RegularPair.CupSymmetry.regularPairCupTriple X U v (fun i j => w i j + w' i j) =
      fun i j l => RegularPair.CupSymmetry.regularPairCupTriple X U v w i j l +
        RegularPair.CupSymmetry.regularPairCupTriple X U v w' i j l := by
  funext i j l
  dsimp only [RegularPair.CupSymmetry.regularPairCupTriple]
  rw [map_add, mul_add]

theorem regularPairCupSheafClass_add_left (hU : iSup U = ⊤)
    (v v' w : ∀ i j, Γ(X, U i ⊓ U j))
    (hv : RegularPair.Closed.RegularPairCocycle X U v) (hv' : RegularPair.Closed.RegularPairCocycle X U v')
    (hw : RegularPair.Closed.RegularPairCocycle X U w) :
    CupCechClass.regularPairCupSheafClass X U hU (fun i j => v i j + v' i j) w
      (RegularPair.ClassAddition.regularPairCocycle_add X U v v' hv hv') hw =
      CupCechClass.regularPairCupSheafClass X U hU v w hv hw +
        CupCechClass.regularPairCupSheafClass X U hU v' w hv' hw := by
  let F := Dual.UnitCechClasses.ringAdditiveSheaf X.sheaf
  let a := BoundaryShuffle.regularTripleCechCochain X U (RegularPair.CupSymmetry.regularPairCupTriple X U v w)
  let b := BoundaryShuffle.regularTripleCechCochain X U (RegularPair.CupSymmetry.regularPairCupTriple X U v' w)
  have ha := CupCechClass.regularPairCupTriple_cech_closed X U v w hv hw
  have hb := CupCechClass.regularPairCupTriple_cech_closed X U v' w hv' hw
  have he : BoundaryShuffle.regularTripleCechCochain X U
      (RegularPair.CupSymmetry.regularPairCupTriple X U (fun i j => v i j + v' i j) w) = a + b := by
    rw [regularPairCupTriple_add_left, regularTripleCechCochain_add]
  exact (Cech.Add.cechSheafClass_congr U F hU 1 _ (a + b)
    (CupCechClass.regularPairCupTriple_cech_closed X U _ w (RegularPair.ClassAddition.regularPairCocycle_add X U v v' hv hv') hw)
    (Cech.Add.cechAdd_closed U F.obj 2 a b ha hb) he).trans
      (Cech.Add.cechSheafClass_add U F hU 1 a b ha hb)

theorem regularPairCupSheafClass_add_right (hU : iSup U = ⊤)
    (v w w' : ∀ i j, Γ(X, U i ⊓ U j))
    (hv : RegularPair.Closed.RegularPairCocycle X U v) (hw : RegularPair.Closed.RegularPairCocycle X U w)
    (hw' : RegularPair.Closed.RegularPairCocycle X U w') :
    CupCechClass.regularPairCupSheafClass X U hU v (fun i j => w i j + w' i j)
      hv (RegularPair.ClassAddition.regularPairCocycle_add X U w w' hw hw') =
      CupCechClass.regularPairCupSheafClass X U hU v w hv hw +
        CupCechClass.regularPairCupSheafClass X U hU v w' hv hw' := by
  let F := Dual.UnitCechClasses.ringAdditiveSheaf X.sheaf
  let a := BoundaryShuffle.regularTripleCechCochain X U (RegularPair.CupSymmetry.regularPairCupTriple X U v w)
  let b := BoundaryShuffle.regularTripleCechCochain X U (RegularPair.CupSymmetry.regularPairCupTriple X U v w')
  have ha := CupCechClass.regularPairCupTriple_cech_closed X U v w hv hw
  have hb := CupCechClass.regularPairCupTriple_cech_closed X U v w' hv hw'
  have he : BoundaryShuffle.regularTripleCechCochain X U
      (RegularPair.CupSymmetry.regularPairCupTriple X U v (fun i j => w i j + w' i j)) = a + b := by
    rw [regularPairCupTriple_add_right, regularTripleCechCochain_add]
  exact (Cech.Add.cechSheafClass_congr U F hU 1 _ (a + b)
    (CupCechClass.regularPairCupTriple_cech_closed X U v _ hv (RegularPair.ClassAddition.regularPairCocycle_add X U w w' hw hw'))
    (Cech.Add.cechAdd_closed U F.obj 2 a b ha hb) he).trans
      (Cech.Add.cechSheafClass_add U F hU 1 a b ha hb)

theorem regularPairCupSheafClass_symm_add_zero (hU : iSup U = ⊤)
    (v w : ∀ i j, Γ(X, U i ⊓ U j))
    (hv : RegularPair.Closed.RegularPairCocycle X U v) (hw : RegularPair.Closed.RegularPairCocycle X U w) :
    CupCechClass.regularPairCupSheafClass X U hU v w hv hw +
      CupCechClass.regularPairCupSheafClass X U hU w v hw hv = 0 := by
  let F := Dual.UnitCechClasses.ringAdditiveSheaf X.sheaf
  let a := BoundaryShuffle.regularTripleCechCochain X U (RegularPair.CupSymmetry.regularPairCupTriple X U v w)
  let b := BoundaryShuffle.regularTripleCechCochain X U (RegularPair.CupSymmetry.regularPairCupTriple X U w v)
  have ha := CupCechClass.regularPairCupTriple_cech_closed X U v w hv hw
  have hb := CupCechClass.regularPairCupTriple_cech_closed X U w v hw hv
  have hp := RegularPair.CupSymmetry.regularPairCup_symm_boundary X U v w hv hw
  have H := RegularPair.CupSymmetry.regularPairCup_symm_class_zero X U hU v w hv hw
  have he := regularTripleCechCochain_add X U
    (RegularPair.CupSymmetry.regularPairCupTriple X U v w) (RegularPair.CupSymmetry.regularPairCupTriple X U w v)
  have hc := Cech.Add.cechSheafClass_congr U F hU 1 _ (a + b)
    (BoundaryShuffle.regularTripleCechCochain_closed X U _ _ hp)
    (Cech.Add.cechAdd_closed U F.obj 2 a b ha hb) he
  exact ((Cech.Add.cechSheafClass_add U F hU 1 a b ha hb).symm.trans hc.symm).trans H

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Regular.CupClassAddition
