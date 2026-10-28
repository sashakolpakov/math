import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.RegularPair.ClassAddition
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.RegularPair.ClassZeroCriterion

/-! # Class Difference -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.RegularPair.ClassDifference

noncomputable section

/-! Original regular pair cocycles with a literal local defect
coboundary define the same native degree-one sheaf class. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace

variable (X : Scheme.{0}) {I : Type} (U : I → X.Opens)
    (v w : ∀ i j : I, Γ(X, U i ⊓ U j))

theorem regularPairCocycle_sub (hv : Closed.RegularPairCocycle X U v) (hw : Closed.RegularPairCocycle X U w) :
    Closed.RegularPairCocycle X U (fun i j => v i j - w i j) := by
  intro i j l
  simp only [map_sub]
  have H := congrArg₂ (· - ·) (hv i j l) (hw i j l)
  convert H using 1
  abel

theorem regularPairCechCochain_sub :
    Closed.regularPairCechCochain X U (fun i j => v i j - w i j) =
      Closed.regularPairCechCochain X U v - Closed.regularPairCechCochain X U w := by
  funext a
  exact map_sub (X.presheaf.map (homOfLE
    (le_inf (AlgebraicTopology.DeRham.Comparison.SmoothCech.cechIntersection_le U a 0)
      (AlgebraicTopology.DeRham.Comparison.SmoothCech.cechIntersection_le U a 1))).op).hom _ _

local instance regularPairClassDifference_group : AddCommGroup (CategoryTheory.Sheaf.H (Dual.UnitCechClasses.ringAdditiveSheaf X.sheaf) 1) :=
  inferInstanceAs (AddCommGroup ((CategoryTheory.Sheaf.functorH
    (Opens.grothendieckTopology X.toPresheafedSpace.carrier) 1).obj (Dual.UnitCechClasses.ringAdditiveSheaf X.sheaf)))

theorem regularPairSheafClass_sub (hU : iSup U = ⊤)
    (hv : Closed.RegularPairCocycle X U v) (hw : Closed.RegularPairCocycle X U w) :
    Closed.regularPairSheafClass X U hU (fun i j => v i j - w i j) (regularPairCocycle_sub X U v w hv hw) =
      Closed.regularPairSheafClass X U hU v hv - Closed.regularPairSheafClass X U hU w hw := by
  let F := Dual.UnitCechClasses.ringAdditiveSheaf X.sheaf
  let a := Closed.regularPairCechCochain X U v
  let b := Closed.regularPairCechCochain X U w
  have ha := Closed.regularPairCechCochain_closed X U v hv
  have hb := Closed.regularPairCechCochain_closed X U w hw
  exact (Cech.Add.cechSheafClass_congr U F hU 0 _ (a - b)
    (Closed.regularPairCechCochain_closed X U _ (regularPairCocycle_sub X U v w hv hw))
    (Cech.Add.cechSub_closed U F.obj 1 a b ha hb) (regularPairCechCochain_sub X U v w)).trans
      (Cech.Add.cechSheafClass_sub U F hU 0 a b ha hb)

theorem regularPairSheafClass_eq_of_localDefects (hU : iSup U = ⊤)
    (hv : Closed.RegularPairCocycle X U v) (hw : Closed.RegularPairCocycle X U w)
    (s : ∀ i, Γ(X, U i))
    (hs : ∀ i j, v i j - w i j =
      X.presheaf.map (homOfLE (show U i ⊓ U j ≤ U j from inf_le_right)).op (s j) -
        X.presheaf.map (homOfLE (show U i ⊓ U j ≤ U i from inf_le_left)).op (s i)) :
    Closed.regularPairSheafClass X U hU v hv = Closed.regularPairSheafClass X U hU w hw := by
  have hp : Closed.RegularPairPrimitive X U (fun i j => v i j - w i j) (fun i => -s i) := by
    intro i j
    rw [map_neg, map_neg]
    exact (hs i j).trans (by abel)
  have hz := (ClassZeroCriterion.regularPairSheafClass_eq_zero_iff_primitive X U (fun i j => v i j - w i j)
    hU (regularPairCocycle_sub X U v w hv hw)).mpr ⟨fun i => -s i, hp⟩
  exact sub_eq_zero.mp ((regularPairSheafClass_sub X U v w hU hv hw).symm.trans hz)

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.RegularPair.ClassDifference
