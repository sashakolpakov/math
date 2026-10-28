import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.RegularPair.Closed
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Cech.Add

/-! # Class Addition -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.RegularPair.ClassAddition

noncomputable section

/-! Addition of original regular pair cocycles gives addition of
their native degree-one sheaf cohomology classes. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace

variable (X : Scheme.{0}) {I : Type} (U : I → X.Opens)
    (v w : ∀ i j : I, Γ(X, U i ⊓ U j))

theorem regularPairCocycle_add (hv : Closed.RegularPairCocycle X U v) (hw : Closed.RegularPairCocycle X U w) :
    Closed.RegularPairCocycle X U (fun i j => v i j + w i j) := by
  intro i j l
  simp only [map_add]
  have h := congrArg₂ (· + ·) (hv i j l) (hw i j l)
  convert h using 1
  abel

theorem regularPairCechCochain_add :
    Closed.regularPairCechCochain X U (fun i j => v i j + w i j) =
      Closed.regularPairCechCochain X U v + Closed.regularPairCechCochain X U w := by
  funext a
  exact map_add (X.presheaf.map (homOfLE
    (le_inf (AlgebraicTopology.DeRham.Comparison.SmoothCech.cechIntersection_le U a 0)
      (AlgebraicTopology.DeRham.Comparison.SmoothCech.cechIntersection_le U a 1))).op).hom _ _

local instance regularPairClassAdd_group : AddCommGroup (CategoryTheory.Sheaf.H (Dual.UnitCechClasses.ringAdditiveSheaf X.sheaf) 1) :=
  inferInstanceAs (AddCommGroup ((CategoryTheory.Sheaf.functorH
    (Opens.grothendieckTopology X.toPresheafedSpace.carrier) 1).obj (Dual.UnitCechClasses.ringAdditiveSheaf X.sheaf)))

theorem regularPairSheafClass_congr (hU : iSup U = ⊤)
    (hv : Closed.RegularPairCocycle X U v) (hw : Closed.RegularPairCocycle X U w) (h : v = w) :
    Closed.regularPairSheafClass X U hU v hv = Closed.regularPairSheafClass X U hU w hw := by
  subst w
  rfl

theorem regularPairSheafClass_add (hU : iSup U = ⊤)
    (hv : Closed.RegularPairCocycle X U v) (hw : Closed.RegularPairCocycle X U w) :
    Closed.regularPairSheafClass X U hU (fun i j => v i j + w i j) (regularPairCocycle_add X U v w hv hw) =
      Closed.regularPairSheafClass X U hU v hv + Closed.regularPairSheafClass X U hU w hw := by
  let F := Dual.UnitCechClasses.ringAdditiveSheaf X.sheaf
  let a := Closed.regularPairCechCochain X U v
  let b := Closed.regularPairCechCochain X U w
  have ha := Closed.regularPairCechCochain_closed X U v hv
  have hb := Closed.regularPairCechCochain_closed X U w hw
  exact (Cech.Add.cechSheafClass_congr U F hU 0 _ (a + b)
    (Closed.regularPairCechCochain_closed X U _ (regularPairCocycle_add X U v w hv hw))
    (Cech.Add.cechAdd_closed U F.obj 1 a b ha hb) (regularPairCechCochain_add X U v w)).trans
      (Cech.Add.cechSheafClass_add U F hU 0 a b ha hb)

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.RegularPair.ClassAddition
