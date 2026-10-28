import OAI.ArithmeticGeometry.OrdinaryLocus.Openness.OpenCechDegreeZero

/-! # Open Cech Cocycles -/

namespace OAI.ArithmeticGeometry.OrdinaryLocus.Openness.OpenCechCocycles.Construction

noncomputable section

/-! Cech one-cocycles expressed on arbitrary common subopens, for geometric gluing arguments. -/

open _root_.CategoryTheory _root_.TopologicalSpace Opposite

universe u v w

variable {R : Type u} [CommRing R] {X : TopCat.{v}}
    (F : TopCat.Sheaf (ModuleCat.{v} R) X) {ι : Type w} (U : ι → Opens X)

def openCechRestrict1 (z : OpenCechDegreeZero.Construction.openModuleCechC1 F U) (i j : ι) (W : Opens X)
    (hi : W ≤ U i) (hj : W ≤ U j) : F.obj.obj (op W) :=
  F.obj.map (homOfLE (le_inf hi hj)).op (z i j)

def IsOpenCechCocycle (z : OpenCechDegreeZero.Construction.openModuleCechC1 F U) : Prop :=
  ∀ (i j k : ι) (W : Opens X) (hi : W ≤ U i) (hj : W ≤ U j) (hk : W ≤ U k),
    openCechRestrict1 F U z i j W hi hj + openCechRestrict1 F U z j k W hj hk =
      openCechRestrict1 F U z i k W hi hk

theorem openCechRestrict1_self (z : OpenCechDegreeZero.Construction.openModuleCechC1 F U) (i j : ι) :
    openCechRestrict1 F U z i j (U i ⊓ U j) inf_le_left inf_le_right = z i j := by
  change F.obj.map (𝟙 (op (U i ⊓ U j))) (z i j) = _
  rw [F.obj.map_id]
  rfl

theorem openCechRestrict1_comp (z : OpenCechDegreeZero.Construction.openModuleCechC1 F U) (i j : ι)
    (W W' : Opens X) (hi : W ≤ U i) (hj : W ≤ U j) (h : W' ≤ W) :
    F.obj.map (homOfLE h).op (openCechRestrict1 F U z i j W hi hj) =
      openCechRestrict1 F U z i j W' (h.trans hi) (h.trans hj) := by
  change F.obj.map (homOfLE h).op (F.obj.map (homOfLE (le_inf hi hj)).op (z i j)) = _
  rw [← ConcreteCategory.comp_apply, ← F.obj.map_comp]
  rfl

theorem openCechRestrict1_d0 (x : OpenCechDegreeZero.Construction.openModuleCechC0 F U) (i j : ι) (W : Opens X)
    (hi : W ≤ U i) (hj : W ≤ U j) :
    openCechRestrict1 F U (OpenCechDegreeZero.Construction.openModuleCechD0 F U x) i j W hi hj =
      F.obj.map (homOfLE hj).op (x j) - F.obj.map (homOfLE hi).op (x i) := by
  change F.obj.map (homOfLE (le_inf hi hj)).op
    (F.obj.map (homOfLE inf_le_right : U i ⊓ U j ⟶ U j).op (x j) -
      F.obj.map (homOfLE inf_le_left : U i ⊓ U j ⟶ U i).op (x i)) = _
  rw [map_sub, ← ConcreteCategory.comp_apply, ← ConcreteCategory.comp_apply,
    ← F.obj.map_comp, ← F.obj.map_comp]
  rfl

theorem openCechD0_isCocycle (x : OpenCechDegreeZero.Construction.openModuleCechC0 F U) :
    IsOpenCechCocycle F U (OpenCechDegreeZero.Construction.openModuleCechD0 F U x) := by
  intro i j k W hi hj hk
  rw [openCechRestrict1_d0, openCechRestrict1_d0, openCechRestrict1_d0]
  abel

theorem openCechRestrict1_sub (z w : OpenCechDegreeZero.Construction.openModuleCechC1 F U) (i j : ι) (W : Opens X)
    (hi : W ≤ U i) (hj : W ≤ U j) :
    openCechRestrict1 F U (z - w) i j W hi hj =
      openCechRestrict1 F U z i j W hi hj - openCechRestrict1 F U w i j W hi hj := by
  exact map_sub (F.obj.map (homOfLE (le_inf hi hj)).op).hom (z i j) (w i j)

theorem openCechCocycle_sub (z w : OpenCechDegreeZero.Construction.openModuleCechC1 F U)
    (hz : IsOpenCechCocycle F U z) (hw : IsOpenCechCocycle F U w) :
    IsOpenCechCocycle F U (z - w) := by
  intro i j k W hi hj hk
  rw [openCechRestrict1_sub, openCechRestrict1_sub, openCechRestrict1_sub]
  calc
    _ = (openCechRestrict1 F U z i j W hi hj + openCechRestrict1 F U z j k W hj hk) -
      (openCechRestrict1 F U w i j W hi hj + openCechRestrict1 F U w j k W hj hk) := by abel
    _ = _ := congrArg₂ (fun a b ↦ a - b) (hz i j k W hi hj hk) (hw i j k W hi hj hk)

theorem openCechCocycle_diagonal (z : OpenCechDegreeZero.Construction.openModuleCechC1 F U)
    (hz : IsOpenCechCocycle F U z) (i : ι) : z i i = 0 := by
  have h := hz i i i (U i ⊓ U i) inf_le_left inf_le_right inf_le_left
  have hid : openCechRestrict1 F U z i i (U i ⊓ U i) inf_le_left inf_le_right = z i i :=
    openCechRestrict1_self F U z i i
  change openCechRestrict1 F U z i i (U i ⊓ U i) inf_le_left inf_le_right +
    openCechRestrict1 F U z i i (U i ⊓ U i) inf_le_left inf_le_right =
      openCechRestrict1 F U z i i (U i ⊓ U i) inf_le_left inf_le_right at h
  rw [hid] at h
  exact add_eq_left.mp h

theorem openCechCocycle_square (z : OpenCechDegreeZero.Construction.openModuleCechC1 F U) (hz : IsOpenCechCocycle F U z)
    (p q r s : ι) (W : Opens X) (hp : W ≤ U p) (hq : W ≤ U q)
    (hr : W ≤ U r) (hs : W ≤ U s) :
    openCechRestrict1 F U z s q W hs hq - openCechRestrict1 F U z p r W hp hr =
      openCechRestrict1 F U z r q W hr hq - openCechRestrict1 F U z p s W hp hs := by
  apply sub_eq_sub_iff_add_eq_add.mpr
  exact (add_comm _ _).trans
    (((hz p s q W hp hs hq).trans (hz p r q W hp hr hq).symm).trans (add_comm _ _))

end

end OAI.ArithmeticGeometry.OrdinaryLocus.Openness.OpenCechCocycles.Construction
