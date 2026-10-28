import OAI.AlgebraicGeometry.Comparison.Betti.Sheaf.ModulePushforwardStalk
import Mathlib.Algebra.Category.Grp.Zero

/-! # Module Pushforward Zero -/

namespace OAI.AlgebraicGeometry.Comparison.Betti.Closed.ModulePushforwardZero.Local

noncomputable section

/-! A native module direct-image stalk vanishes outside a closed image. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.TopologicalSpace Opposite

variable {X Y : TopCat.{0}} (f : X ⟶ Y)
  {R : Sheaf (Opens.grothendieckTopology X) RingCat.{0}}
  {S : Sheaf (Opens.grothendieckTopology Y) RingCat.{0}}
  [(Opens.map f).IsContinuous (Opens.grothendieckTopology Y) (Opens.grothendieckTopology X)]
  (φ : S ⟶ ((Opens.map f).sheafPushforwardContinuous RingCat
    (Opens.grothendieckTopology Y) (Opens.grothendieckTopology X)).obj R)

theorem closedModulePushforwardStalkZero (hclosed : IsClosed (Set.range f))
    (M : SheafOfModules.{0} R) (y : Y) (hy : y ∉ Set.range f) :
    IsZero ((StalkPointModuleAdjunction.Local.sheafRingModuleStalk S y).obj ((SheafOfModules.pushforward φ).obj M)) := by
  let P : TopCat.Presheaf AddCommGrpCat Y :=
    ((SheafOfModules.pushforward φ).obj M).val.presheaf
  let F : TopCat.Sheaf AddCommGrpCat X := (SheafOfModules.toSheaf R).obj M
  let U : Opens Y := ⟨(Set.range f)ᶜ, hclosed.isOpen_compl⟩
  have hzero : IsZero (P.stalk y) := by
    rw [IsZero.iff_id_eq_zero]
    apply P.stalk_hom_ext
    intro V hyV
    simp only [Category.comp_id, comp_zero]
    have hempty : (Opens.map f).obj (V ⊓ U) = ⊥ := by
      ext x
      constructor
      · intro hx
        change f x ∈ V ∧ f x ∉ Set.range f at hx
        exact (hx.2 ⟨x, rfl⟩).elim
      · intro hx
        exact hx.elim
    have hz : IsZero (P.obj (op (V ⊓ U))) := (F.isTerminalOfEqEmpty hempty).isZero
    have hw : P.germ (V ⊓ U) y ⟨hyV, hy⟩ = 0 := hz.eq_of_src _ _
    have hr := P.germ_res (homOfLE inf_le_left : V ⊓ U ⟶ V) y ⟨hyV, hy⟩
    exact hr.symm.trans (by rw [hw, comp_zero])
  apply ModuleCat.isZero_iff_subsingleton.mpr
  exact AddCommGrpCat.isZero_iff_subsingleton.mp hzero

end

end OAI.AlgebraicGeometry.Comparison.Betti.Closed.ModulePushforwardZero.Local
