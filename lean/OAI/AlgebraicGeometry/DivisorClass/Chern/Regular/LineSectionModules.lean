import OAI.AlgebraicGeometry.DivisorClass.Chern.Regular.LineSections

/-! # Line Section Modules -/

namespace OAI.AlgebraicGeometry.DivisorClass.Chern.Regular.LineSectionModules

noncomputable section

/-! Actual regular-coordinate sections are modules over the original structure sheaf. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace Opposite
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

variable {X : Scheme} {ι : Type} (D : FunctionGluing.RegularLineCocycle X ι)

instance regularLineSection_smul (U : X.Opens) : SMul Γ(X, U) (LineSections.RegularLineSection D U) where
  smul r s := ⟨fun i W => FunctionGluing.regularRestriction W.property.1 r * s.val i W, by
    constructor
    · intro i W V hWU hWi hVW
      change FunctionGluing.regularRestriction hVW (FunctionGluing.regularRestriction hWU r * s.val i ⟨W, hWU, hWi⟩) = _
      rw [map_mul, FunctionGluing.regularRestriction_comp, s.property.1 i W V hWU hWi hVW]
    · intro i j W hWU hWi hWj
      change FunctionGluing.regularRestriction hWU r * s.val j ⟨W, hWU, hWj⟩ = _
      rw [s.property.2 i j W hWU hWi hWj]
      exact mul_left_comm _ _ _⟩

@[simp] theorem regularLineSection_smul_apply {U : X.Opens} (r : Γ(X, U))
    (s : LineSections.RegularLineSection D U) (i : ι) (W : X.Opens) (hWU : W ≤ U) (hWi : W ≤ D.domain i) :
    (r • s).val i ⟨W, hWU, hWi⟩ = FunctionGluing.regularRestriction hWU r * s.val i ⟨W, hWU, hWi⟩ := rfl

instance regularLineSection_module (U : X.Opens) : Module Γ(X, U) (LineSections.RegularLineSection D U) where
  one_smul s := by
    apply LineSections.regularLineSection_ext
    intro i W hWU hWi
    change FunctionGluing.regularRestriction hWU 1 * s.val i ⟨W, hWU, hWi⟩ = _
    rw [map_one, one_mul]
  mul_smul r q s := by
    apply LineSections.regularLineSection_ext
    intro i W hWU hWi
    change FunctionGluing.regularRestriction hWU (r * q) * s.val i ⟨W, hWU, hWi⟩ = _
    rw [map_mul, mul_assoc]
    rfl
  smul_zero r := by
    apply LineSections.regularLineSection_ext
    intro i W hWU hWi
    exact mul_zero _
  smul_add r s t := by
    apply LineSections.regularLineSection_ext
    intro i W hWU hWi
    exact mul_add _ _ _
  add_smul r q s := by
    apply LineSections.regularLineSection_ext
    intro i W hWU hWi
    change FunctionGluing.regularRestriction hWU (r + q) * s.val i ⟨W, hWU, hWi⟩ = _
    rw [map_add, add_mul]
    rfl
  zero_smul s := by
    apply LineSections.regularLineSection_ext
    intro i W hWU hWi
    change FunctionGluing.regularRestriction hWU 0 * s.val i ⟨W, hWU, hWi⟩ = _
    rw [map_zero, zero_mul]
    rfl

theorem regularLineSectionRestrict_smul {U V : X.Opens} (hVU : V ≤ U)
    (r : Γ(X, U)) (s : LineSections.RegularLineSection D U) :
    LineSections.regularLineSectionRestrict D hVU (r • s) =
      FunctionGluing.regularRestriction hVU r • LineSections.regularLineSectionRestrict D hVU s := by
  apply LineSections.regularLineSection_ext
  intro i W hWV hWi
  change FunctionGluing.regularRestriction (hWV.trans hVU) r * s.val i ⟨W, hWV.trans hVU, hWi⟩ =
    FunctionGluing.regularRestriction hWV (FunctionGluing.regularRestriction hVU r) * s.val i ⟨W, hWV.trans hVU, hWi⟩
  rw [FunctionGluing.regularRestriction_comp]

end

end OAI.AlgebraicGeometry.DivisorClass.Chern.Regular.LineSectionModules
