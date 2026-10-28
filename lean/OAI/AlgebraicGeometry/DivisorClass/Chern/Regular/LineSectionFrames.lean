import OAI.AlgebraicGeometry.DivisorClass.Chern.Regular.LineSectionModules

/-! # Line Section Frames -/

namespace OAI.AlgebraicGeometry.DivisorClass.Chern.Regular.LineSectionFrames

noncomputable section

/-! Explicit native regular frames for the cocycle section modules. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace Opposite
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

variable {X : Scheme} {ι : Type} (D : FunctionGluing.RegularLineCocycle X ι)
variable {U : X.Opens} (i : ι) (hUi : U ≤ D.domain i)

def regularLineSectionOfFrame (r : Γ(X, U)) : LineSections.RegularLineSection D U :=
  ⟨fun j W => (D.transition i j W.val (W.property.1.trans hUi) W.property.2 : Γ(X, W.val)) *
    FunctionGluing.regularRestriction W.property.1 r, by
    constructor
    · intro j W V hWU hWj hVW
      change FunctionGluing.regularRestriction hVW ((D.transition i j W _ _ : Γ(X, W)) *
        FunctionGluing.regularRestriction hWU r) = _
      rw [map_mul, D.restrict, FunctionGluing.regularRestriction_comp]
    · intro j k W hWU hWj hWk
      change (D.transition i k W _ _ : Γ(X, W)) * FunctionGluing.regularRestriction hWU r = _
      have hc := congrArg (fun t : Γ(X, W)ˣ => (t : Γ(X, W)))
        (D.cocycle i j k W (hWU.trans hUi) hWj hWk)
      change (D.transition i j W _ _ : Γ(X, W)) * (D.transition j k W _ _ : Γ(X, W)) = _ at hc
      change (D.transition i k W (hWU.trans hUi) hWk : Γ(X, W)) * FunctionGluing.regularRestriction hWU r =
        (D.transition j k W hWj hWk : Γ(X, W)) *
          ((D.transition i j W (hWU.trans hUi) hWj : Γ(X, W)) * FunctionGluing.regularRestriction hWU r)
      rw [← hc, mul_assoc]
      exact mul_left_comm _ _ _⟩

def regularLineSectionFrameValue (s : LineSections.RegularLineSection D U) : Γ(X, U) :=
  s.val i ⟨U, le_rfl, hUi⟩

@[simp] theorem regularLineSectionFrameValue_ofFrame (r : Γ(X, U)) :
    regularLineSectionFrameValue D i hUi (regularLineSectionOfFrame D i hUi r) = r := by
  change (D.transition i i U hUi hUi : Γ(X, U)) * FunctionGluing.regularRestriction le_rfl r = r
  rw [D.refl, Units.val_one, FunctionGluing.regularRestriction_self, one_mul]

@[simp] theorem regularLineSectionOfFrame_frameValue (s : LineSections.RegularLineSection D U) :
    regularLineSectionOfFrame D i hUi (regularLineSectionFrameValue D i hUi s) = s := by
  apply LineSections.regularLineSection_ext
  intro j W hWU hWj
  change (D.transition i j W _ _ : Γ(X, W)) *
    FunctionGluing.regularRestriction hWU (s.val i ⟨U, le_rfl, hUi⟩) = _
  rw [s.property.1 i U W le_rfl hUi hWU]
  exact (s.property.2 i j W hWU (hWU.trans hUi) hWj).symm

def regularLineSectionLinearFrame : LineSections.RegularLineSection D U ≃ₗ[Γ(X, U)] Γ(X, U) where
  toFun := regularLineSectionFrameValue D i hUi
  invFun := regularLineSectionOfFrame D i hUi
  left_inv := regularLineSectionOfFrame_frameValue D i hUi
  right_inv := regularLineSectionFrameValue_ofFrame D i hUi
  map_add' _ _ := rfl
  map_smul' r s := by
    change FunctionGluing.regularRestriction le_rfl r * s.val i ⟨U, le_rfl, hUi⟩ = _
    rw [FunctionGluing.regularRestriction_self]
    rfl

theorem regularLineSectionFrameValue_restrict {V : X.Opens} (hVU : V ≤ U)
    (s : LineSections.RegularLineSection D U) :
    regularLineSectionFrameValue D i (hVU.trans hUi) (LineSections.regularLineSectionRestrict D hVU s) =
      FunctionGluing.regularRestriction hVU (regularLineSectionFrameValue D i hUi s) :=
  (s.property.1 i U V le_rfl hUi hVU).symm

end

end OAI.AlgebraicGeometry.DivisorClass.Chern.Regular.LineSectionFrames
