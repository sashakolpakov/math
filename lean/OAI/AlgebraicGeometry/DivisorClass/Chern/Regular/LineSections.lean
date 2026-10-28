import OAI.AlgebraicGeometry.DivisorClass.Chern.Regular.FunctionGluing

/-! # Line Sections -/

namespace OAI.AlgebraicGeometry.DivisorClass.Chern.Regular.LineSections

noncomputable section

/-! Compatible regular coordinates on every subopen form actual additive section groups. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace Opposite
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

variable {X : Scheme} {ι : Type} (D : FunctionGluing.RegularLineCocycle X ι)

abbrev regularLineLocalSections (U : X.Opens) :=
  ∀ (i : ι) (W : {W : X.Opens // W ≤ U ∧ W ≤ D.domain i}), Γ(X, W.val)

def regularLineSectionAddSubgroup (U : X.Opens) :
    AddSubgroup (regularLineLocalSections D U) where
  carrier := {s | (∀ (i : ι) (W V : X.Opens) (hWU : W ≤ U)
    (hWi : W ≤ D.domain i) (hVW : V ≤ W),
    FunctionGluing.regularRestriction hVW (s i ⟨W, hWU, hWi⟩) = s i ⟨V, hVW.trans hWU, hVW.trans hWi⟩) ∧
    (∀ (i j : ι) (W : X.Opens) (hWU : W ≤ U)
    (hWi : W ≤ D.domain i) (hWj : W ≤ D.domain j),
    s j ⟨W, hWU, hWj⟩ = (D.transition i j W hWi hWj : Γ(X, W)) * s i ⟨W, hWU, hWi⟩)}
  zero_mem' := by
    constructor
    · intro i W V hWU hWi hVW
      exact map_zero _
    · intro i j W hWU hWi hWj
      exact (mul_zero _).symm
  add_mem' := by
    intro s t hs ht
    constructor
    · intro i W V hWU hWi hVW
      change FunctionGluing.regularRestriction hVW (s i ⟨W, hWU, hWi⟩ + t i ⟨W, hWU, hWi⟩) = _
      rw [map_add, hs.1 i W V hWU hWi hVW, ht.1 i W V hWU hWi hVW]
      rfl
    · intro i j W hWU hWi hWj
      change s j ⟨W, hWU, hWj⟩ + t j ⟨W, hWU, hWj⟩ = _
      rw [hs.2 i j W hWU hWi hWj, ht.2 i j W hWU hWi hWj]
      exact (mul_add _ _ _).symm
  neg_mem' := by
    intro s hs
    constructor
    · intro i W V hWU hWi hVW
      change FunctionGluing.regularRestriction hVW (-s i ⟨W, hWU, hWi⟩) = _
      rw [map_neg, hs.1 i W V hWU hWi hVW]
      rfl
    · intro i j W hWU hWi hWj
      change -s j ⟨W, hWU, hWj⟩ = _
      rw [hs.2 i j W hWU hWi hWj]
      exact (mul_neg _ _).symm

abbrev RegularLineSection (U : X.Opens) := ↥(regularLineSectionAddSubgroup D U)

@[ext] theorem regularLineSection_ext {U : X.Opens} {s t : RegularLineSection D U}
    (h : ∀ i W hWU hWi, s.val i ⟨W, hWU, hWi⟩ = t.val i ⟨W, hWU, hWi⟩) : s = t := by
  apply Subtype.ext
  funext i ⟨W, hWU, hWi⟩
  exact h i W hWU hWi

def regularLineSectionRestrict {U V : X.Opens} (hVU : V ≤ U) :
    RegularLineSection D U →+ RegularLineSection D V where
  toFun s := ⟨fun i W => s.val i ⟨W.val, W.property.1.trans hVU, W.property.2⟩, by
    constructor
    · intro i W A hWV hWi hAW
      exact s.property.1 i W A (hWV.trans hVU) hWi hAW
    · intro i j W hWV hWi hWj
      exact s.property.2 i j W (hWV.trans hVU) hWi hWj⟩
  map_zero' := rfl
  map_add' _ _ := rfl

@[simp] theorem regularLineSectionRestrict_self {U : X.Opens} (s : RegularLineSection D U) :
    regularLineSectionRestrict D (le_refl U) s = s := rfl

@[simp] theorem regularLineSectionRestrict_comp {U V W : X.Opens}
    (hVU : V ≤ U) (hWV : W ≤ V) (s : RegularLineSection D U) :
    regularLineSectionRestrict D hWV (regularLineSectionRestrict D hVU s) =
      regularLineSectionRestrict D (hWV.trans hVU) s := rfl

end

end OAI.AlgebraicGeometry.DivisorClass.Chern.Regular.LineSections
