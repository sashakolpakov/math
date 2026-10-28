import OAI.AlgebraicGeometry.DivisorClass.Chern.Regular.LineSections
import OAI.AlgebraicGeometry.DivisorClass.Chern.Regular.FunctionGluing

/-! # Line Gluing -/

namespace OAI.AlgebraicGeometry.DivisorClass.Chern.Regular.LineGluing

noncomputable section

section

/-! Native structure-sheaf gluing constructs each regular bundle coordinate. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace Opposite
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

variable {X : Scheme} {ι : Type} {κ : Type*} (D : FunctionGluing.RegularLineCocycle X ι)
variable (U : κ → X.Opens) (s : ∀ a, LineSections.RegularLineSection D (U a))
variable (hc : ∀ a b, LineSections.regularLineSectionRestrict D inf_le_left (s a) =
  LineSections.regularLineSectionRestrict D inf_le_right (s b))

include hc in
theorem regularLineSectionCompatible_value (a b : κ) (i : ι) (W : X.Opens)
    (hWa : W ≤ U a) (hWb : W ≤ U b) (hWi : W ≤ D.domain i) :
    (s a).val i ⟨W, hWa, hWi⟩ = (s b).val i ⟨W, hWb, hWi⟩ := by
  exact congrArg (fun t : LineSections.RegularLineSection D (U a ⊓ U b) =>
    t.val i ⟨W, le_inf hWa hWb, hWi⟩) (hc a b)

include hc in
theorem exists_regularLineCoordinate_glue (i : ι) (W : X.Opens)
    (hWU : W ≤ iSup U) (hWi : W ≤ D.domain i) :
    ∃ g : Γ(X, W), ∀ a, FunctionGluing.regularRestriction inf_le_left g =
      (s a).val i ⟨W ⊓ U a, inf_le_right, inf_le_left.trans hWi⟩ := by
  apply FunctionGluing.exists_regularFunction_glue (fun a => W ⊓ U a) W (fun _ => inf_le_left)
  · rw [← inf_iSup_eq, inf_eq_left.mpr hWU]
  · intro a b
    change FunctionGluing.regularRestriction inf_le_left ((s a).val i ⟨W ⊓ U a, inf_le_right, inf_le_left.trans hWi⟩) =
      FunctionGluing.regularRestriction inf_le_right ((s b).val i ⟨W ⊓ U b, inf_le_right, inf_le_left.trans hWi⟩)
    rw [(s a).property.1 i (W ⊓ U a) ((W ⊓ U a) ⊓ (W ⊓ U b))
      inf_le_right (inf_le_left.trans hWi) inf_le_left,
      (s b).property.1 i (W ⊓ U b) ((W ⊓ U a) ⊓ (W ⊓ U b))
      inf_le_right (inf_le_left.trans hWi) inf_le_right]
    exact regularLineSectionCompatible_value D U s hc a b i _
      (inf_le_left.trans inf_le_right) (inf_le_right.trans inf_le_right)
      (inf_le_left.trans (inf_le_left.trans hWi))

def regularLineGluedCoordinate (i : ι) (W : X.Opens)
    (hWU : W ≤ iSup U) (hWi : W ≤ D.domain i) : Γ(X, W) :=
  (exists_regularLineCoordinate_glue D U s hc i W hWU hWi).choose

theorem regularLineGluedCoordinate_restrict (i : ι) (W : X.Opens)
    (hWU : W ≤ iSup U) (hWi : W ≤ D.domain i) (a : κ) :
    FunctionGluing.regularRestriction inf_le_left (regularLineGluedCoordinate D U s hc i W hWU hWi) =
      (s a).val i ⟨W ⊓ U a, inf_le_right, inf_le_left.trans hWi⟩ :=
  (exists_regularLineCoordinate_glue D U s hc i W hWU hWi).choose_spec a

end

section

/-! Glued regular coordinates respect native restriction and transition functions. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace Opposite
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

variable {X : Scheme} {ι : Type} {κ : Type*} (D : FunctionGluing.RegularLineCocycle X ι)
variable (U : κ → X.Opens) (s : ∀ a, LineSections.RegularLineSection D (U a))
variable (hc : ∀ a b, LineSections.regularLineSectionRestrict D inf_le_left (s a) =
  LineSections.regularLineSectionRestrict D inf_le_right (s b))

theorem regularLineGluedCoordinate_naturality (i : ι) (W V : X.Opens)
    (hWU : W ≤ iSup U) (hWi : W ≤ D.domain i) (hVW : V ≤ W) :
    FunctionGluing.regularRestriction hVW (regularLineGluedCoordinate D U s hc i W hWU hWi) =
      regularLineGluedCoordinate D U s hc i V (hVW.trans hWU) (hVW.trans hWi) := by
  apply FunctionGluing.regularFunction_eq_of_restrictions (fun a => V ⊓ U a) V (fun _ => inf_le_left)
  · rw [← inf_iSup_eq, inf_eq_left.mpr (hVW.trans hWU)]
  · intro a
    have hr : FunctionGluing.regularRestriction inf_le_left
        (FunctionGluing.regularRestriction hVW (regularLineGluedCoordinate D U s hc i W hWU hWi)) =
        FunctionGluing.regularRestriction (inf_le_inf_right (U a) hVW)
          (FunctionGluing.regularRestriction inf_le_left (regularLineGluedCoordinate D U s hc i W hWU hWi)) := by
      simp only [FunctionGluing.regularRestriction_comp]
    rw [hr, regularLineGluedCoordinate_restrict,
      (s a).property.1 i (W ⊓ U a) (V ⊓ U a) inf_le_right (inf_le_left.trans hWi)
        (inf_le_inf_right (U a) hVW), regularLineGluedCoordinate_restrict]

theorem regularLineGluedCoordinate_transition (i j : ι) (W : X.Opens)
    (hWU : W ≤ iSup U) (hWi : W ≤ D.domain i) (hWj : W ≤ D.domain j) :
    regularLineGluedCoordinate D U s hc j W hWU hWj =
      (D.transition i j W hWi hWj : Γ(X, W)) *
        regularLineGluedCoordinate D U s hc i W hWU hWi := by
  apply FunctionGluing.regularFunction_eq_of_restrictions (fun a => W ⊓ U a) W (fun _ => inf_le_left)
  · rw [← inf_iSup_eq, inf_eq_left.mpr hWU]
  · intro a
    rw [map_mul, D.restrict, regularLineGluedCoordinate_restrict,
      regularLineGluedCoordinate_restrict]
    exact (s a).property.2 i j (W ⊓ U a) inf_le_right
      (inf_le_left.trans hWi) (inf_le_left.trans hWj)

theorem regularLineGluedCoordinate_on_subopen (a : κ) (i : ι) (W : X.Opens)
    (hWa : W ≤ U a) (hWi : W ≤ D.domain i) :
    regularLineGluedCoordinate D U s hc i W (hWa.trans (le_iSup U a)) hWi =
      (s a).val i ⟨W, hWa, hWi⟩ := by
  have h := congrArg (FunctionGluing.regularRestriction (le_inf le_rfl hWa))
    (regularLineGluedCoordinate_restrict D U s hc i W (hWa.trans (le_iSup U a)) hWi a)
  rw [FunctionGluing.regularRestriction_comp, FunctionGluing.regularRestriction_self,
    (s a).property.1 i (W ⊓ U a) W inf_le_right (inf_le_left.trans hWi)
      (le_inf le_rfl hWa)] at h
  exact h

end

/-! Compatible regular-coordinate sections form a genuine sheaf of additive groups. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace Opposite
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

variable {X : Scheme} {ι : Type} (D : FunctionGluing.RegularLineCocycle X ι)

theorem exists_regularLineSection_glue {κ : Type*} (U : κ → X.Opens)
    (s : ∀ a, LineSections.RegularLineSection D (U a))
    (hc : ∀ a b, LineSections.regularLineSectionRestrict D inf_le_left (s a) =
      LineSections.regularLineSectionRestrict D inf_le_right (s b)) :
    ∃ g : LineSections.RegularLineSection D (iSup U),
      ∀ a, LineSections.regularLineSectionRestrict D (le_iSup U a) g = s a := by
  let g : LineSections.RegularLineSection D (iSup U) :=
    ⟨fun i W => regularLineGluedCoordinate D U s hc i W.val W.property.1 W.property.2,
      ⟨regularLineGluedCoordinate_naturality D U s hc,
        regularLineGluedCoordinate_transition D U s hc⟩⟩
  refine ⟨g, ?_⟩
  intro a
  apply LineSections.regularLineSection_ext
  intro i W hWa hWi
  exact regularLineGluedCoordinate_on_subopen D U s hc a i W hWa hWi

theorem regularLineSection_eq_of_restrictions {κ : Type*} (U : κ → X.Opens)
    (s t : LineSections.RegularLineSection D (iSup U))
    (h : ∀ a, LineSections.regularLineSectionRestrict D (le_iSup U a) s =
      LineSections.regularLineSectionRestrict D (le_iSup U a) t) : s = t := by
  apply LineSections.regularLineSection_ext
  intro i W hWU hWi
  apply FunctionGluing.regularFunction_eq_of_restrictions (fun a => W ⊓ U a) W (fun _ => inf_le_left)
  · rw [← inf_iSup_eq, inf_eq_left.mpr hWU]
  · intro a
    rw [s.property.1 i W (W ⊓ U a) hWU hWi inf_le_left,
      t.property.1 i W (W ⊓ U a) hWU hWi inf_le_left]
    exact congrArg (fun q : LineSections.RegularLineSection D (U a) =>
      q.val i ⟨W ⊓ U a, inf_le_right, inf_le_left.trans hWi⟩) (h a)

def regularLineSectionPresheaf : TopCat.Presheaf AddCommGrpCat X where
  obj U := AddCommGrpCat.of (LineSections.RegularLineSection D U.unop)
  map f := AddCommGrpCat.ofHom (LineSections.regularLineSectionRestrict D (leOfHom f.unop))
  map_id U := by
    ext s
    rfl
  map_comp f g := by
    ext s
    rfl

theorem regularLineSectionPresheaf_isSheaf : (regularLineSectionPresheaf D).IsSheaf := by
  apply (TopCat.Presheaf.isSheaf_iff_isSheafUniqueGluing (regularLineSectionPresheaf D)).mpr
  intro κ U s hc
  obtain ⟨g, hg⟩ := exists_regularLineSection_glue D U s hc
  refine ⟨g, hg, ?_⟩
  intro t ht
  exact regularLineSection_eq_of_restrictions D U t g (fun a => (ht a).trans (hg a).symm)

def regularLineSectionSheaf : TopCat.Sheaf AddCommGrpCat X where
  obj := regularLineSectionPresheaf D
  property := regularLineSectionPresheaf_isSheaf D

end

end OAI.AlgebraicGeometry.DivisorClass.Chern.Regular.LineGluing
