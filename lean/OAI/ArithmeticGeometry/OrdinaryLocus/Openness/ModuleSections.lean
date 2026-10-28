import OAI.ArithmeticGeometry.OrdinaryLocus.Openness.LineBundle

/-! # Module Sections -/

namespace OAI.ArithmeticGeometry.OrdinaryLocus.Openness.ModuleSections.Construction

noncomputable section

/-! Global sections and endomorphisms of the structure sheaf. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

/-- Compatible sections over all opens are determined by the section over the whole scheme. -/
def moduleSectionsEquivGlobal {X : Scheme.{u}} (M : X.Modules) :
    M.sections ≃ Γ(M, ⊤) where
  toFun s := s.val (.op ⊤)
  invFun s := PresheafOfModules.sectionsMk
    (fun U ↦ M.val.map (homOfLE (show U.unop ≤ ⊤ from le_top)).op s)
    (by
      intro U V f
      change M.presheaf.map f
        (M.presheaf.map (homOfLE (show U.unop ≤ ⊤ from le_top)).op s) = _
      rw [← ConcreteCategory.comp_apply, ← Functor.map_comp]
      rfl)
  left_inv s := by
    apply PresheafOfModules.sections_ext
    intro U
    exact PresheafOfModules.sections_property s _
  right_inv s := by
    change M.presheaf.map (𝟙 (.op ⊤)) s = s
    simp

/-- A morphism from the structure sheaf is determined by the image of its global unit section. -/
def structureSheafHomEquiv {X : Scheme.{u}} (M : X.Modules) :
    (LineBundle.Construction.structureSheafModule X ⟶ M) ≃ Γ(M, ⊤) :=
  (SheafOfModules.unitHomEquiv M).trans (moduleSectionsEquivGlobal M)

theorem structureSheafHomEquiv_apply {X : Scheme.{u}} (M : X.Modules)
    (f : LineBundle.Construction.structureSheafModule X ⟶ M) :
    structureSheafHomEquiv M f = f.app ⊤ (1 : Γ(X, ⊤)) := rfl

/-- On every open set, a map from the structure sheaf acts by multiplication
by the restriction of its global section. -/
theorem structureSheafHom_apply {X : Scheme.{u}} {M : X.Modules}
    (f : LineBundle.Construction.structureSheafModule X ⟶ M) (U : X.Opens) (r : Γ(X, U)) :
    f.app U r = r • M.presheaf.map (homOfLE (show U ≤ ⊤ from le_top)).op
      (structureSheafHomEquiv M f) := by
  have h := PresheafOfModules.sections_property (SheafOfModules.unitHomEquiv M f)
    (homOfLE (show U ≤ ⊤ from le_top)).op
  change M.presheaf.map _ (f.app ⊤ (1 : Γ(X, ⊤))) = f.app U (1 : Γ(X, U)) at h
  rw [structureSheafHomEquiv_apply, h]
  calc
    f.app U r = f.app U (r • (1 : Γ(X, U))) := congrArg (f.app U) (mul_one r).symm
    _ = r • f.app U (1 : Γ(X, U)) := f.app_smul r _

/-- Endomorphisms of the structure sheaf form the ring of global regular functions. -/
def structureSheafEndRingEquiv (X : Scheme.{u}) :
    End (LineBundle.Construction.structureSheafModule X) ≃+* Γ(X, ⊤) where
  __ := structureSheafHomEquiv (LineBundle.Construction.structureSheafModule X)
  map_add' f g := rfl
  map_mul' f g := by
    let a : Γ(X, ⊤) := f.app ⊤ (1 : Γ(X, ⊤))
    let b : Γ(X, ⊤) := g.app ⊤ (1 : Γ(X, ⊤))
    change (f.app ⊤ b : Γ(X, ⊤)) = a * b
    rw [structureSheafHom_apply]
    change b * X.presheaf.map (𝟙 (.op ⊤)) a = a * b
    simp [mul_comm]

end

end OAI.ArithmeticGeometry.OrdinaryLocus.Openness.ModuleSections.Construction
