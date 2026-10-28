import OAI.AlgebraicGeometry.AbelianScheme.TateComparison.PELBaseChange

/-! # PEL Transport -/

namespace OAI.AlgebraicGeometry.AbelianScheme.TateComparison

noncomputable section

/-! Transport actual PEL isogenies through isomorphisms of their source
and target families, without changing the multiplier or the marking. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj

universe u

variable {R : Type u} [CommRing R] {g N : ℕ} {S : Scheme.{u}}

section

variable {A B : PEL.PELFamilyData R g N S}

def PELModuli.PELFamilyIso.toIsogeny (e : PELModuli.PELFamilyIso A B) : PELIsogenies.PELIsogeny A B 1 where
  isogeny := {
    hom := e.abelian.hom
    preservesGroup := inferInstance
    finite := by
      have : IsIso e.abelian.hom.left := (Over.forget S).map_isIso e.abelian.hom
      infer_instance
    flat := by
      have : IsIso e.abelian.hom.left := (Over.forget S).map_isIso e.abelian.hom
      infer_instance
    surjective := by
      have : IsIso e.abelian.hom.left := (Over.forget S).map_isIso e.abelian.hom
      infer_instance }
  dualHom := e.dual.inv
  dualGroup := inferInstance
  poincare := by
    have h := congrArg (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackClass (e.dual.inv ⊗ₘ 𝟙 A.abelian.scheme).left) e.poincare
    rw [← AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackClass_comp, ← Over.comp_left, tensorHom_comp_tensorHom,
      Iso.inv_hom_id, Category.id_comp] at h
    exact h
  equivariant := e.equivariant
  polarization := by
    change e.abelian.hom ≫ B.polarizationMap.hom ≫ e.dual.inv = A.polarizationMap.hom ^ 1
    rw [← Category.assoc, ← e.polarization, Category.assoc, Iso.hom_inv_id, Category.comp_id, pow_one]
  marking := e.marking

end

variable {A A' B B' : PEL.PELFamilyData R g N S} {n m : ℕ}

def PELIsogenies.PELIsogeny.castMultiplier (h : n = m) (e : PELIsogenies.PELIsogeny A B n) : PELIsogenies.PELIsogeny A B m := h ▸ e

@[simp]
theorem PELIsogenies.PELIsogeny.castMultiplier_hom (h : n = m) (e : PELIsogenies.PELIsogeny A B n) :
    (e.castMultiplier h).isogeny.hom = e.isogeny.hom := by cases h; rfl

@[simp]
theorem PELIsogenies.PELIsogeny.castMultiplier_dualHom (h : n = m) (e : PELIsogenies.PELIsogeny A B n) :
    (e.castMultiplier h).dualHom = e.dualHom := by cases h; rfl

def PELIsogenies.PELIsogeny.transport (e : PELIsogenies.PELIsogeny A B n) (a : PELModuli.PELFamilyIso A' A) (b : PELModuli.PELFamilyIso B B') :
    PELIsogenies.PELIsogeny A' B' n :=
  ((a.toIsogeny.comp e).comp b.toIsogeny).castMultiplier (by simp)

@[simp]
theorem PELIsogenies.PELIsogeny.transport_hom (e : PELIsogenies.PELIsogeny A B n) (a : PELModuli.PELFamilyIso A' A) (b : PELModuli.PELFamilyIso B B') :
    (e.transport a b).isogeny.hom = a.abelian.hom ≫ e.isogeny.hom ≫ b.abelian.hom := by
  rw [PELIsogenies.PELIsogeny.transport, PELIsogenies.PELIsogeny.castMultiplier_hom]
  exact Category.assoc _ _ _

@[simp]
theorem PELIsogenies.PELIsogeny.transport_dualHom (e : PELIsogenies.PELIsogeny A B n) (a : PELModuli.PELFamilyIso A' A) (b : PELModuli.PELFamilyIso B B') :
    (e.transport a b).dualHom = b.dual.inv ≫ e.dualHom ≫ a.dual.inv := by
  rw [PELIsogenies.PELIsogeny.transport, PELIsogenies.PELIsogeny.castMultiplier_dualHom]
  rfl

end

end OAI.AlgebraicGeometry.AbelianScheme.TateComparison
