import OAI.AlgebraicGeometry.Picard.Homomorphisms.ModuleHomSheaf
import Mathlib.CategoryTheory.Preadditive.FunctorCategory

/-! # Module Hom Sections -/

namespace OAI.AlgebraicGeometry.Picard.Homomorphisms.ModuleHomSections

noncomputable section

/-! Scalar multiplication on local module homomorphisms. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry Opposite

set_option backward.isDefEq.respectTransparency.types false

namespace Construction

universe u

variable {X : Scheme.{u}} (M N : X.Modules)

/-- A ring section acts on the restricted target sheaf by multiplication. -/
def localSectionScalarEnd (U : X.Opens) :
    Γ(X, U) →+* End ((Over.forget U).op ⋙ N.presheaf) where
  toFun r :=
    { app V := ModuleCat.smul (N.val.obj (.op V.unop.left))
        (X.presheaf.map V.unop.hom.op r)
      naturality {V W} f := by
        ext s
        change Γ(N, V.unop.left) at s
        change X.presheaf.map W.unop.hom.op r •
            (show Γ(N, W.unop.left) from N.presheaf.map f.unop.left.op s) =
          N.presheaf.map f.unop.left.op
            (X.presheaf.map V.unop.hom.op r • (s : Γ(N, V.unop.left)))
        erw [N.val.map_smul]
        have hr : X.presheaf.map f.unop.left.op (X.presheaf.map V.unop.hom.op r) =
            X.presheaf.map W.unop.hom.op r := by
          rw [← Functor.map_comp_apply, ← op_comp, Over.w f.unop]
        exact congrArg (fun c : Γ(X, W.unop.left) =>
          c • (show Γ(N, W.unop.left) from N.presheaf.map f.unop.left.op s)) hr.symm }
  map_one' := by
    apply NatTrans.ext
    funext V
    apply AddCommGrpCat.ext
    intro s
    change Γ(N, V.unop.left) at s
    change X.presheaf.map V.unop.hom.op (1 : Γ(X, U)) • (s : Γ(N, V.unop.left)) = s
    rw [map_one, one_smul]
  map_zero' := by
    apply NatTrans.ext
    funext V
    apply AddCommGrpCat.ext
    intro s
    change Γ(N, V.unop.left) at s
    change X.presheaf.map V.unop.hom.op (0 : Γ(X, U)) • (s : Γ(N, V.unop.left)) = 0
    rw [map_zero, zero_smul]
  map_add' r t := by
    apply NatTrans.ext
    funext V
    apply AddCommGrpCat.ext
    intro s
    change Γ(N, V.unop.left) at s
    change X.presheaf.map V.unop.hom.op (r + t) • (s : Γ(N, V.unop.left)) =
      X.presheaf.map V.unop.hom.op r • s + X.presheaf.map V.unop.hom.op t • s
    rw [map_add, add_smul]
  map_mul' r t := by
    apply NatTrans.ext
    funext V
    apply AddCommGrpCat.ext
    intro s
    change Γ(N, V.unop.left) at s
    change X.presheaf.map V.unop.hom.op (r * t) • (s : Γ(N, V.unop.left)) =
      X.presheaf.map V.unop.hom.op r • (X.presheaf.map V.unop.hom.op t • s)
    rw [map_mul, smul_smul]

instance localAdditiveHomAddCommGroup (U : X.Opens) :
    AddCommGroup ((presheafHom M.presheaf N.presheaf).obj (.op U)) :=
  inferInstanceAs (AddCommGroup
    (((Over.forget U).op ⋙ M.presheaf) ⟶ ((Over.forget U).op ⋙ N.presheaf)))

instance localAdditiveHomModule (U : X.Opens) :
    Module Γ(X, U) ((presheafHom M.presheaf N.presheaf).obj (.op U)) :=
  Module.compHom (((Over.forget U).op ⋙ M.presheaf) ⟶ ((Over.forget U).op ⋙ N.presheaf))
    (localSectionScalarEnd N U)

theorem localAdditiveHom_smul_app (U : X.Opens) (r : Γ(X, U))
    (a : (presheafHom M.presheaf N.presheaf).obj (.op U))
    (V : Over U) (s : Γ(M, V.left)) :
    (r • a).app (.op V) s =
      X.presheaf.map V.hom.op r • (show Γ(N, V.left) from a.app (.op V) s) := rfl

/-- Linearity cuts out a submodule of the local additive homomorphisms. -/
def linearHomSubmodule (U : X.Opens) :
    Submodule Γ(X, U) ((presheafHom M.presheaf N.presheaf).obj (.op U)) where
  carrier := {a | ModuleHomSheaf.Construction.IsLinearLocalHom M N a}
  zero_mem' := by
    intro V r s
    change (0 : Γ(N, V.left)) = r • 0
    rw [smul_zero]
  add_mem' {a b} ha hb := by
    intro V r s
    change (show Γ(N, V.left) from a.app (.op V) (r • s)) +
        (show Γ(N, V.left) from b.app (.op V) (r • s)) =
      r • ((show Γ(N, V.left) from a.app (.op V) s) +
        (show Γ(N, V.left) from b.app (.op V) s))
    rw [ha, hb, smul_add]
  smul_mem' r a ha := by
    intro V t s
    rw [localAdditiveHom_smul_app, localAdditiveHom_smul_app, ha]
    exact smul_comm _ _ _

/-- The sheaf sections of local linear maps carry their natural scalar module. -/
instance linearHomSectionAddCommGroup (U : X.Opens) :
    AddCommGroup ((ModuleHomSheaf.Construction.linearHomSubfunctor M N).toFunctor.obj (.op U)) :=
  inferInstanceAs (AddCommGroup (linearHomSubmodule M N U))

instance linearHomSectionModule (U : X.Opens) :
    Module Γ(X, U) ((ModuleHomSheaf.Construction.linearHomSubfunctor M N).toFunctor.obj (.op U)) :=
  inferInstanceAs (Module Γ(X, U) (linearHomSubmodule M N U))

end Construction

end

end OAI.AlgebraicGeometry.Picard.Homomorphisms.ModuleHomSections
