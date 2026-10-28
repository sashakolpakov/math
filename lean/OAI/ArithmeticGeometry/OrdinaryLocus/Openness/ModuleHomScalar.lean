import OAI.ArithmeticGeometry.OrdinaryLocus.Openness.ModuleHomAdditive

/-! # Module Hom Scalar -/

namespace OAI.ArithmeticGeometry.OrdinaryLocus.Openness.ModuleHomScalar.Construction

noncomputable section

/-! Scalar multiplication on local module homomorphisms. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

theorem overSectionRestriction_comp {X : Scheme.{u}} (U : X.Opens)
    {V W : Over U} (h : V ⟶ W) (r : Γ(X, U)) :
    X.presheaf.map h.left.op (X.presheaf.map W.hom.op r) = X.presheaf.map V.hom.op r := by
  have he : W.hom.op ≫ h.left.op = V.hom.op := congrArg Quiver.Hom.op (Over.w h)
  have hm := (X.presheaf.map_comp W.hom.op h.left.op).symm.trans (congrArg X.presheaf.map he)
  exact congrArg (fun q ↦ q r) hm

def moduleScalarNat {X : Scheme.{u}} (N : X.Modules) (U : X.Opens) (r : Γ(X, U)) :
    (Over.forget U).op ⋙ N.presheaf ⟶ (Over.forget U).op ⋙ N.presheaf where
  app V := N.smul (X.presheaf.map V.unop.hom.op r)
  naturality V W h := by
    have hm := Scheme.Modules.map_comp_smul (M := N) h.unop.left
      (X.presheaf.map V.unop.hom.op r)
    exact (congrArg (fun a ↦ N.presheaf.map h.unop.left.op ≫ N.smul a)
      (overSectionRestriction_comp U h.unop r)).symm.trans hm.symm

def moduleHomScalar {X : Scheme.{u}} (M N : X.Modules) (U : X.Opens)
    (r : Γ(X, U)) (q : ModuleHomAdditive.Construction.moduleHomLocalAddSubgroup M N U) : ModuleHomAdditive.Construction.moduleHomLocalAddSubgroup M N U := by
  refine ⟨q.1 ≫ moduleScalarNat N U r, ?_⟩
  intro V a
  change M.smul a ≫ (q.1.app (.op V) ≫ N.smul (X.presheaf.map V.hom.op r)) =
    (q.1.app (.op V) ≫ N.smul (X.presheaf.map V.hom.op r)) ≫ N.smul a
  have hq := q.2 V a
  have hc : N.smul a ≫ N.smul (X.presheaf.map V.hom.op r) =
      N.smul (X.presheaf.map V.hom.op r) ≫ N.smul a := by
    ext m
    exact smul_comm (X.presheaf.map V.hom.op r) a m
  exact (Category.assoc _ _ _).symm.trans
    ((congrArg (fun t ↦ t ≫ N.smul (X.presheaf.map V.hom.op r)) hq).trans
      ((Category.assoc _ _ _).trans
        ((congrArg (fun t ↦ q.1.app (.op V) ≫ t) hc).trans (Category.assoc _ _ _).symm)))

theorem moduleHomScalar_apply {X : Scheme.{u}} (M N : X.Modules) (U : X.Opens)
    (r : Γ(X, U)) (q : ModuleHomAdditive.Construction.moduleHomLocalAddSubgroup M N U) (V : Over U) (m : Γ(M, V.left)) :
    (moduleHomScalar M N U r q).1.app (.op V) m =
      X.presheaf.map V.hom.op r • (show Γ(N, V.left) from q.1.app (.op V) m) := rfl

instance moduleHomLocalModule {X : Scheme.{u}} (M N : X.Modules) (U : X.Opens) :
    Module Γ(X, U) (ModuleHomAdditive.Construction.moduleHomLocalAddSubgroup M N U) where
  smul := moduleHomScalar M N U
  one_smul q := by
    apply Subtype.ext
    apply NatTrans.ext
    funext V
    ext m
    let z : Γ(N, V.unop.left) := q.1.app V m
    change X.presheaf.map V.unop.hom.op 1 • z = z
    simp
  mul_smul r s q := by
    apply Subtype.ext
    apply NatTrans.ext
    funext V
    ext m
    let z : Γ(N, V.unop.left) := q.1.app V m
    change X.presheaf.map V.unop.hom.op (r * s) • z =
      X.presheaf.map V.unop.hom.op r • (X.presheaf.map V.unop.hom.op s • z)
    simp [mul_smul]
  smul_zero r := by
    apply Subtype.ext
    apply NatTrans.ext
    funext V
    ext m
    change X.presheaf.map V.unop.hom.op r • (0 : Γ(N, V.unop.left)) = 0
    exact smul_zero _
  smul_add r q q' := by
    apply Subtype.ext
    apply NatTrans.ext
    funext V
    ext m
    let z : Γ(N, V.unop.left) := q.1.app V m
    let z' : Γ(N, V.unop.left) := q'.1.app V m
    change X.presheaf.map V.unop.hom.op r • (z + z') =
      X.presheaf.map V.unop.hom.op r • z + X.presheaf.map V.unop.hom.op r • z'
    exact smul_add _ _ _
  zero_smul q := by
    apply Subtype.ext
    apply NatTrans.ext
    funext V
    ext m
    let z : Γ(N, V.unop.left) := q.1.app V m
    change X.presheaf.map V.unop.hom.op 0 • z = 0
    simp
  add_smul r s q := by
    apply Subtype.ext
    apply NatTrans.ext
    funext V
    ext m
    let z : Γ(N, V.unop.left) := q.1.app V m
    change X.presheaf.map V.unop.hom.op (r + s) • z =
      X.presheaf.map V.unop.hom.op r • z + X.presheaf.map V.unop.hom.op s • z
    simp [add_smul]

end

end OAI.ArithmeticGeometry.OrdinaryLocus.Openness.ModuleHomScalar.Construction
