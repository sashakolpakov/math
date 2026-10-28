/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
This file has been modified.
-/
import OAI.AlgebraicGeometry.SheafCohomology.Projective.TwistPowers

/-! # Power Frame Scalar -/

namespace OAI.AlgebraicGeometry.SheafCohomology.Projective.PowerFrameScalar

noncomputable section

open _root_.CategoryTheory _root_.AlgebraicGeometry MonoidalCategory
universe u
local instance powerFrameScalarMonoidal (X : Scheme.{u}) : MonoidalCategory X.Modules :=
  Monoidal.Scheme.Modules.monoidalCategory X

/-- A scalar transition between compatible frames of a recursively
tensor-built module family raises to its `n`th power in degree `n`. -/
theorem recursiveTensorTrivialization_hom_eq_comp_scalar
    {X : Scheme.{u}} {M : X.Modules} {P : ℕ → X.Modules}
    (U : X.Opens)
    (T : (M.restrict U.ι ≅ Invertible.Scheme.Modules.unitObj U.toScheme) →
      ∀ n : ℕ, (P n).restrict U.ι ≅ Invertible.Scheme.Modules.unitObj U.toScheme)
    (q : ∀ n : ℕ,
      (P (n + 1)).restrict U.ι ≅
        (P n).restrict U.ι ⊗ M.restrict U.ι)
    (hzero : ∀ e g, (T e 0).hom = (T g 0).hom)
    (hsucc : ∀ e n, (T e (n + 1)).hom =
      (q n).hom ≫ ((T e n).hom ⊗ₘ e.hom) ≫
        (TensorSections.unitObjTensorIso U.toScheme).hom)
    (e g : M.restrict U.ι ≅ Invertible.Scheme.Modules.unitObj U.toScheme)
    (r : Γ(U.toScheme, (⊤ : U.toScheme.Opens)))
    (h : e.hom = g.hom ≫ UnitScalar.unitEndomorphismOfTopSection r) :
    ∀ n : ℕ, (T e n).hom = (T g n).hom ≫
      UnitScalar.unitEndomorphismOfTopSection (r ^ n) := by
  intro n
  induction n with
  | zero =>
      rw [pow_zero, UnitScalar.unitEndomorphismOfTopSection_one, Category.comp_id]
      exact hzero e g
  | succ n hn =>
      have htensor₀ :
          (T e n).hom ⊗ₘ e.hom =
            ((T g n).hom ≫ UnitScalar.unitEndomorphismOfTopSection (r ^ n)) ⊗ₘ
              (g.hom ≫ UnitScalar.unitEndomorphismOfTopSection r) :=
        congrArg₂ (fun a b ↦ a ⊗ₘ b) hn h
      have htensor :
          (T e n).hom ⊗ₘ e.hom =
            ((T g n).hom ⊗ₘ g.hom) ≫
              (UnitScalar.unitEndomorphismOfTopSection (r ^ n) ⊗ₘ
                UnitScalar.unitEndomorphismOfTopSection r) :=
        htensor₀.trans
          (MonoidalCategory.tensorHom_comp_tensorHom
            (T g n).hom g.hom
            (UnitScalar.unitEndomorphismOfTopSection (r ^ n))
            (UnitScalar.unitEndomorphismOfTopSection r)).symm
      rw [hsucc e n, hsucc g n]
      simp only [Category.assoc]
      rw [htensor]
      simp only [Category.assoc]
      rw [TensorSections.unitObjTensorIso_hom_comp_scalars]
      rw [pow_succ]

end

end OAI.AlgebraicGeometry.SheafCohomology.Projective.PowerFrameScalar
