import OAI.AlgebraicGeometry.Picard.Homomorphisms.Properties
import Mathlib.CategoryTheory.Monoidal.Cartesian.Grp

/-! # Group -/

namespace OAI.AlgebraicGeometry.Picard.Homomorphisms.Group.Construction

open _root_.CategoryTheory _root_.AlgebraicGeometry Opposite _root_.CategoryTheory.Limits
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj

universe u

variable (p : ℕ) (hp : p.Prime)

set_option backward.isDefEq.respectTransparency.types false in
noncomputable def relativeFrobeniusNat {S : Scheme.{u}}
    (hS : (p : Γ(S, ⊤)) = 0) :
    𝟭 (Over S) ⟶ Over.pullback (Frobenius.Construction.absoluteFrobenius p hp S hS) where
  app A := Frobenius.Construction.relativeFrobenius p hp hS A
  naturality {A B} f := by
    apply Over.OverMorphism.ext
    apply pullback.hom_ext
    · simp only [Over.comp_left, Over.pullback_map_left, Frobenius.Construction.relativeFrobenius,
        Over.homMk_left, Category.assoc, pullback.lift_fst,
        pullback.lift_fst_assoc]
      exact (Frobenius.Construction.absoluteFrobenius_naturality p hp _ _ f.left).symm
    · simp only [Over.comp_left, Over.pullback_map_left, Frobenius.Construction.relativeFrobenius,
        Over.homMk_left, Category.assoc, pullback.lift_snd]
      exact f.w

noncomputable instance frobeniusTwist_grp {S : Scheme.{u}}
    (hS : (p : Γ(S, ⊤)) = 0) (A : Over S) [GrpObj A] :
    GrpObj (Frobenius.Construction.frobeniusTwist p hp hS A) :=
  Functor.grpObjObj (F := Over.pullback (Frobenius.Construction.absoluteFrobenius p hp S hS)) (G := A)

set_option backward.isDefEq.respectTransparency.types false in
instance relativeFrobenius_isMonHom {S : Scheme.{u}}
    (hS : (p : Γ(S, ⊤)) = 0) (A : Over S) [GrpObj A] :
    IsMonHom (Frobenius.Construction.relativeFrobenius p hp hS A) := by
  let f : Mon.mk A ⟶
      (Over.pullback (Frobenius.Construction.absoluteFrobenius p hp S hS)).mapMon.obj (Mon.mk A) :=
    Functor.mapMonIdIso.inv.app (Mon.mk A) ≫
      (Functor.mapMonNatTrans (relativeFrobeniusNat p hp hS)).app (Mon.mk A)
  have hf : IsMonHom f.hom := inferInstance
  have hf' : IsMonHom ((𝟙 A) ≫ Frobenius.Construction.relativeFrobenius p hp hS A) := hf
  simpa only [Category.id_comp] using hf'

end OAI.AlgebraicGeometry.Picard.Homomorphisms.Group.Construction
