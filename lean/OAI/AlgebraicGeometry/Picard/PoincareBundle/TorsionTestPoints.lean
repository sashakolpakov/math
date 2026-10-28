import OAI.AlgebraicGeometry.Picard.Homomorphisms.UnbundledTranslationBaseChange
import OAI.AlgebraicGeometry.AbelianScheme.CartierDuality.KernelCharacterBaseChange

/-! # Torsion Test Points -/

namespace OAI.AlgebraicGeometry.Picard.PoincareBundle.TorsionTestPoints

noncomputable section

/-! Full scheme-valued torsion points, their restriction maps, and their exact base-change equivalences. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj

universe u

open OAI.AlgebraicGeometry.Picard.Homomorphisms.UnbundledTranslationBaseChange.Construction.UnbundledPicard

/-- All n-torsion points on an arbitrary test scheme, without reduction. -/
def Point {S : Scheme.{u}} (A : Over S) [GrpObj A] (n : ℕ) (T : Over S) :=
  {x : T ⟶ A // x ^ n = 1}

/-- Restriction is precomposition on actual scheme morphisms. -/
def restrict {S : Scheme.{u}} {A : Over S} [GrpObj A] {n : ℕ}
    {T U : Over S} (f : U ⟶ T) (x : Point A n T) : Point A n U :=
  ⟨f ≫ x.val, by rw [← MonObj.comp_pow, x.property, MonObj.comp_one]⟩

/-- Successive restrictions are the restriction along the composite. -/
theorem restrict_comp {S : Scheme.{u}} {A : Over S} [GrpObj A] {n : ℕ}
    {T U V : Over S} (f : U ⟶ T) (g : V ⟶ U) (x : Point A n T) :
    restrict g (restrict f x) = restrict (g ≫ f) x :=
  Subtype.ext (Category.assoc g f x.val).symm

/-- Pullback preserves all torsion points by the actual scheme pullback adjunction. -/
def pullbackEquiv {S S' : Scheme.{u}} (s : S' ⟶ S) (A : Over S) [GrpObj A]
    (n : ℕ) (T : Over S') : Point ((Over.pullback s).obj A) n T ≃ Point A n ((Over.map s).obj T) where
  toFun x := ⟨Homomorphisms.UnbundledBaseChangePoints.Construction.UnbundledPicard.baseChangePointsEquiv A s T x.val, by
    let e := Homomorphisms.UnbundledBaseChangePoints.Construction.UnbundledPicard.baseChangePointsMulEquiv A s T
    exact (map_pow e x.val n).symm.trans ((congrArg e x.property).trans (map_one e))⟩
  invFun x := ⟨(Homomorphisms.UnbundledBaseChangePoints.Construction.UnbundledPicard.baseChangePointsEquiv A s T).symm x.val, by
    let e := (Homomorphisms.UnbundledBaseChangePoints.Construction.UnbundledPicard.baseChangePointsMulEquiv A s T).symm
    exact (map_pow e x.val n).symm.trans ((congrArg e x.property).trans (map_one e))⟩
  left_inv x := Subtype.ext ((Homomorphisms.UnbundledBaseChangePoints.Construction.UnbundledPicard.baseChangePointsEquiv A s T).symm_apply_apply x.val)
  right_inv x := Subtype.ext ((Homomorphisms.UnbundledBaseChangePoints.Construction.UnbundledPicard.baseChangePointsEquiv A s T).apply_symm_apply x.val)

/-- The full torsion-point comparison commutes with arbitrary test restriction. -/
theorem pullback_restrict {S S' : Scheme.{u}} (s : S' ⟶ S) (A : Over S) [GrpObj A]
    (n : ℕ) {T U : Over S'} (f : U ⟶ T) (x : Point ((Over.pullback s).obj A) n T) :
    pullbackEquiv s A n U (restrict f x) = restrict ((Over.map s).map f) (pullbackEquiv s A n T x) :=
  Subtype.ext (Homomorphisms.UnbundledTranslationBaseChange.Construction.UnbundledPicard.baseChangePointsEquiv_precomp A s f x.val)

/-- The original and pulled-back kernel conditions are equivalent on every test scheme. -/
theorem kernel_iff {S S' : Scheme.{u}} (s : S' ⟶ S) {A B : Over S} [GrpObj A] [GrpObj B]
    (f : A ⟶ B) (T : Over S') (x : T ⟶ (Over.pullback s).obj A) :
    x ≫ (Over.pullback s).map f = 1 ↔ Homomorphisms.UnbundledBaseChangePoints.Construction.UnbundledPicard.baseChangePointsEquiv A s T x ≫ f = 1 := by
  have hmap := AbelianScheme.CartierDuality.KernelCharacterBaseChange.Construction.KernelCharacters.pullbackPoint_symm_comp s f T x
  have hone : Homomorphisms.UnbundledBaseChangePoints.Construction.UnbundledPicard.baseChangePointsEquiv B s T 1 = 1 := (Homomorphisms.UnbundledBaseChangePoints.Construction.UnbundledPicard.baseChangePointsMulEquiv B s T).map_one
  constructor
  · intro h
    exact hmap.symm.trans ((congrArg (Homomorphisms.UnbundledBaseChangePoints.Construction.UnbundledPicard.baseChangePointsEquiv B s T) h).trans hone)
  · intro h
    apply (Homomorphisms.UnbundledBaseChangePoints.Construction.UnbundledPicard.baseChangePointsEquiv B s T).injective
    exact hmap.trans (h.trans hone.symm)

end

end OAI.AlgebraicGeometry.Picard.PoincareBundle.TorsionTestPoints
