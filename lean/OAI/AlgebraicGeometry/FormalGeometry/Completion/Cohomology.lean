import Mathlib.AlgebraicGeometry.Sites.ElladicCohomology
import Mathlib.LinearAlgebra.TensorProduct.Basic

/-! # Cohomology -/

namespace OAI.AlgebraicGeometry.FormalGeometry.Completion.Cohomology.Construction

noncomputable section

/-!
# Completion: integral scalar multiplication on actual ℓ-adic cohomology

The scalar action is induced by multiplication on the coefficient sheaf.
It is constructed on mathlib's cohomology groups, with no weight or
Frobenius assertions built into the definitions.
-/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

variable (ℓ : ℕ) [Fact ℓ.Prime]

/-- Multiplication by a coefficient on the continuous-function presheaf. -/
def continuousCoefficientScalar (a : ℤ_[ℓ]) :
    continuousMapPresheafAb (ℤ_[ℓ]) ⟶
      continuousMapPresheafAb (ℤ_[ℓ]) where
  app U := AddCommGrpCat.ofHom {
    toFun := fun f => a • f
    map_zero' := smul_zero a
    map_add' := fun f g => by
      ext x
      exact mul_add a (f x) (g x)
  }
  naturality := by
    intro U V f
    ext s
    rfl

variable (X : Scheme.{u})

/-- Multiplication on the actual coefficient sheaf on the small pro-étale site. -/
def ellAdicSheafScalar (a : ℤ_[ℓ]) :
    X.ellAdicSheaf ℓ ⟶ X.ellAdicSheaf ℓ where
  hom := Functor.whiskerLeft (Scheme.ProEt.forget X ⋙ Over.forget _).op
    (continuousCoefficientScalar ℓ a)

theorem ellAdicSheafScalar_one : ellAdicSheafScalar ℓ X 1 = 𝟙 _ := by
  ext U s
  change C(((Scheme.ProEt.forget X).obj U.unop).left, ℤ_[ℓ]) at s
  change (1 : ℤ_[ℓ]) • s = s
  exact one_smul (ℤ_[ℓ]) s

theorem ellAdicSheafScalar_zero : ellAdicSheafScalar ℓ X 0 = 0 := by
  ext U s
  change C(((Scheme.ProEt.forget X).obj U.unop).left, ℤ_[ℓ]) at s
  change (0 : ℤ_[ℓ]) • s = 0
  exact zero_smul (ℤ_[ℓ]) s

theorem ellAdicSheafScalar_add (a b : ℤ_[ℓ]) :
    ellAdicSheafScalar ℓ X (a + b) =
      ellAdicSheafScalar ℓ X a + ellAdicSheafScalar ℓ X b := by
  ext U s
  change C(((Scheme.ProEt.forget X).obj U.unop).left, ℤ_[ℓ]) at s
  change (a + b) • s = a • s + b • s
  exact add_smul a b s

theorem ellAdicSheafScalar_mul (a b : ℤ_[ℓ]) :
    ellAdicSheafScalar ℓ X (a * b) =
      ellAdicSheafScalar ℓ X b ≫ ellAdicSheafScalar ℓ X a := by
  ext U s
  change C(((Scheme.ProEt.forget X).obj U.unop).left, ℤ_[ℓ]) at s
  change (a * b) • s = a • (b • s)
  exact mul_smul a b s

/-- Scalar multiplication lifted to the coefficient sheaf universe used by H. -/
noncomputable def liftedEllAdicScalar (a : ℤ_[ℓ]) :
    (sheafCompose _ AddCommGrpCat.uliftFunctor.{u + 1}).obj (X.ellAdicSheaf ℓ) ⟶
      (sheafCompose _ AddCommGrpCat.uliftFunctor.{u + 1}).obj (X.ellAdicSheaf ℓ) :=
  (sheafCompose _ AddCommGrpCat.uliftFunctor.{u + 1}).map
    (ellAdicSheafScalar ℓ X a)

theorem liftedEllAdicScalar_add (a b : ℤ_[ℓ]) :
    liftedEllAdicScalar ℓ X (a + b) =
      liftedEllAdicScalar ℓ X a + liftedEllAdicScalar ℓ X b := by
  unfold liftedEllAdicScalar
  rw [ellAdicSheafScalar_add]
  ext U s
  rfl

/-- Scalar multiplication on the existing integral ℓ-adic cohomology group. -/
noncomputable def ellAdicCohomologyScalar (n : ℕ) (a : ℤ_[ℓ]) :
    X.EllAdicCohomology ℓ n →+ X.EllAdicCohomology ℓ n :=
  Sheaf.H.map (liftedEllAdicScalar ℓ X a) n

noncomputable instance ellAdicCohomologyModule (n : ℕ) :
    Module (ℤ_[ℓ]) (X.EllAdicCohomology ℓ n) where
  smul a x := ellAdicCohomologyScalar ℓ X n a x
  one_smul x := by
    change ellAdicCohomologyScalar ℓ X n 1 x = x
    unfold ellAdicCohomologyScalar liftedEllAdicScalar
    rw [ellAdicSheafScalar_one, CategoryTheory.Functor.map_id]
    exact Sheaf.H.map_id_apply x
  mul_smul a b x := by
    change ellAdicCohomologyScalar ℓ X n (a * b) x =
      ellAdicCohomologyScalar ℓ X n a (ellAdicCohomologyScalar ℓ X n b x)
    unfold ellAdicCohomologyScalar liftedEllAdicScalar
    rw [ellAdicSheafScalar_mul, CategoryTheory.Functor.map_comp]
    exact Sheaf.H.map_comp_apply _ _ x
  smul_zero a := (ellAdicCohomologyScalar ℓ X n a).map_zero
  smul_add a x y := (ellAdicCohomologyScalar ℓ X n a).map_add x y
  add_smul a b x := by
    change ellAdicCohomologyScalar ℓ X n (a + b) x =
      ellAdicCohomologyScalar ℓ X n a x + ellAdicCohomologyScalar ℓ X n b x
    unfold ellAdicCohomologyScalar
    rw [liftedEllAdicScalar_add]
    exact Sheaf.H.map_add_apply _ _ x
  zero_smul x := by
    change ellAdicCohomologyScalar ℓ X n 0 x = 0
    unfold ellAdicCohomologyScalar liftedEllAdicScalar
    rw [ellAdicSheafScalar_zero, CategoryTheory.Functor.map_zero]
    change x.comp (CategoryTheory.Abelian.Ext.mk₀ 0) (add_zero n) = 0
    rw [CategoryTheory.Abelian.Ext.mk₀_zero]
    exact CategoryTheory.Abelian.Ext.comp_zero x _ 0 n (add_zero n)

/-- Extension of coefficients to an algebraic closure of ℚ_ℓ. -/
abbrev EllAdicH1AlgebraicCoefficients (Y : Scheme.{u}) :=
  TensorProduct (ℤ_[ℓ]) (AlgebraicClosure ℚ_[ℓ]) (Y.EllAdicCohomology ℓ 1)

/-- The actual base change to an algebraic closure of the ground field. -/
noncomputable def geometricFiber
    {k : Type u} [Field k] (A : Over (Spec (CommRingCat.of k))) : Scheme.{u} :=
  Limits.pullback A.hom
    (Spec.map (CommRingCat.ofHom (algebraMap k (AlgebraicClosure k))))

/-- Degree-one geometric cohomology with algebraically closed ℓ-adic coefficients. -/
abbrev GeometricH1
    {k : Type u} [Field k] (A : Over (Spec (CommRingCat.of k))) :=
  EllAdicH1AlgebraicCoefficients ℓ (geometricFiber A)

end

end OAI.AlgebraicGeometry.FormalGeometry.Completion.Cohomology.Construction
