import Mathlib
import OAI.AlgebraicGeometry.ComplexMultiplication.CMAbelianVariety

/-! # End -/

namespace OAI.AlgebraicGeometry.AbelianScheme.TateComparison.End

noncomputable section

/-!
Integral endomorphisms are natural additive endomorphisms of the actual
functor of points. Yoneda reconstructs their underlying scheme maps.
The ring operations therefore act by point addition and composition, not
by arbitrary linear operators supplied as an external realization.
-/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj TensorProduct

universe u

variable {S : Scheme.{u}} (A : Over S) [GrpObj A] [IsCommMonObj A]

/-- The actual functor of points, written additively. -/
def additivePoints : (Over S)ᵒᵖ ⥤ AddCommGrpCat.{u} where
  obj T := AddCommGrpCat.of (Additive (T.unop ⟶ A))
  map f := AddCommGrpCat.ofHom
    (((yonedaGrpObj A).map f).hom.toAdditive)
  map_id T := by
    apply AddCommGrpCat.hom_ext
    apply AddMonoidHom.ext
    intro x
    change 𝟙 T.unop ≫ x.toMul = x.toMul
    exact Category.id_comp x.toMul
  map_comp f g := by
    apply AddCommGrpCat.hom_ext
    apply AddMonoidHom.ext
    intro x
    change (g.unop ≫ f.unop) ≫ x.toMul = g.unop ≫ f.unop ≫ x.toMul
    exact Category.assoc _ _ x.toMul

/-- Integral algebraic group endomorphisms, via their faithful point functor. -/
abbrev IntegralEnd := CategoryTheory.End (additivePoints A)

/-- Rational endomorphisms are the scalar extension of the integral ring. -/
abbrev RationalEnd := ℚ ⊗[ℤ] IntegralEnd A

/-- The natural inclusion into rational endomorphisms. -/
def endToRational : IntegralEnd A →+* RationalEnd A :=
  Algebra.TensorProduct.includeRight.toRingHom

/-- Recover the scheme morphism by evaluation on the universal point. -/
def endSchemeMap (f : IntegralEnd A) : A ⟶ A :=
  ((f.app (.op A)).hom (Additive.ofMul (𝟙 A))).toMul

/-- The recovered scheme map acts on every test-scheme point as prescribed. -/
theorem endSchemeMap_points (f : IntegralEnd A) (T : Over S) (x : T ⟶ A) :
    ((f.app (.op T)).hom (Additive.ofMul x)).toMul = x ≫ endSchemeMap A f := by
  have h := congrArg
    (fun k : (additivePoints A).obj (.op A) ⟶ (additivePoints A).obj (.op T) =>
      (k.hom (Additive.ofMul (𝟙 A))).toMul) (f.naturality x.op)
  change ((f.app (.op T)).hom (Additive.ofMul (x ≫ 𝟙 A))).toMul =
    x ≫ endSchemeMap A f at h
  simpa only [Category.comp_id] using h

/-- Algebraic group homomorphisms induce natural additive maps on points. -/
def endOfSchemeMap (f : A ⟶ A) [IsMonHom f] : IntegralEnd A where
  app T := AddCommGrpCat.ofHom ((IsMonHom.monoidHom f T.unop).toAdditive)
  naturality {X Y} h := by
    apply AddCommGrpCat.hom_ext
    apply AddMonoidHom.ext
    intro x
    change (h.unop ≫ x.toMul) ≫ f = h.unop ≫ x.toMul ≫ f
    exact Category.assoc _ _ _

@[simp]
theorem endSchemeMap_ofSchemeMap (f : A ⟶ A) [IsMonHom f] :
    endSchemeMap A (endOfSchemeMap A f) = f := by
  change 𝟙 A ≫ f = f
  exact Category.id_comp f

/-- The scheme-map reconstruction loses no natural endomorphism. -/
theorem endSchemeMap_injective : Function.Injective (endSchemeMap A) := by
  intro f g h
  apply NatTrans.ext
  funext T
  apply AddCommGrpCat.hom_ext
  apply AddMonoidHom.ext
  intro x
  change ((f.app T).hom x).toMul = ((g.app T).hom x).toMul
  exact (endSchemeMap_points A f T.unop x.toMul).trans
    ((congrArg (fun k => x.toMul ≫ k) h).trans
      (endSchemeMap_points A g T.unop x.toMul).symm)

theorem endSchemeMap_mul_points (f : IntegralEnd A) (T : Over S) (x y : T ⟶ A) :
    (x * y) ≫ endSchemeMap A f =
      (x ≫ endSchemeMap A f) * (y ≫ endSchemeMap A f) := by
  rw [← endSchemeMap_points, ← endSchemeMap_points, ← endSchemeMap_points]
  exact congrArg Additive.toMul ((f.app (.op T)).hom.map_add
    (Additive.ofMul x) (Additive.ofMul y))

theorem endSchemeMap_one_points (f : IntegralEnd A) (T : Over S) :
    (1 : T ⟶ A) ≫ endSchemeMap A f = 1 := by
  rw [← endSchemeMap_points]
  exact congrArg Additive.toMul ((f.app (.op T)).hom.map_zero)

open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory

/-- The scheme map reconstructed by Yoneda preserves the algebraic group law. -/
instance endSchemeMap_isMonHom (f : IntegralEnd A) : IsMonHom (endSchemeMap A f) where
  one_hom := by
    have h := endSchemeMap_one_points A f (𝟙_ (Over S))
    simpa only [MonObj.one_eq_one] using h
  mul_hom := by
    have h := endSchemeMap_mul_points A f (A ⊗ A) (fst A A) (snd A A)
    simpa only [CategoryTheory.Hom.mul_def, lift_fst_snd, Category.id_comp,
      lift_fst_comp_snd_comp] using h

/-- Endomorphisms of the point functor are exactly algebraic group maps. -/
def endSchemeEquiv : IntegralEnd A ≃ {f : A ⟶ A // IsMonHom f} where
  toFun f := ⟨endSchemeMap A f, inferInstance⟩
  invFun f := @endOfSchemeMap _ A _ _ f.val f.property
  left_inv f := endSchemeMap_injective A (endSchemeMap_ofSchemeMap A _)
  right_inv f := by
    let : IsMonHom f.val := f.property
    exact Subtype.ext (endSchemeMap_ofSchemeMap A f.val)

end

end OAI.AlgebraicGeometry.AbelianScheme.TateComparison.End
