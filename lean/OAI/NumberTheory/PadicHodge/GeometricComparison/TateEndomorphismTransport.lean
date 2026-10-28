import OAI.AlgebraicGeometry.AbelianScheme.TateComparison.End
import OAI.AlgebraicGeometry.FormalGeometry.Completion.Endomorphisms

/-! # Tate Endomorphism Transport -/

namespace OAI.NumberTheory.PadicHodge.GeometricComparison.TateEndomorphismTransport.Comparison

noncomputable section

/-! The TateComparison point-functor endomorphisms and the GeometricComparison algebraic group endomorphisms have the same ring structure. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj TensorProduct

universe u

variable {S : Scheme.{u}} (A : Over S) [GrpObj A] [IsCommMonObj A]

def integralEndHom : AlgebraicGeometry.AbelianScheme.TateComparison.End.IntegralEnd A →+* AlgebraicGeometry.FormalGeometry.Completion.Endomorphisms.Construction.AlgebraicEnd A where
  toFun f := Additive.ofMul (Grp.ofHom (AlgebraicGeometry.AbelianScheme.TateComparison.End.endSchemeMap A f))
  map_zero' := by
    apply Grp.hom_ext
    rfl
  map_one' := by
    apply Grp.hom_ext
    rfl
  map_add' f g := by
    apply Grp.hom_ext
    rfl
  map_mul' f g := by
    apply Grp.hom_ext
    exact AlgebraicGeometry.AbelianScheme.TateComparison.End.endSchemeMap_points A f A (AlgebraicGeometry.AbelianScheme.TateComparison.End.endSchemeMap A g)

theorem integralEndHom_bijective : Function.Bijective (integralEndHom A) := by
  constructor
  · intro f g h
    apply AlgebraicGeometry.AbelianScheme.TateComparison.End.endSchemeMap_injective A
    exact congrArg (fun a : AlgebraicGeometry.FormalGeometry.Completion.Endomorphisms.Construction.AlgebraicEnd A => a.toMul.hom.hom) h
  · intro f
    refine ⟨AlgebraicGeometry.AbelianScheme.TateComparison.End.endOfSchemeMap A f.toMul.hom.hom, ?_⟩
    apply Grp.hom_ext
    exact AlgebraicGeometry.AbelianScheme.TateComparison.End.endSchemeMap_ofSchemeMap A f.toMul.hom.hom

def integralEndEquiv : AlgebraicGeometry.AbelianScheme.TateComparison.End.IntegralEnd A ≃+* AlgebraicGeometry.FormalGeometry.Completion.Endomorphisms.Construction.AlgebraicEnd A :=
  RingEquiv.ofBijective (integralEndHom A) (integralEndHom_bijective A)

theorem integralEndEquiv_schemeMap (f : AlgebraicGeometry.AbelianScheme.TateComparison.End.IntegralEnd A) :
    (integralEndEquiv A f).toMul.hom.hom = AlgebraicGeometry.AbelianScheme.TateComparison.End.endSchemeMap A f := rfl

def integralEndAlgEquiv : AlgebraicGeometry.AbelianScheme.TateComparison.End.IntegralEnd A ≃ₐ[ℤ] AlgebraicGeometry.FormalGeometry.Completion.Endomorphisms.Construction.AlgebraicEnd A where
  __ := integralEndEquiv A
  commutes' n := by simp

def rationalEndEquiv : AlgebraicGeometry.AbelianScheme.TateComparison.End.RationalEnd A ≃ₐ[ℚ] AlgebraicGeometry.FormalGeometry.Completion.Endomorphisms.Construction.RationalAlgebraicEnd A :=
  Algebra.TensorProduct.congr (.refl : ℚ ≃ₐ[ℚ] ℚ) (integralEndAlgEquiv A)

theorem rationalEndEquiv_tmul (r : ℚ) (f : AlgebraicGeometry.AbelianScheme.TateComparison.End.IntegralEnd A) :
    rationalEndEquiv A (r ⊗ₜ[ℤ] f) = r ⊗ₜ[ℤ] integralEndEquiv A f := rfl

theorem rationalEndEquiv_integral (f : AlgebraicGeometry.AbelianScheme.TateComparison.End.IntegralEnd A) :
    rationalEndEquiv A (AlgebraicGeometry.AbelianScheme.TateComparison.End.endToRational A f) = (1 : ℚ) ⊗ₜ[ℤ] integralEndEquiv A f := rfl

end

end OAI.NumberTheory.PadicHodge.GeometricComparison.TateEndomorphismTransport.Comparison
