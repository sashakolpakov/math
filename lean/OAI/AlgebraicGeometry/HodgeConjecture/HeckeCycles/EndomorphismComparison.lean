import OAI.AlgebraicGeometry.AbelianScheme.TateComparison.BaseChange
import OAI.AlgebraicGeometry.FormalGeometry.Completion.Endomorphisms

/-! # Endomorphism Comparison -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.EndomorphismComparison.CM

noncomputable section

/-! Identify TateComparison's natural endomorphisms of the point functor with
GeometricComparison/Completion's actual algebraic group endomorphisms, including rationalization. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj TensorProduct
open OAI.AlgebraicGeometry.AbelianScheme.TateComparison.BaseChange OAI.AlgebraicGeometry.FormalGeometry.Completion.Endomorphisms.Construction

variable {S : Scheme} (A : Over S) [GrpObj A] [IsCommMonObj A]

def integralEquiv : AbelianScheme.TateComparison.End.IntegralEnd A ≃+* FormalGeometry.Completion.Endomorphisms.Construction.AlgebraicEnd A where
  toFun f := Additive.ofMul (Grp.ofHom (AbelianScheme.TateComparison.End.endSchemeMap A f))
  invFun f := AbelianScheme.TateComparison.End.endOfSchemeMap A f.toMul.hom.hom
  left_inv f := AbelianScheme.TateComparison.End.endSchemeMap_injective A (AbelianScheme.TateComparison.End.endSchemeMap_ofSchemeMap A _)
  right_inv f := by
    apply Additive.toMul.injective
    apply Grp.hom_ext
    exact AbelianScheme.TateComparison.End.endSchemeMap_ofSchemeMap A f.toMul.hom.hom
  map_add' f g := by
    apply Additive.toMul.injective
    apply Grp.hom_ext
    exact AbelianScheme.TateComparison.BaseChange.endSchemeMap_add A f g
  map_mul' f g := by
    apply Additive.toMul.injective
    apply Grp.hom_ext
    exact AbelianScheme.TateComparison.BaseChange.endSchemeMap_mul A f g

theorem integralEquiv_schemeMap (f : AbelianScheme.TateComparison.End.IntegralEnd A) :
    (integralEquiv A f).toMul.hom.hom = AbelianScheme.TateComparison.End.endSchemeMap A f := rfl

def integralAlgEquiv : AbelianScheme.TateComparison.End.IntegralEnd A ≃ₐ[ℤ] FormalGeometry.Completion.Endomorphisms.Construction.AlgebraicEnd A where
  __ := integralEquiv A
  commutes' n := by
    have hn : (algebraMap ℤ (AbelianScheme.TateComparison.End.IntegralEnd A)) n = (n : AbelianScheme.TateComparison.End.IntegralEnd A) :=
      map_intCast (algebraMap ℤ (AbelianScheme.TateComparison.End.IntegralEnd A)) n
    change integralEquiv A ((algebraMap ℤ (AbelianScheme.TateComparison.End.IntegralEnd A)) n) = (n : FormalGeometry.Completion.Endomorphisms.Construction.AlgebraicEnd A)
    rw [hn]
    exact map_intCast (integralEquiv A) n

def rationalEquiv : AbelianScheme.TateComparison.End.RationalEnd A ≃ₐ[ℚ] FormalGeometry.Completion.Endomorphisms.Construction.RationalAlgebraicEnd A :=
  Algebra.TensorProduct.congr (AlgEquiv.refl : ℚ ≃ₐ[ℚ] ℚ) (integralAlgEquiv A)

theorem rationalEquiv_tmul (a : ℚ) (f : AbelianScheme.TateComparison.End.IntegralEnd A) :
    rationalEquiv A (a ⊗ₜ[ℤ] f) = a ⊗ₜ[ℤ] integralEquiv A f := by
  simp [rationalEquiv, integralAlgEquiv]

theorem rationalEquiv_integral (f : AbelianScheme.TateComparison.End.IntegralEnd A) :
    rationalEquiv A (AbelianScheme.TateComparison.End.endToRational A f) = (1 : ℚ) ⊗ₜ[ℤ] integralEquiv A f :=
  rationalEquiv_tmul A 1 f

/-- An actual TateComparison denominator clearing is the identical clearing in
the endomorphism algebra used by GeometricComparison's Hecke realization. -/
theorem transports_clearing (n : ℕ) (a : AbelianScheme.TateComparison.End.IntegralEnd A) (f : AbelianScheme.TateComparison.End.RationalEnd A)
    (h : n • f = AbelianScheme.TateComparison.End.endToRational A a) :
    n • rationalEquiv A f = (1 : ℚ) ⊗ₜ[ℤ] integralEquiv A a := by
  exact (map_nsmul (rationalEquiv A) n f).symm.trans
    ((congrArg (rationalEquiv A) h).trans (rationalEquiv_integral A a))

end

end OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.EndomorphismComparison.CM
