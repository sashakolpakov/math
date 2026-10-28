import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.CrystallineMonoidAction
import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Ordinary.Polynomial
import Mathlib.Algebra.Algebra.Opposite

/-! # Crystalline End Action -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.CrystallineEndAction.CM

noncomputable section

/-! Rational endomorphisms act on actual crystalline H1 through the proved
group-law formula. Centrality of actual Frobenius transports its polynomial
through this contravariant action. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj TensorProduct
open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.CrystallineFunctoriality.CM

variable (q : ℕ) [Fact q.Prime]
  (A : Over (Spec (.of (ZMod q)))) [GrpObj A] [IsCommMonObj A]

local instance crystallineEndRing : Ring (Module.End ℚ_[q] (NumberTheory.PadicHodge.GeometricComparison.Crystalline.CoefficientAdapter.RationalH1 q A)) :=
  Module.End.instRing (R := ℚ_[q]) (N₁ := NumberTheory.PadicHodge.GeometricComparison.Crystalline.CoefficientAdapter.RationalH1 q A)

def ringAction (h : CrystallineMonoidAction.CM.End.GroupLawIdentity q A) :
    (FormalGeometry.Completion.Endomorphisms.Construction.AlgebraicEnd A)ᵐᵒᵖ →+* Module.End ℚ_[q] (NumberTheory.PadicHodge.GeometricComparison.Crystalline.CoefficientAdapter.RationalH1 q A) :=
  RingHom.mk' (α := (FormalGeometry.Completion.Endomorphisms.Construction.AlgebraicEnd A)ᵐᵒᵖ)
    (β := Module.End ℚ_[q] (NumberTheory.PadicHodge.GeometricComparison.Crystalline.CoefficientAdapter.RationalH1 q A)) (CrystallineMonoidAction.CM.End.monoidAction q A) (fun f g =>
    CrystallineMonoidAction.CM.End.pullback_mul_of_groupLaw q A h f.unop.toMul.hom.hom g.unop.toMul.hom.hom)

def rationalAction (h : CrystallineMonoidAction.CM.End.GroupLawIdentity q A) :
    (FormalGeometry.Completion.Endomorphisms.Construction.RationalAlgebraicEnd A)ᵐᵒᵖ →ₐ[ℚ] Module.End ℚ_[q] (NumberTheory.PadicHodge.GeometricComparison.Crystalline.CoefficientAdapter.RationalH1 q A) :=
  AlgHom.opComm ((AlgHom.liftEquiv ℤ ℚ (FormalGeometry.Completion.Endomorphisms.Construction.AlgebraicEnd A)
    (Module.End ℚ_[q] (NumberTheory.PadicHodge.GeometricComparison.Crystalline.CoefficientAdapter.RationalH1 q A))ᵐᵒᵖ)
      (AlgHom.opComm.symm (ringAction q A h).toIntAlgHom))

theorem rationalAction_tmul (h : CrystallineMonoidAction.CM.End.GroupLawIdentity q A) (r : ℚ) (f : FormalGeometry.Completion.Endomorphisms.Construction.AlgebraicEnd A) :
    rationalAction q A h (MulOpposite.op (r ⊗ₜ[ℤ] f)) =
      r • NumberTheory.PadicHodge.GeometricComparison.Crystalline.CoefficientAdapter.rationalPullback q f.toMul.hom.hom := rfl

theorem rationalAction_frobenius (h : CrystallineMonoidAction.CM.End.GroupLawIdentity q A) :
    rationalAction q A h (MulOpposite.op (FormalGeometry.Completion.Endomorphisms.Construction.rationalAlgebraicFrobenius (ZMod q) A)) =
      NumberTheory.PadicHodge.GeometricComparison.Crystalline.CoefficientAdapter.rationalPullback q (FormalGeometry.Completion.Frobenius.Construction.finiteFieldSchemeFrobenius (ZMod q) A) := by
  rw [FormalGeometry.Completion.Endomorphisms.Construction.rationalAlgebraicFrobenius, rationalAction_tmul, one_smul]
  rfl

omit [Fact q.Prime] in
theorem opposite_polynomial {R : Type*} [Ring R] (Phi : R) (T : Fin 3 → R)
    (hc : ∀ i, Commute Phi (T i))
    (hp : Ordinary.Polynomial.CM.heckePolynomialValue q Phi T = 0) :
    Ordinary.Polynomial.CM.heckePolynomialValue q (MulOpposite.op Phi)
      (fun i => MulOpposite.op (T i)) = 0 := by
  have h := congrArg MulOpposite.op hp
  simp only [Ordinary.Polynomial.CM.heckePolynomialValue, MulOpposite.op_sub,
    MulOpposite.op_add, MulOpposite.op_mul, MulOpposite.op_pow, MulOpposite.op_smul,
    MulOpposite.op_zero] at h ⊢
  rw [((hc 0).op.pow_left 2).eq, (hc 1).op.eq] at h
  exact h

theorem crystalline_polynomial (h : CrystallineMonoidAction.CM.End.GroupLawIdentity q A)
    (T : Fin 3 → FormalGeometry.Completion.Endomorphisms.Construction.RationalAlgebraicEnd A)
    (hp : Ordinary.Polynomial.CM.heckePolynomialValue q
      (FormalGeometry.Completion.Endomorphisms.Construction.rationalAlgebraicFrobenius (ZMod q) A) T = 0) :
    Ordinary.Polynomial.CM.heckePolynomialValue q
      (NumberTheory.PadicHodge.GeometricComparison.Crystalline.CoefficientAdapter.rationalPullback q (FormalGeometry.Completion.Frobenius.Construction.finiteFieldSchemeFrobenius (ZMod q) A))
      (fun i => rationalAction q A h (MulOpposite.op (T i))) = 0 := by
  have hop := opposite_polynomial q (FormalGeometry.Completion.Endomorphisms.Construction.rationalAlgebraicFrobenius (ZMod q) A) T
    (fun i => FormalGeometry.Completion.Endomorphisms.Construction.rationalAlgebraicFrobenius_commutes (ZMod q) A (T i)) hp
  have hmap := congrArg (rationalAction q A h) hop
  simpa only [Ordinary.Polynomial.CM.heckePolynomialValue, map_sub, map_add,
    map_mul, map_pow, map_nsmul, map_zero, rationalAction_frobenius] using hmap

end

end OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.CrystallineEndAction.CM
