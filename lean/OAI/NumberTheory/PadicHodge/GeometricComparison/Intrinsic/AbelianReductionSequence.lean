import OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicIntegral.ReductionExact
import OAI.NumberTheory.PadicHodge.GeometricComparison.Geometry

/-! # Abelian Reduction Sequence -/

namespace OAI.NumberTheory.PadicHodge.GeometricComparison.Intrinsic.AbelianReductionSequence.AbelianModel

noncomputable section

/-! Actual prime-reduction short exact sequences for the zero- and one-form sheaves of the GeometricComparison integral abelian model. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

variable {K : Type} [Field K] [NumberField K]
  {q : ℕ} [Fact q.Prime] {jq : K →+* ℚ_[q]} (A : Geometry.AbelianH1Model K q jq)

local instance : Algebra ℤ_[q] (ZMod q) := PadicInt.toZMod.toAlgebra

def _root_.OAI.NumberTheory.PadicHodge.GeometricComparison.Geometry.AbelianH1Model.integralReductionMorphism : A.specialFiber.scheme.left ⟶ A.integral.scheme.left :=
  pullback.fst A.integral.scheme.hom (Geometry.scalarBaseMap (PadicInt.toZMod : ℤ_[q] →+* ZMod q))

theorem _root_.OAI.NumberTheory.PadicHodge.GeometricComparison.Geometry.AbelianH1Model.integralReductionSquare :
    IsPullback A.integralReductionMorphism A.specialFiber.scheme.hom A.integral.scheme.hom
      (Spec.map (CommRingCat.ofHom (algebraMap ℤ_[q] (ZMod q)))) :=
  IsPullback.of_hasPullback _ _

theorem _root_.OAI.NumberTheory.PadicHodge.GeometricComparison.Geometry.AbelianH1Model.residue_prime_zero : algebraMap ℤ_[q] (ZMod q) (q : ℤ_[q]) = 0 := by
  rw [map_natCast, ZMod.natCast_self]

def _root_.OAI.NumberTheory.PadicHodge.GeometricComparison.Geometry.AbelianH1Model.integralFormReductionSequence (n : ℕ) : ShortComplex (AlgebraicGeometry.Crystalline.Cohomology.DeRhamGlobalId.DeRhamGlobal.Sheaves ℤ_[q] A.integral.scheme) :=
  (IntrinsicIntegral.ReductionExact.IntrinsicIntegralReductionExact.sequence ℤ_[q] (ZMod q) A.integral.scheme A.specialFiber.scheme
    A.integralReductionMorphism A.integralReductionSquare.w n (q : ℤ_[q])
      (Geometry.AbelianH1Model.residue_prime_zero (q := q))).map
    (presheafToSheaf (Opens.grothendieckTopology A.integral.scheme.left) (ModuleCat ℤ_[q]))

theorem _root_.OAI.NumberTheory.PadicHodge.GeometricComparison.Geometry.AbelianH1Model.integralFormReduction_shortExact (n : ℕ) (hn : n ≤ 1) :
    (A.integralFormReductionSequence n).ShortExact := by
  apply IntrinsicIntegral.ReductionExact.IntrinsicIntegralReductionExact.shortExact ℤ_[q] (ZMod q) A.integral.scheme A.specialFiber.scheme
    A.integralReductionMorphism A.integralReductionSquare.w A.integralReductionSquare
    (ZMod.ringHom_surjective PadicInt.toZMod) n hn (q : ℤ_[q]) (Geometry.AbelianH1Model.residue_prime_zero (q := q))
  · exact PadicInt.ker_toZMod.trans PadicInt.maximalIdeal_eq_span_p
  · exact IsRegular.of_ne_zero (Nat.cast_ne_zero.mpr (Fact.out : q.Prime).ne_zero)

end

end OAI.NumberTheory.PadicHodge.GeometricComparison.Intrinsic.AbelianReductionSequence.AbelianModel
