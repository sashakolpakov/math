import OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.IntegralReducedBaseIso
import OAI.NumberTheory.PadicHodge.GeometricComparison.IdealQuotientOf

/-! # Reduced Base Coefficient Level -/

namespace OAI

noncomputable section

namespace NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.ReducedBaseCoefficientLevel.IntrinsicPadicReducedBaseCoefficientLevel

/-! The actual Witt/p-adic coefficient quotient isomorphisms commute
with their canonical prime-power transitions. -/

open _root_.CategoryTheory

variable (p : ℕ) [Fact p.Prime] (n m : ℕ) (hnm : n ≤ m)

local notation "W" => WittVector p (ZMod p)
local notation "IW" => fun q : ℕ => (Ideal.span {(p : WittVector p (ZMod p))}) ^ (q + 1)
local notation "IZ" => fun q : ℕ => (Ideal.span {(p : ℤ_[p])}) ^ (q + 1)
local notation "G" => ModuleCat.restrictScalars (RingEquiv.toRingHom (WittVector.equiv p))
local instance coefficients : Algebra W ℤ_[p] := WittAlgebra.PadicWittAlgebra.coefficientAlgebra p

theorem natural : (IntegralReducedBaseIso.IntrinsicPadicIntegralReducedBaseIso.coefficientIso p m).hom ≫
    Functor.whiskerRight (IntegralComparison.Module.IdealQuotientTransition.transformation ℤ_[p] (IZ m) (IZ n)
      (Ideal.pow_le_pow_right (Nat.add_le_add_right hnm 1))) G =
    Functor.whiskerLeft G (IntegralComparison.Module.IdealQuotientTransition.transformation W (IW m) (IW n)
      (Ideal.pow_le_pow_right (Nat.add_le_add_right hnm 1))) ≫
        (IntegralReducedBaseIso.IntrinsicPadicIntegralReducedBaseIso.coefficientIso p n).hom :=
  IdealQuotientOf.IdealQuotientRestrictionLevel.naturalOfEq W ℤ_[p] (IW m) (IW n)
    (Ideal.pow_le_pow_right (Nat.add_le_add_right hnm 1)) (IZ m) (IZ n)
    (IntegralReducedBaseIso.IntrinsicPadicIntegralReducedBaseIso.ideal_map p m) (IntegralReducedBaseIso.IntrinsicPadicIntegralReducedBaseIso.ideal_map p n)
    (Ideal.pow_le_pow_right (Nat.add_le_add_right hnm 1))

end NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.ReducedBaseCoefficientLevel.IntrinsicPadicReducedBaseCoefficientLevel

namespace NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.ReducedBaseCoefficientLevel.IntrinsicPadicReducedBaseComplexLevel

/-! The original Witt/p-adic quotient isomorphisms commute with level
transitions on actual cochain complexes. -/

open _root_.CategoryTheory

variable (p : ℕ) [Fact p.Prime] (n m : ℕ) (hnm : n ≤ m)
  (K : CochainComplex (ModuleCat.{0} ℤ_[p]) ℕ)

local notation "W" => WittVector p (ZMod p)
local notation "IW" => fun q : ℕ => (Ideal.span {(p : WittVector p (ZMod p))}) ^ (q + 1)
local notation "IZ" => fun q : ℕ => (Ideal.span {(p : ℤ_[p])}) ^ (q + 1)
local notation "G" => ModuleCat.restrictScalars (RingEquiv.toRingHom (WittVector.equiv p))

theorem natural : ((NatIso.mapHomologicalComplex
    (IntegralReducedBaseIso.IntrinsicPadicIntegralReducedBaseIso.coefficientIso p m) (.up ℕ)).app K).hom ≫
      ((G).mapHomologicalComplex (.up ℕ)).map
        (IntegralComparison.Module.IdealQuotientTransition.complexMap ℤ_[p] (IZ m) (IZ n)
          (Ideal.pow_le_pow_right (Nat.add_le_add_right hnm 1)) K) =
    IntegralComparison.Module.IdealQuotientTransition.complexMap W (IW m) (IW n)
      (Ideal.pow_le_pow_right (Nat.add_le_add_right hnm 1)) (((G).mapHomologicalComplex (.up ℕ)).obj K) ≫
        ((NatIso.mapHomologicalComplex
          (IntegralReducedBaseIso.IntrinsicPadicIntegralReducedBaseIso.coefficientIso p n) (.up ℕ)).app K).hom := by
  apply HomologicalComplex.Hom.ext
  funext i
  exact congrArg (fun q => q.app (K.X i)) (IntrinsicPadicReducedBaseCoefficientLevel.natural p n m hnm)

end NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.ReducedBaseCoefficientLevel.IntrinsicPadicReducedBaseComplexLevel

end

end OAI
