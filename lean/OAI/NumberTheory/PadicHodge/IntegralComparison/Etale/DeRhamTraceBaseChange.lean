import OAI.NumberTheory.PadicHodge.IntegralComparison.Etale.DeRhamTraceCoordinates
import OAI.NumberTheory.PadicHodge.PeriodInvariants.AlgebraTraceBaseChange

/-! # De Rham Trace Base Change -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Etale.DeRhamTraceBaseChange

noncomputable section

/-! The native de Rham trace commutes with arbitrary cartesian changes of
étale charts, including affine open restrictions that are not principal. -/

open _root_.CategoryTheory
open scoped TensorProduct

universe u v w

section Coefficients

variable (A B C D : Type u) [CommRing A] [CommRing B] [CommRing C] [CommRing D]
  [Algebra A B] [Algebra A C] [Algebra B D] [Algebra C D] [Algebra A D]
  [IsScalarTower A B D] [IsScalarTower A C D]
  [Algebra.IsPushout A C B D] [Module.Free A B] [Module.Finite A B]

theorem coefficientTrace_baseChange (x : B) :
    Algebra.trace C D (algebraMap B D x) = algebraMap A C (Algebra.trace A B x) := by
  let e := Algebra.IsPushout.equiv A C B D
  have he : e (1 ⊗ₜ[A] x) = algebraMap B D x := by
    rw [Algebra.IsPushout.equiv_tmul, map_one, one_mul]
  rw [← he, Algebra.trace_eq_of_algEquiv e]
  exact PeriodInvariants.AlgebraTraceBaseChange.includeRight A B C x

end Coefficients

variable (R A B C D σ : Type u) [CommRing R] [CommRing A] [CommRing B]
  [CommRing C] [CommRing D]
  [Algebra R A] [Algebra R B] [Algebra R C] [Algebra R D]
  [Algebra A B] [Algebra A C] [Algebra B D] [Algebra C D] [Algebra A D]
  [IsScalarTower R A B] [IsScalarTower R A C] [IsScalarTower R B D]
  [IsScalarTower R C D] [IsScalarTower A B D] [IsScalarTower A C D]
  [Algebra (MvPolynomial σ R) A] [Algebra (MvPolynomial σ R) B]
  [Algebra (MvPolynomial σ R) C] [Algebra (MvPolynomial σ R) D]
  [IsScalarTower R (MvPolynomial σ R) A] [IsScalarTower R (MvPolynomial σ R) B]
  [IsScalarTower R (MvPolynomial σ R) C] [IsScalarTower R (MvPolynomial σ R) D]
  [IsScalarTower (MvPolynomial σ R) A B] [IsScalarTower (MvPolynomial σ R) A C]
  [IsScalarTower (MvPolynomial σ R) B D] [IsScalarTower (MvPolynomial σ R) C D]
  [Algebra.FormallyEtale (MvPolynomial σ R) A]
  [Algebra.FormallyEtale (MvPolynomial σ R) B]
  [Algebra.FormallyEtale (MvPolynomial σ R) C]
  [Algebra.FormallyEtale (MvPolynomial σ R) D]
  [Fintype σ] [LinearOrder σ]
  {ι : Type v} {κ : Type w} [Fintype ι] [Fintype κ]
  (b : Module.Basis ι A B) (c : Module.Basis κ C D)
  [Algebra.IsPushout A C B D]

theorem trace_baseChange :
    DeRhamTrace.trace R A B σ b ≫ DeRhamTrace.pullback R A C =
      DeRhamTrace.pullback R B D ≫ DeRhamTrace.trace R C D σ c := by
  let : Module.Free A B := Module.Free.of_basis b
  let : Module.Finite A B := Module.Finite.of_basis b
  apply DeRhamTraceNaturality.complexMap_ext R B σ
  intro n x v
  change (DeRhamTrace.pullback R A C).f n ((DeRhamTrace.trace R A B σ b).f n _) =
    (DeRhamTrace.trace R C D σ c).f n ((DeRhamTrace.pullback R B D).f n _)
  rw [DeRhamTrace.trace_coordinate_symbol, DeRhamTraceNaturality.pullback_coordinate_symbol R A C σ,
    DeRhamTraceNaturality.pullback_coordinate_symbol R B D σ, DeRhamTrace.trace_coordinate_symbol,
    coefficientTrace_baseChange A B C D]

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Etale.DeRhamTraceBaseChange
