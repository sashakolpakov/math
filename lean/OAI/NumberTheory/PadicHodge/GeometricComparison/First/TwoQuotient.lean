import OAI.NumberTheory.PadicHodge.GeometricComparison.First.TwoFunctor
import OAI.NumberTheory.PadicHodge.GeometricComparison.TruncationBoundsGE
import Mathlib.Algebra.Homology.ShortComplex.ShortExact

/-! # Two Quotient -/

namespace OAI.NumberTheory.PadicHodge.GeometricComparison.First.TwoQuotient.FirstTwoComplex

noncomputable section

/-! The tail in degrees at least two is the kernel of the projection to the first two terms. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits ZeroObject

universe u v

variable {C : Type u} [Category.{v} C] [Abelian C] (K : CochainComplex C ℕ)

theorem tail_projection : AlgebraicGeometry.Crystalline.Cohomology.HodgeFiltrationD.HodgeFiltration.inclusion K 2 ≫ TwoComplex.FirstTwoComplex.projection K = 0 := by
  apply HomologicalComplex.Hom.ext
  funext n
  cases n with
  | zero =>
    change AlgebraicGeometry.Crystalline.Cohomology.HodgeFiltrationD.HodgeFiltration.inclusionTerm K 2 0 ≫ 𝟙 (K.X 0) = 0
    rw [AlgebraicGeometry.Crystalline.Cohomology.HodgeFiltrationD.HodgeFiltration.inclusionTerm, dite_eq_right (show ¬ (2 : ℤ) ≤ (0 : ℕ) by omega)]
    exact zero_comp
  | succ n =>
    cases n with
    | zero =>
      change AlgebraicGeometry.Crystalline.Cohomology.HodgeFiltrationD.HodgeFiltration.inclusionTerm K 2 1 ≫ 𝟙 (K.X 1) = 0
      rw [AlgebraicGeometry.Crystalline.Cohomology.HodgeFiltrationD.HodgeFiltration.inclusionTerm, dite_eq_right (show ¬ (2 : ℤ) ≤ (1 : ℕ) by omega)]
      exact zero_comp
    | succ n => exact comp_zero

def quotientSequence : ShortComplex (CochainComplex C ℕ) :=
  ShortComplex.mk (AlgebraicGeometry.Crystalline.Cohomology.HodgeFiltrationD.HodgeFiltration.inclusion K 2) (TwoComplex.FirstTwoComplex.projection K) (tail_projection K)

theorem tail_zero (n : ℕ) (hn : n ≤ 1) : IsZero ((AlgebraicGeometry.Crystalline.Cohomology.HodgeFiltrationD.HodgeFiltration.brutal K 2).X n) := by
  change IsZero (AlgebraicGeometry.Crystalline.Cohomology.HodgeFiltrationD.HodgeFiltration.term K 2 n)
  have h : ¬ (2 : ℤ) ≤ (n : ℤ) := by omega
  rw [AlgebraicGeometry.Crystalline.Cohomology.HodgeFiltrationD.HodgeFiltration.term, ite_eq_right h]
  exact isZero_zero C

theorem tail_inclusion_isIso (n : ℕ) (hn : 2 ≤ n) : IsIso ((AlgebraicGeometry.Crystalline.Cohomology.HodgeFiltrationD.HodgeFiltration.inclusion K 2).f n) := by
  change IsIso (AlgebraicGeometry.Crystalline.Cohomology.HodgeFiltrationD.HodgeFiltration.inclusionTerm K 2 n)
  rw [AlgebraicGeometry.Crystalline.Cohomology.HodgeFiltrationD.HodgeFiltration.inclusionTerm, dite_eq_left (show (2 : ℤ) ≤ (n : ℤ) by omega)]
  infer_instance

def quotientSplitting (n : ℕ) :
    ((quotientSequence K).map (HomologicalComplex.eval C (.up ℕ) n)).Splitting := by
  cases n with
  | zero =>
    apply ShortComplex.Splitting.ofIsZeroOfIsIso _ (tail_zero K 0 (by omega))
    exact inferInstanceAs (IsIso (𝟙 (K.X 0)))
  | succ n =>
    cases n with
    | zero =>
      apply ShortComplex.Splitting.ofIsZeroOfIsIso _ (tail_zero K 1 (by omega))
      exact inferInstanceAs (IsIso (𝟙 (K.X 1)))
    | succ n =>
      exact ShortComplex.Splitting.ofIsIsoOfIsZero _ (tail_inclusion_isIso K (n + 2) (by omega))
        (isZero_zero C)

theorem quotient_shortExact : (quotientSequence K).ShortExact :=
  HomologicalComplex.shortExact_of_degreewise_shortExact _ (fun n => (quotientSplitting K n).shortExact)

end

end OAI.NumberTheory.PadicHodge.GeometricComparison.First.TwoQuotient.FirstTwoComplex
