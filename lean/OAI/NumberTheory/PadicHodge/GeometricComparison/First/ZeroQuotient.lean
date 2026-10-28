import OAI.NumberTheory.PadicHodge.GeometricComparison.TruncationBoundsGE
import Mathlib.Algebra.Homology.HomologicalComplexAbelian
import Mathlib.Algebra.Homology.Single

/-! # Zero Quotient -/

namespace OAI.NumberTheory.PadicHodge.GeometricComparison.First.ZeroQuotient.FirstZeroComplex

noncomputable section

/-! The native positive-degree Hodge tail is the kernel of projection to the degree-zero term. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits ZeroObject

universe u v

variable {C : Type u} [Category.{v} C] [Abelian C] (K : CochainComplex C ℕ)

def complex : CochainComplex C ℕ := (CochainComplex.single₀ C).obj (K.X 0)

def projection : K ⟶ complex K := (CochainComplex.toSingle₀Equiv K (K.X 0)).symm (𝟙 _)

theorem projection_zero : (projection K).f 0 = 𝟙 (K.X 0) :=
  CochainComplex.toSingle₀Equiv_symm_apply_f_zero _

theorem projection_succ (n : ℕ) : (projection K).f (n + 1) = 0 :=
  CochainComplex.toSingle₀Equiv_symm_apply_f_succ _ n

theorem tail_projection : AlgebraicGeometry.Crystalline.Cohomology.HodgeFiltrationD.HodgeFiltration.inclusion K 1 ≫ projection K = 0 := by
  apply HomologicalComplex.Hom.ext
  funext n
  cases n with
  | zero =>
    change AlgebraicGeometry.Crystalline.Cohomology.HodgeFiltrationD.HodgeFiltration.inclusionTerm K 1 0 ≫ (projection K).f 0 = 0
    rw [AlgebraicGeometry.Crystalline.Cohomology.HodgeFiltrationD.HodgeFiltration.inclusionTerm, dite_eq_right (show ¬ (1 : ℤ) ≤ (0 : ℕ) by omega)]
    exact zero_comp
  | succ n =>
    change (AlgebraicGeometry.Crystalline.Cohomology.HodgeFiltrationD.HodgeFiltration.inclusion K 1).f (n + 1) ≫ (projection K).f (n + 1) = 0
    rw [projection_succ, comp_zero]

def quotientSequence : ShortComplex (CochainComplex C ℕ) :=
  ShortComplex.mk (AlgebraicGeometry.Crystalline.Cohomology.HodgeFiltrationD.HodgeFiltration.inclusion K 1) (projection K) (tail_projection K)

theorem quotient_shortExact : (quotientSequence K).ShortExact := by
  apply HomologicalComplex.shortExact_of_degreewise_shortExact
  intro n
  cases n with
  | zero =>
    have ht : IsZero ((AlgebraicGeometry.Crystalline.Cohomology.HodgeFiltrationD.HodgeFiltration.brutal K 1).X 0) := by
      change IsZero (AlgebraicGeometry.Crystalline.Cohomology.HodgeFiltrationD.HodgeFiltration.term K 1 0)
      rw [AlgebraicGeometry.Crystalline.Cohomology.HodgeFiltrationD.HodgeFiltration.term, ite_eq_right (show ¬ (1 : ℤ) ≤ (0 : ℕ) by omega)]
      exact isZero_zero C
    apply ShortComplex.Splitting.shortExact
    apply ShortComplex.Splitting.ofIsZeroOfIsIso _ ht
    change IsIso ((projection K).f 0)
    rw [projection_zero]
    exact inferInstanceAs (IsIso (𝟙 (K.X 0)))
  | succ n =>
    have hi : IsIso ((AlgebraicGeometry.Crystalline.Cohomology.HodgeFiltrationD.HodgeFiltration.inclusion K 1).f (n + 1)) := by
      change IsIso (AlgebraicGeometry.Crystalline.Cohomology.HodgeFiltrationD.HodgeFiltration.inclusionTerm K 1 (n + 1))
      rw [AlgebraicGeometry.Crystalline.Cohomology.HodgeFiltrationD.HodgeFiltration.inclusionTerm, dite_eq_left (show (1 : ℤ) ≤ ((n + 1 : ℕ) : ℤ) by omega)]
      infer_instance
    exact (ShortComplex.Splitting.ofIsIsoOfIsZero _ hi
      (HomologicalComplex.isZero_single_obj_X (.up ℕ) 0 (K.X 0) (n + 1) (by omega))).shortExact

end

end OAI.NumberTheory.PadicHodge.GeometricComparison.First.ZeroQuotient.FirstZeroComplex
