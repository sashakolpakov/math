import OAI.NumberTheory.PadicHodge.GeometricComparison.FirstThree.ThreeComplex
import OAI.NumberTheory.PadicHodge.GeometricComparison.TruncationBoundsGE
import Mathlib.Algebra.Homology.ShortComplex.ShortExact
import Mathlib.Algebra.Homology.HomologicalComplexAbelian

/-! # Quotient -/

namespace OAI.NumberTheory.PadicHodge.GeometricComparison.FirstThree.Quotient.FirstThreeComplex

noncomputable section

/-! The discarded tail begins in degree three and forms the actual kernel of the three-term quotient. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits ZeroObject

universe u v

variable {C : Type u} [Category.{v} C] [Abelian C] (K : CochainComplex C ℕ)

theorem tail_projection : AlgebraicGeometry.Crystalline.Cohomology.HodgeFiltrationD.HodgeFiltration.inclusion K 3 ≫ ThreeComplex.FirstThreeComplex.projection K = 0 := by
  apply HomologicalComplex.Hom.ext
  funext n
  rcases n with _ | (_ | (_ | n))
  · change AlgebraicGeometry.Crystalline.Cohomology.HodgeFiltrationD.HodgeFiltration.inclusionTerm K 3 0 ≫ 𝟙 (K.X 0) = 0
    rw [AlgebraicGeometry.Crystalline.Cohomology.HodgeFiltrationD.HodgeFiltration.inclusionTerm, dite_eq_right (show ¬ (3 : ℤ) ≤ (0 : ℕ) by omega)]
    exact zero_comp
  · change AlgebraicGeometry.Crystalline.Cohomology.HodgeFiltrationD.HodgeFiltration.inclusionTerm K 3 1 ≫ 𝟙 (K.X 1) = 0
    rw [AlgebraicGeometry.Crystalline.Cohomology.HodgeFiltrationD.HodgeFiltration.inclusionTerm, dite_eq_right (show ¬ (3 : ℤ) ≤ (1 : ℕ) by omega)]
    exact zero_comp
  · change AlgebraicGeometry.Crystalline.Cohomology.HodgeFiltrationD.HodgeFiltration.inclusionTerm K 3 2 ≫ 𝟙 (K.X 2) = 0
    rw [AlgebraicGeometry.Crystalline.Cohomology.HodgeFiltrationD.HodgeFiltration.inclusionTerm, dite_eq_right (show ¬ (3 : ℤ) ≤ (2 : ℕ) by omega)]
    exact zero_comp
  · exact comp_zero

def quotientSequence : ShortComplex (CochainComplex C ℕ) :=
  ShortComplex.mk (AlgebraicGeometry.Crystalline.Cohomology.HodgeFiltrationD.HodgeFiltration.inclusion K 3) (ThreeComplex.FirstThreeComplex.projection K) (tail_projection K)

theorem tail_zero (n : ℕ) (hn : n ≤ 2) : IsZero ((AlgebraicGeometry.Crystalline.Cohomology.HodgeFiltrationD.HodgeFiltration.brutal K 3).X n) := by
  change IsZero (AlgebraicGeometry.Crystalline.Cohomology.HodgeFiltrationD.HodgeFiltration.term K 3 n)
  rw [AlgebraicGeometry.Crystalline.Cohomology.HodgeFiltrationD.HodgeFiltration.term, ite_eq_right (show ¬ (3 : ℤ) ≤ (n : ℤ) by omega)]
  exact isZero_zero C

theorem tail_inclusion_isIso (n : ℕ) (hn : 3 ≤ n) : IsIso ((AlgebraicGeometry.Crystalline.Cohomology.HodgeFiltrationD.HodgeFiltration.inclusion K 3).f n) := by
  change IsIso (AlgebraicGeometry.Crystalline.Cohomology.HodgeFiltrationD.HodgeFiltration.inclusionTerm K 3 n)
  rw [AlgebraicGeometry.Crystalline.Cohomology.HodgeFiltrationD.HodgeFiltration.inclusionTerm, dite_eq_left (show (3 : ℤ) ≤ (n : ℤ) by omega)]
  infer_instance

def quotientSplitting (n : ℕ) :
    ((quotientSequence K).map (HomologicalComplex.eval C (.up ℕ) n)).Splitting := by
  rcases n with _ | (_ | (_ | n))
  · apply ShortComplex.Splitting.ofIsZeroOfIsIso _ (tail_zero K 0 (by omega))
    exact inferInstanceAs (IsIso (𝟙 (K.X 0)))
  · apply ShortComplex.Splitting.ofIsZeroOfIsIso _ (tail_zero K 1 (by omega))
    exact inferInstanceAs (IsIso (𝟙 (K.X 1)))
  · apply ShortComplex.Splitting.ofIsZeroOfIsIso _ (tail_zero K 2 (by omega))
    exact inferInstanceAs (IsIso (𝟙 (K.X 2)))
  · exact ShortComplex.Splitting.ofIsIsoOfIsZero _ (tail_inclusion_isIso K (n + 3) (by omega))
      (isZero_zero C)

theorem quotient_shortExact : (quotientSequence K).ShortExact :=
  HomologicalComplex.shortExact_of_degreewise_shortExact _ (fun n => (quotientSplitting K n).shortExact)

end

end OAI.NumberTheory.PadicHodge.GeometricComparison.FirstThree.Quotient.FirstThreeComplex
