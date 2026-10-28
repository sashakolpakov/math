import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.TorsionCongruence
import OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.AbelianUniformizationEq
import OAI.AlgebraicGeometry.ComplexGroups.HolomorphicAlgebraicity.ProjectiveGraph

/-! # Torsion -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Intrinsic.Torsion.IntrinsicTorsion

noncomputable section

/-! Standard torsion of actual complex abelian varieties, obtained from
the native exponential and its proved full period lattice. HolomorphicAlgebraicity is used
through its checked proof, not through an additional theorem assumption. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj

open OAI.AlgebraicGeometry.ComplexGroups.HolomorphicAlgebraicity.ProjectiveGraph.CM
open OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.AbelianUniformizationEq.Constructions.AbelianUniformization
open OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.TorsionCongruence.TorusTorsion

theorem e06Input : HodgeConjecture.DegreeTwo.Transport.Constructions.HolomorphicAlgebraicityInput := ComplexGroups.HolomorphicAlgebraicity.ProjectiveGraph.CM.holomorphic_group_hom_is_algebraic

variable (A : ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety)

local instance : IsIntegral A.toOver.left := A.variety.property
local instance : Smooth A.toOver.hom := A.variety.presentation.smooth
local instance : ConnectedSpace (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints A.toOver) := HodgeConjecture.DegreeTwo.AbelianUniformizationEq.Constructions.AbelianUniformization.native_connectedSpace e06Input A
local instance : IsZLattice ℝ (HodgeConjecture.DegreeTwo.AbelianUniformizationEq.Constructions.AbelianUniformization.periodLattice A) := HodgeConjecture.DegreeTwo.AbelianUniformizationEq.Constructions.AbelianUniformization.periodLattice_full e06Input A
local instance : Module.Finite ℤ (HodgeConjecture.DegreeTwo.AbelianUniformizationEq.Constructions.AbelianUniformization.periodLattice A) := ZLattice.module_finite ℝ (HodgeConjecture.DegreeTwo.AbelianUniformizationEq.Constructions.AbelianUniformization.periodLattice A)
local instance : Module.Free ℤ (HodgeConjecture.DegreeTwo.AbelianUniformizationEq.Constructions.AbelianUniformization.periodLattice A) := ZLattice.module_free ℝ (HodgeConjecture.DegreeTwo.AbelianUniformizationEq.Constructions.AbelianUniformization.periodLattice A)

/-- The actual exponential gives an additive group isomorphism from its
period quotient to the native complex-point group. -/
def nativePeriodAddEquiv :
    (HodgeConjecture.DegreeTwo.Transport.Constructions.AbelianModel A ⧸ (HodgeConjecture.DegreeTwo.AbelianUniformizationEq.Constructions.AbelianUniformization.periodLattice A).toAddSubgroup) ≃+
      Additive (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints A.toOver) :=
  QuotientAddGroup.quotientKerEquivOfSurjective
    (HodgeConjecture.DegreeTwo.ExponentialLocal.Constructions.Exponential.expAddHom (E := HodgeConjecture.DegreeTwo.Transport.Constructions.AbelianModel A) (C := ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints A.toOver))
    (HodgeConjecture.DegreeTwo.ExponentialLocal.Constructions.Exponential.expMap_surjective (E := HodgeConjecture.DegreeTwo.Transport.Constructions.AbelianModel A) (C := ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints A.toOver))

theorem period_rank : Module.finrank ℤ (HodgeConjecture.DegreeTwo.AbelianUniformizationEq.Constructions.AbelianUniformization.periodLattice A) =
    2 * Betti.AffineDimension.Realization.functionFieldDifferentialDimension A.toOver.hom := by
  rw [ZLattice.rank ℝ (HodgeConjecture.DegreeTwo.AbelianUniformizationEq.Constructions.AbelianUniformization.periodLattice A)]
  simp only [HodgeConjecture.DegreeTwo.Transport.Constructions.AbelianModel, Module.finrank_pi_fintype, Complex.finrank_real_complex,
    Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul]
  omega

def periodBasis : Module.Basis
    (Fin (2 * Betti.AffineDimension.Realization.functionFieldDifferentialDimension A.toOver.hom)) ℤ (HodgeConjecture.DegreeTwo.AbelianUniformizationEq.Constructions.AbelianUniformization.periodLattice A) :=
  (Module.finBasis ℤ (HodgeConjecture.DegreeTwo.AbelianUniformizationEq.Constructions.AbelianUniformization.periodLattice A)).reindex (finCongr (period_rank A))

/-- Native complex torsion has the standard free Z/N module of rank
twice the complex dimension, for every nonzero N. -/
def nativeTorsionEquiv (N : ℕ) [NeZero N] :
    (Fin (2 * Betti.AffineDimension.Realization.functionFieldDifferentialDimension A.toOver.hom) → ZMod N) ≃+
      TorsionCongruence.TorusTorsion.killedBy (Additive (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints A.toOver)) N :=
  (TorsionCongruence.TorusTorsion.latticeTorsionEquiv (HodgeConjecture.DegreeTwo.AbelianUniformizationEq.Constructions.AbelianUniformization.periodLattice A) (periodBasis A) N).trans
    (TorsionCongruence.TorusTorsion.killedByEquiv (nativePeriodAddEquiv A) N)

theorem nativeTorsion_card (N : ℕ) [NeZero N] :
    Nat.card (TorsionCongruence.TorusTorsion.killedBy (Additive (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints A.toOver)) N) =
      N ^ (2 * Betti.AffineDimension.Realization.functionFieldDifferentialDimension A.toOver.hom) := by
  rw [← Nat.card_congr (nativeTorsionEquiv A N).toEquiv]
  simp only [Nat.card_fun, Nat.card_zmod, Nat.card_fin]

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Intrinsic.Torsion.IntrinsicTorsion
