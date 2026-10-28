import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Intrinsic.IntegralMaps
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.SingularPeriodEquiv

/-! # Period Squares -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Intrinsic.PeriodSquares.IntrinsicLinearMaps

noncomputable section

/-! The unique native linear lift gives an actual commuting square
between the vector-space coverings, lattice quotients and algebraic
complex-point spaces. All maps use the existing period homeomorphisms. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.AbelianUniformizationEq.Constructions.AbelianUniformization
open scoped _root_.CategoryTheory.MonObj

def nativePeriodMap (A : ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety) : HodgeConjecture.DegreeTwo.SingularPeriodsD.Constructions.SingularPeriods.Base (HodgeConjecture.DegreeTwo.AbelianUniformizationEq.Constructions.AbelianUniformization.periodLattice A) ⟶ Betti.Scheme.schemePointSpace A.toOver :=
  TopCat.ofHom ⟨HodgeConjecture.DegreeTwo.AbelianUniformizationEq.Constructions.AbelianUniformization.periodHomeomorph Torsion.IntrinsicTorsion.e06Input A, (HodgeConjecture.DegreeTwo.AbelianUniformizationEq.Constructions.AbelianUniformization.periodHomeomorph Torsion.IntrinsicTorsion.e06Input A).continuous⟩

def nativePeriodInverseMap (A : ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety) : Betti.Scheme.schemePointSpace A.toOver ⟶ HodgeConjecture.DegreeTwo.SingularPeriodsD.Constructions.SingularPeriods.Base (HodgeConjecture.DegreeTwo.AbelianUniformizationEq.Constructions.AbelianUniformization.periodLattice A) :=
  TopCat.ofHom ⟨(HodgeConjecture.DegreeTwo.AbelianUniformizationEq.Constructions.AbelianUniformization.periodHomeomorph Torsion.IntrinsicTorsion.e06Input A).symm,
    (HodgeConjecture.DegreeTwo.AbelianUniformizationEq.Constructions.AbelianUniformization.periodHomeomorph Torsion.IntrinsicTorsion.e06Input A).symm.continuous⟩

def nativeTorusPointMap {A B : ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety} (f : A.toOver ⟶ B.toOver) :
    HodgeConjecture.DegreeTwo.SingularPeriodsD.Constructions.SingularPeriods.Base (HodgeConjecture.DegreeTwo.AbelianUniformizationEq.Constructions.AbelianUniformization.periodLattice A) ⟶ HodgeConjecture.DegreeTwo.SingularPeriodsD.Constructions.SingularPeriods.Base (HodgeConjecture.DegreeTwo.AbelianUniformizationEq.Constructions.AbelianUniformization.periodLattice B) :=
  nativePeriodMap A ≫ TopCat.ofHom (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.mapContinuous f) ≫ nativePeriodInverseMap B

def nativeCoverLinearMap {A B : ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety} (f : A.toOver ⟶ B.toOver) [IsMonHom f] :
    HodgeConjecture.DegreeTwo.SingularPeriodsD.Constructions.SingularPeriods.Cover (V := HodgeConjecture.DegreeTwo.Transport.Constructions.AbelianModel A) ⟶ HodgeConjecture.DegreeTwo.SingularPeriodsD.Constructions.SingularPeriods.Cover (V := HodgeConjecture.DegreeTwo.Transport.Constructions.AbelianModel B) :=
  TopCat.ofHom ⟨Maps.IntrinsicLinearMaps.linearLift f, (Maps.IntrinsicLinearMaps.linearLift f).continuous_of_finiteDimensional⟩

theorem nativeCoverLinearMap_zero {A B : ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety} (f : A.toOver ⟶ B.toOver) [IsMonHom f] :
    nativeCoverLinearMap f 0 = 0 := (Maps.IntrinsicLinearMaps.linearLift f).map_zero

theorem nativeCover_period_square {A B : ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety} (f : A.toOver ⟶ B.toOver) [IsMonHom f] :
    HodgeConjecture.DegreeTwo.SingularPeriodsD.Constructions.SingularPeriods.projection (HodgeConjecture.DegreeTwo.AbelianUniformizationEq.Constructions.AbelianUniformization.periodLattice A) ≫ nativeTorusPointMap f =
      nativeCoverLinearMap f ≫ HodgeConjecture.DegreeTwo.SingularPeriodsD.Constructions.SingularPeriods.projection (HodgeConjecture.DegreeTwo.AbelianUniformizationEq.Constructions.AbelianUniformization.periodLattice B) := by
  apply TopCat.ext
  intro v
  have h := congrArg (HodgeConjecture.DegreeTwo.AbelianUniformizationEq.Constructions.AbelianUniformization.periodHomeomorph Torsion.IntrinsicTorsion.e06Input B).symm (Maps.IntrinsicLinearMaps.linearLift_period f v)
  exact h.trans ((HodgeConjecture.DegreeTwo.AbelianUniformizationEq.Constructions.AbelianUniformization.periodHomeomorph Torsion.IntrinsicTorsion.e06Input B).symm_apply_apply _)

theorem nativePeriod_map_square {A B : ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety} (f : A.toOver ⟶ B.toOver) :
    nativePeriodMap A ≫ TopCat.ofHom (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.mapContinuous f) =
      nativeTorusPointMap f ≫ nativePeriodMap B := by
  apply TopCat.ext
  intro v
  exact ((HodgeConjecture.DegreeTwo.AbelianUniformizationEq.Constructions.AbelianUniformization.periodHomeomorph Torsion.IntrinsicTorsion.e06Input B).apply_symm_apply _).symm

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Intrinsic.PeriodSquares.IntrinsicLinearMaps
