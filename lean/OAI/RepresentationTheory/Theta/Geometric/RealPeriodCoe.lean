import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Intrinsic.PeriodSquares

/-! # Real Period Coe -/

namespace OAI.RepresentationTheory.Theta.Geometric.RealPeriodCoe

noncomputable section

/-! A genuine real linear map preserving the full native lattice
induces its actual rational period map. A commuting exponential square
is retained for continuous maps between the native point spaces. -/

set_option backward.isDefEq.respectTransparency false
open _root_.CategoryTheory _root_.AlgebraicGeometry
open OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.AbelianUniformizationEq.Constructions.AbelianUniformization

namespace RealPeriodMaps
open OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Intrinsic.PeriodSquares.IntrinsicLinearMaps

local instance realPeriodMaps_integral (A : AlgebraicGeometry.ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety) : IsIntegral A.toOver.left := A.variety.property

variable {A B : AlgebraicGeometry.ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety} (T : AlgebraicGeometry.HodgeConjecture.DegreeTwo.Transport.Constructions.AbelianModel A →L[ℝ] AlgebraicGeometry.HodgeConjecture.DegreeTwo.Transport.Constructions.AbelianModel B)
    (hT : ∀ v ∈ AlgebraicGeometry.HodgeConjecture.DegreeTwo.AbelianUniformizationEq.Constructions.AbelianUniformization.periodLattice A, T v ∈ AlgebraicGeometry.HodgeConjecture.DegreeTwo.AbelianUniformizationEq.Constructions.AbelianUniformization.periodLattice B)

include hT in
theorem preserves_rational (v : AlgebraicGeometry.HodgeConjecture.DegreeTwo.Transport.Constructions.AbelianModel A) (hv : v ∈ AlgebraicGeometry.AbelianModuli.ReferenceFamily.Intrinsic.RationalPeriods.IntrinsicRationalPeriods.rationalPeriods A) :
    T v ∈ AlgebraicGeometry.AbelianModuli.ReferenceFamily.Intrinsic.RationalPeriods.IntrinsicRationalPeriods.rationalPeriods B := by
  induction hv using Submodule.span_induction with
  | mem v hv => exact Submodule.subset_span (hT v hv)
  | zero => exact T.map_zero.symm ▸ (AlgebraicGeometry.AbelianModuli.ReferenceFamily.Intrinsic.RationalPeriods.IntrinsicRationalPeriods.rationalPeriods B).zero_mem
  | add v w _ _ hv hw => exact (T.map_add v w).symm ▸ (AlgebraicGeometry.AbelianModuli.ReferenceFamily.Intrinsic.RationalPeriods.IntrinsicRationalPeriods.rationalPeriods B).add_mem hv hw
  | smul q v _ hv => exact ((T.restrictScalars ℚ).map_smul q v).symm ▸ (AlgebraicGeometry.AbelianModuli.ReferenceFamily.Intrinsic.RationalPeriods.IntrinsicRationalPeriods.rationalPeriods B).smul_mem q hv

def rationalMap : AlgebraicGeometry.AbelianModuli.ReferenceFamily.Intrinsic.RationalPeriods.IntrinsicRationalPeriods.rationalPeriods A →ₗ[ℚ] AlgebraicGeometry.AbelianModuli.ReferenceFamily.Intrinsic.RationalPeriods.IntrinsicRationalPeriods.rationalPeriods B :=
  (((T.restrictScalars ℚ).toLinearMap).domRestrict (AlgebraicGeometry.AbelianModuli.ReferenceFamily.Intrinsic.RationalPeriods.IntrinsicRationalPeriods.rationalPeriods A)).codRestrict
    (AlgebraicGeometry.AbelianModuli.ReferenceFamily.Intrinsic.RationalPeriods.IntrinsicRationalPeriods.rationalPeriods B) (fun v => preserves_rational T hT v.val v.property)

theorem rationalMap_coe (v : AlgebraicGeometry.AbelianModuli.ReferenceFamily.Intrinsic.RationalPeriods.IntrinsicRationalPeriods.rationalPeriods A) : (rationalMap T hT v).val = T v.val := rfl

def coverMap : AlgebraicGeometry.HodgeConjecture.DegreeTwo.SingularPeriodsD.Constructions.SingularPeriods.Cover (V := AlgebraicGeometry.HodgeConjecture.DegreeTwo.Transport.Constructions.AbelianModel A) ⟶ AlgebraicGeometry.HodgeConjecture.DegreeTwo.SingularPeriodsD.Constructions.SingularPeriods.Cover (V := AlgebraicGeometry.HodgeConjecture.DegreeTwo.Transport.Constructions.AbelianModel B) :=
  TopCat.ofHom ⟨T, T.continuous⟩

def torusMap (f : AlgebraicGeometry.Betti.Scheme.schemePointSpace A.toOver ⟶ AlgebraicGeometry.Betti.Scheme.schemePointSpace B.toOver) :
    AlgebraicGeometry.HodgeConjecture.DegreeTwo.SingularPeriodsD.Constructions.SingularPeriods.Base (AlgebraicGeometry.HodgeConjecture.DegreeTwo.AbelianUniformizationEq.Constructions.AbelianUniformization.periodLattice A) ⟶ AlgebraicGeometry.HodgeConjecture.DegreeTwo.SingularPeriodsD.Constructions.SingularPeriods.Base (AlgebraicGeometry.HodgeConjecture.DegreeTwo.AbelianUniformizationEq.Constructions.AbelianUniformization.periodLattice B) :=
  AlgebraicGeometry.AbelianModuli.ReferenceFamily.Intrinsic.PeriodSquares.IntrinsicLinearMaps.nativePeriodMap A ≫ f ≫ AlgebraicGeometry.AbelianModuli.ReferenceFamily.Intrinsic.PeriodSquares.IntrinsicLinearMaps.nativePeriodInverseMap B

theorem period_square (f : AlgebraicGeometry.Betti.Scheme.schemePointSpace A.toOver ⟶ AlgebraicGeometry.Betti.Scheme.schemePointSpace B.toOver) :
    AlgebraicGeometry.AbelianModuli.ReferenceFamily.Intrinsic.PeriodSquares.IntrinsicLinearMaps.nativePeriodMap A ≫ f = torusMap f ≫ AlgebraicGeometry.AbelianModuli.ReferenceFamily.Intrinsic.PeriodSquares.IntrinsicLinearMaps.nativePeriodMap B := by
  apply TopCat.ext
  intro v
  exact ((AlgebraicGeometry.HodgeConjecture.DegreeTwo.AbelianUniformizationEq.Constructions.AbelianUniformization.periodHomeomorph AlgebraicGeometry.AbelianModuli.ReferenceFamily.Intrinsic.Torsion.IntrinsicTorsion.e06Input B).apply_symm_apply _).symm

theorem cover_square (f : AlgebraicGeometry.Betti.Scheme.schemePointSpace A.toOver ⟶ AlgebraicGeometry.Betti.Scheme.schemePointSpace B.toOver)
    (hf : ∀ v : AlgebraicGeometry.HodgeConjecture.DegreeTwo.Transport.Constructions.AbelianModel A,
      f (AlgebraicGeometry.HodgeConjecture.DegreeTwo.AbelianUniformizationEq.Constructions.AbelianUniformization.periodHomeomorph AlgebraicGeometry.AbelianModuli.ReferenceFamily.Intrinsic.Torsion.IntrinsicTorsion.e06Input A (QuotientAddGroup.mk v)) =
        AlgebraicGeometry.HodgeConjecture.DegreeTwo.AbelianUniformizationEq.Constructions.AbelianUniformization.periodHomeomorph AlgebraicGeometry.AbelianModuli.ReferenceFamily.Intrinsic.Torsion.IntrinsicTorsion.e06Input B (QuotientAddGroup.mk (T v))) :
    AlgebraicGeometry.HodgeConjecture.DegreeTwo.SingularPeriodsD.Constructions.SingularPeriods.projection (AlgebraicGeometry.HodgeConjecture.DegreeTwo.AbelianUniformizationEq.Constructions.AbelianUniformization.periodLattice A) ≫ torusMap f = coverMap T ≫ AlgebraicGeometry.HodgeConjecture.DegreeTwo.SingularPeriodsD.Constructions.SingularPeriods.projection (AlgebraicGeometry.HodgeConjecture.DegreeTwo.AbelianUniformizationEq.Constructions.AbelianUniformization.periodLattice B) := by
  apply TopCat.ext
  intro v
  have h := congrArg (AlgebraicGeometry.HodgeConjecture.DegreeTwo.AbelianUniformizationEq.Constructions.AbelianUniformization.periodHomeomorph AlgebraicGeometry.AbelianModuli.ReferenceFamily.Intrinsic.Torsion.IntrinsicTorsion.e06Input B).symm (hf v)
  exact h.trans ((AlgebraicGeometry.HodgeConjecture.DegreeTwo.AbelianUniformizationEq.Constructions.AbelianUniformization.periodHomeomorph AlgebraicGeometry.AbelianModuli.ReferenceFamily.Intrinsic.Torsion.IntrinsicTorsion.e06Input B).symm_apply_apply _)

end RealPeriodMaps

end

end OAI.RepresentationTheory.Theta.Geometric.RealPeriodCoe
