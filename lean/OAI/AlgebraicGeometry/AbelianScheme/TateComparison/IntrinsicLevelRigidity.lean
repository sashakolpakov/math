import OAI.AlgebraicGeometry.AbelianScheme.TateComparison.IntrinsicPositiveQuadratic
import OAI.AlgebraicGeometry.AbelianScheme.TateComparison.PositiveLatticeRigidity
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Intrinsic.LevelStabilizers

/-! # Intrinsic Level Rigidity -/

namespace OAI.AlgebraicGeometry.AbelianScheme.TateComparison.IntrinsicLevelRigidity

noncomputable section

/-! Positivity of the actual ample Chern form and native period
faithfulness prove rigidity of full-level algebraic automorphisms. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj

open OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.AbelianUniformizationEq.Constructions.AbelianUniformization

def nativeLinearLiftIso {A B : ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety}
    (e : A.toOver ≅ B.toOver) [IsMonHom e.hom] : HodgeConjecture.DegreeTwo.Transport.Constructions.AbelianModel A ≃ₗ[ℂ] HodgeConjecture.DegreeTwo.Transport.Constructions.AbelianModel B :=
  LinearEquiv.ofLinearMap (AbelianModuli.ReferenceFamily.Intrinsic.Maps.IntrinsicLinearMaps.linearLift e.hom) (AbelianModuli.ReferenceFamily.Intrinsic.Maps.IntrinsicLinearMaps.linearLift e.inv)
    ((AbelianModuli.ReferenceFamily.Intrinsic.Maps.IntrinsicLinearMaps.linearLift_comp e.inv e.hom).symm.trans
      ((AbelianModuli.ReferenceFamily.Intrinsic.Maps.IntrinsicLinearMaps.linearLift_congr _ _ e.inv_hom_id).trans (AbelianModuli.ReferenceFamily.Intrinsic.Maps.IntrinsicLinearMaps.linearLift_id B)))
    ((AbelianModuli.ReferenceFamily.Intrinsic.Maps.IntrinsicLinearMaps.linearLift_comp e.hom e.inv).symm.trans
      ((AbelianModuli.ReferenceFamily.Intrinsic.Maps.IntrinsicLinearMaps.linearLift_congr _ _ e.hom_inv_id).trans (AbelianModuli.ReferenceFamily.Intrinsic.Maps.IntrinsicLinearMaps.linearLift_id A)))

variable (A : ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety)
local instance : IsIntegral A.toOver.left := A.variety.property

theorem nativeChern_period_congruence_rigidity
    (L : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle A.toOver.left) (hL : L.IsAmple)
    (e : A.toOver ≅ A.toOver) [IsMonHom e.hom]
    (he : ∀ x y : AbelianModuli.ReferenceFamily.Intrinsic.RationalPeriods.IntrinsicRationalPeriods.rationalPeriods A,
      AbelianModuli.ReferenceFamily.Intrinsic.ChernPairing.nativeChernForm A L (AbelianModuli.ReferenceFamily.Intrinsic.IntegralMaps.IntrinsicLinearMaps.rationalLift e.hom x) (AbelianModuli.ReferenceFamily.Intrinsic.IntegralMaps.IntrinsicLinearMaps.rationalLift e.hom y) = AbelianModuli.ReferenceFamily.Intrinsic.ChernPairing.nativeChernForm A L x y)
    (N : ℕ) (hN : 3 ≤ N)
    (hcong : ∀ x ∈ HodgeConjecture.DegreeTwo.AbelianUniformizationEq.Constructions.AbelianUniformization.periodLattice A, ∃ y ∈ HodgeConjecture.DegreeTwo.AbelianUniformizationEq.Constructions.AbelianUniformization.periodLattice A,
      AbelianModuli.ReferenceFamily.Intrinsic.Maps.IntrinsicLinearMaps.linearLift e.hom x - x = (N : ℤ) • y) : e.hom = 𝟙 A.toOver := by
  let : IsZLattice ℝ (HodgeConjecture.DegreeTwo.AbelianUniformizationEq.Constructions.AbelianUniformization.periodLattice A) := HodgeConjecture.DegreeTwo.AbelianUniformizationEq.Constructions.AbelianUniformization.periodLattice_full AbelianModuli.ReferenceFamily.Intrinsic.Torsion.IntrinsicTorsion.e06Input A
  let f := (nativeLinearLiftIso e).restrictScalars ℝ
  have hspan : Submodule.span ℤ (Set.range (AbelianModuli.ReferenceFamily.Intrinsic.RationalPeriods.IntrinsicRationalPeriods.realPeriodBasis A)) = HodgeConjecture.DegreeTwo.AbelianUniformizationEq.Constructions.AbelianUniformization.periodLattice A :=
    (AbelianModuli.ReferenceFamily.Intrinsic.Torsion.IntrinsicTorsion.periodBasis A).ofZLatticeBasis_span ℝ
  have hpres : ∀ x ∈ Submodule.span ℤ (Set.range (AbelianModuli.ReferenceFamily.Intrinsic.RationalPeriods.IntrinsicRationalPeriods.realPeriodBasis A)),
      f x ∈ Submodule.span ℤ (Set.range (AbelianModuli.ReferenceFamily.Intrinsic.RationalPeriods.IntrinsicRationalPeriods.realPeriodBasis A)) := by
    intro x hx
    rw [hspan] at hx ⊢
    exact AbelianModuli.ReferenceFamily.Intrinsic.Maps.IntrinsicLinearMaps.linearLift_preserves e.hom x hx
  have hf : f = 1 := by
    apply PositiveLatticeRigidity.positiveLattice_congruence_eq_one (AbelianModuli.ReferenceFamily.Intrinsic.RationalPeriods.IntrinsicRationalPeriods.realPeriodBasis A) (IntrinsicPositiveQuadratic.nativeChernQuadratic A L)
      (IntrinsicPositiveQuadratic.nativeChernQuadratic_continuous A L) (IntrinsicPositiveQuadratic.nativeChernQuadratic_smul A L)
      (IntrinsicPositiveQuadratic.nativeChernQuadratic_positive A L hL) f
      (IntrinsicPositiveQuadratic.nativeChernQuadratic_isometry A L e.hom he) hpres N hN
    intro x hx
    rw [hspan] at hx ⊢
    obtain ⟨y, hy, hxy⟩ := hcong x hx
    refine ⟨y, hy, ?_⟩
    change AbelianModuli.ReferenceFamily.Intrinsic.Maps.IntrinsicLinearMaps.linearLift e.hom x - x = N • y
    simpa only [natCast_zsmul] using hxy
  apply AbelianModuli.ReferenceFamily.Intrinsic.Maps.IntrinsicLinearMaps.linearLift_faithful e.hom (𝟙 A.toOver)
  rw [AbelianModuli.ReferenceFamily.Intrinsic.Maps.IntrinsicLinearMaps.linearLift_id]
  apply LinearMap.ext
  intro x
  exact LinearEquiv.congr_fun hf x

end

end OAI.AlgebraicGeometry.AbelianScheme.TateComparison.IntrinsicLevelRigidity
