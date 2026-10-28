import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.CrystallineMonoidAction
import OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedCrystalline.BasePointCohomology
import OAI.NumberTheory.PadicHodge.IntegralComparison.Crystalline.RestrictionJointKernel
import OAI.NumberTheory.PadicHodge.IntegralComparison.Crystalline.FiniteLevelKernel
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

/-! # Crystalline Axes -/

namespace OAI.NumberTheory.PadicHodge.CrystallineAxes.FrobeniusSlope

noncomputable section

/-! Actual crystalline H1 of the base point and the product-axis reduction
of the group-law identity. No de Rham or Betti comparison is used here. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open MonoidalCategory CartesianMonoidalCategory MonObj
open scoped _root_.CategoryTheory.MonObj TensorProduct
open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.CrystallineFunctoriality.CM
open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.CrystallineMonoidAction.CM.End

variable (q : ℕ) [Fact q.Prime]

def basePoint : Over (Spec (.of (ZMod q))) := Over.mk (𝟙 _)

instance integral_basePoint_subsingleton : Subsingleton (GeometricComparison.Crystalline.CoefficientAdapter.IntegralH1 q (basePoint q)) := by
  apply subsingleton_of_forall_eq 0
  intro x
  let f := IntegralComparison.Crystalline.BasePointFrame.baseMap q (ZMod q)
  let : Mono (HomologicalComplex.homologyMap
      (IntegralComparison.Crystalline.ResolutionComplexExact.sequence (p := q)
        (J := Ideal.span {(q : GeometricComparison.Crystalline.CoefficientAdapter.Witt q)})
        (δ := AlgebraicGeometry.Crystalline.Cohomology.Witt.DividedPowers.WittDividedPowers.wittDividedPowers q (ZMod q)) f).f 1) :=
    IntegralComparison.Crystalline.FiniteLevelKernel.inclusion_mono_succ f 0
  exact IntegralComparison.Crystalline.RestrictionJointKernel.zero_of_restrictions f 1 x
    (fun n => IntegralComparison.BoundedCrystalline.BasePointCohomology.eq_zero q (ZMod q) n 0 _)

instance rational_basePoint_subsingleton : Subsingleton (GeometricComparison.Crystalline.CoefficientAdapter.RationalH1 q (basePoint q)) := by
  infer_instance

theorem pullback_through_basePoint
    {X Y : Over (Spec (.of (ZMod q)))}
    (f : X ⟶ basePoint q) (g : basePoint q ⟶ Y) : GeometricComparison.Crystalline.CoefficientAdapter.rationalPullback q (f ≫ g) = 0 := by
  rw [← AlgebraicGeometry.HodgeConjecture.HeckeCycles.CrystallineFunctoriality.CM.rationalPullback_comp]
  apply LinearMap.ext
  intro x
  rw [LinearMap.comp_apply, Subsingleton.elim (GeometricComparison.Crystalline.CoefficientAdapter.rationalPullback q g x) 0, map_zero]
  rfl

theorem pullback_one {X Y : Over (Spec (.of (ZMod q)))} [GrpObj Y] :
    GeometricComparison.Crystalline.CoefficientAdapter.rationalPullback q (1 : X ⟶ Y) = 0 := by
  change GeometricComparison.Crystalline.CoefficientAdapter.rationalPullback q (toUnit X ≫ η[Y]) = 0
  exact pullback_through_basePoint q (toUnit X) η[Y]

variable (A : Over (Spec (.of (ZMod q)))) [GrpObj A] [IsCommMonObj A]

def leftAxis : A ⟶ A ⊗ A := lift (𝟙 A) (1 : A ⟶ A)
def rightAxis : A ⟶ A ⊗ A := lift (1 : A ⟶ A) (𝟙 A)

def restrictions : GeometricComparison.Crystalline.CoefficientAdapter.RationalH1 q (A ⊗ A) →ₗ[ℚ_[q]] GeometricComparison.Crystalline.CoefficientAdapter.RationalH1 q A × GeometricComparison.Crystalline.CoefficientAdapter.RationalH1 q A :=
  (GeometricComparison.Crystalline.CoefficientAdapter.rationalPullback q (leftAxis q A)).prod (GeometricComparison.Crystalline.CoefficientAdapter.rationalPullback q (rightAxis q A))

def projections : GeometricComparison.Crystalline.CoefficientAdapter.RationalH1 q A × GeometricComparison.Crystalline.CoefficientAdapter.RationalH1 q A →ₗ[ℚ_[q]] GeometricComparison.Crystalline.CoefficientAdapter.RationalH1 q (A ⊗ A) :=
  (GeometricComparison.Crystalline.CoefficientAdapter.rationalPullback q (fst A A)).comp (LinearMap.fst ℚ_[q] _ _) +
    (GeometricComparison.Crystalline.CoefficientAdapter.rationalPullback q (snd A A)).comp (LinearMap.snd ℚ_[q] _ _)

theorem restrictions_projections :
    (restrictions q A).comp (projections q A) = LinearMap.id := by
  apply LinearMap.ext
  intro x
  apply Prod.ext
  · change GeometricComparison.Crystalline.CoefficientAdapter.rationalPullback q (leftAxis q A)
      (GeometricComparison.Crystalline.CoefficientAdapter.rationalPullback q (fst A A) x.1 + GeometricComparison.Crystalline.CoefficientAdapter.rationalPullback q (snd A A) x.2) = x.1
    rw [map_add, ← LinearMap.comp_apply, AlgebraicGeometry.HodgeConjecture.HeckeCycles.CrystallineFunctoriality.CM.rationalPullback_comp,
      ← LinearMap.comp_apply, AlgebraicGeometry.HodgeConjecture.HeckeCycles.CrystallineFunctoriality.CM.rationalPullback_comp]
    simp only [leftAxis, lift_fst, lift_snd, AlgebraicGeometry.HodgeConjecture.HeckeCycles.CrystallineFunctoriality.CM.rationalPullback_id, pullback_one,
      LinearMap.id_apply, LinearMap.zero_apply, add_zero]
  · change GeometricComparison.Crystalline.CoefficientAdapter.rationalPullback q (rightAxis q A)
      (GeometricComparison.Crystalline.CoefficientAdapter.rationalPullback q (fst A A) x.1 + GeometricComparison.Crystalline.CoefficientAdapter.rationalPullback q (snd A A) x.2) = x.2
    rw [map_add, ← LinearMap.comp_apply, AlgebraicGeometry.HodgeConjecture.HeckeCycles.CrystallineFunctoriality.CM.rationalPullback_comp,
      ← LinearMap.comp_apply, AlgebraicGeometry.HodgeConjecture.HeckeCycles.CrystallineFunctoriality.CM.rationalPullback_comp]
    simp only [rightAxis, lift_fst, lift_snd, AlgebraicGeometry.HodgeConjecture.HeckeCycles.CrystallineFunctoriality.CM.rationalPullback_id, pullback_one,
      LinearMap.id_apply, LinearMap.zero_apply, zero_add]

theorem groupLaw_of_restrictions_injective
    (hinj : Function.Injective (restrictions q A)) : AlgebraicGeometry.HodgeConjecture.HeckeCycles.CrystallineMonoidAction.CM.End.GroupLawIdentity q A := by
  apply LinearMap.ext
  intro x
  apply hinj
  change restrictions q A (GeometricComparison.Crystalline.CoefficientAdapter.rationalPullback q μ[A] x) =
    restrictions q A (projections q A (x, x))
  have hsplit := LinearMap.congr_fun (restrictions_projections q A) (x, x)
  rw [LinearMap.comp_apply, LinearMap.id_apply] at hsplit
  rw [hsplit]
  apply Prod.ext
  · change GeometricComparison.Crystalline.CoefficientAdapter.rationalPullback q (leftAxis q A) (GeometricComparison.Crystalline.CoefficientAdapter.rationalPullback q μ[A] x) = x
    rw [← LinearMap.comp_apply, AlgebraicGeometry.HodgeConjecture.HeckeCycles.CrystallineFunctoriality.CM.rationalPullback_comp]
    have h : leftAxis q A ≫ μ[A] = 𝟙 A := by
      change (𝟙 A) * (1 : A ⟶ A) = 𝟙 A
      exact mul_one _
    rw [h, AlgebraicGeometry.HodgeConjecture.HeckeCycles.CrystallineFunctoriality.CM.rationalPullback_id, LinearMap.id_apply]
  · change GeometricComparison.Crystalline.CoefficientAdapter.rationalPullback q (rightAxis q A) (GeometricComparison.Crystalline.CoefficientAdapter.rationalPullback q μ[A] x) = x
    rw [← LinearMap.comp_apply, AlgebraicGeometry.HodgeConjecture.HeckeCycles.CrystallineFunctoriality.CM.rationalPullback_comp]
    have h : rightAxis q A ≫ μ[A] = 𝟙 A := by
      change (1 : A ⟶ A) * (𝟙 A) = 𝟙 A
      exact one_mul _
    rw [h, AlgebraicGeometry.HodgeConjecture.HeckeCycles.CrystallineFunctoriality.CM.rationalPullback_id, LinearMap.id_apply]

/-- The only remaining geometric requirement in the dimension route is the
product H1 upper bound. The split projection identities are already proved above. -/
theorem restrictions_injective_of_dimension_bound
    [FiniteDimensional ℚ_[q] (GeometricComparison.Crystalline.CoefficientAdapter.RationalH1 q A)]
    [FiniteDimensional ℚ_[q] (GeometricComparison.Crystalline.CoefficientAdapter.RationalH1 q (A ⊗ A))]
    (hdim : Module.finrank ℚ_[q] (GeometricComparison.Crystalline.CoefficientAdapter.RationalH1 q (A ⊗ A)) ≤
      2 * Module.finrank ℚ_[q] (GeometricComparison.Crystalline.CoefficientAdapter.RationalH1 q A)) :
    Function.Injective (restrictions q A) := by
  have hs : Function.Surjective (restrictions q A) := by
    intro x
    exact ⟨projections q A x, LinearMap.congr_fun (restrictions_projections q A) x⟩
  have hlower := LinearMap.finrank_le_finrank_of_surjective hs
  have hd : Module.finrank ℚ_[q] (GeometricComparison.Crystalline.CoefficientAdapter.RationalH1 q (A ⊗ A)) =
      Module.finrank ℚ_[q] (GeometricComparison.Crystalline.CoefficientAdapter.RationalH1 q A × GeometricComparison.Crystalline.CoefficientAdapter.RationalH1 q A) := by
    rw [Module.finrank_prod] at hlower ⊢
    omega
  exact (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hd).mpr hs

end

end OAI.NumberTheory.PadicHodge.CrystallineAxes.FrobeniusSlope
