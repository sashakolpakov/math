import OAI.AlgebraicGeometry.Resolution.Blowups.Finite.TypeEmbeddingDimension
import OAI.AlgebraicGeometry.Resolution.Blowups.Smooth.BlowupChart
import OAI.AlgebraicGeometry.Resolution.Blowups.Affine.OpenDimension

/-! # Blowup Dimension -/

namespace OAI.AlgebraicGeometry.Resolution.Blowups.Smooth.BlowupDimension.Construction

noncomputable section

/-! Dimension bounds on actual smooth blowup denominator charts. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

attribute [local instance] Relative.DifferentialBlowup.Construction.blowupRelativeBaseAlgebra

/-- The coefficient-fraction embedding retains the original ground-field
structure map, even when the original ring has zero divisors. -/
def blowupChartToLocalizationAlgHom (k : Type u) {R : Type u}
    [CommRing k] [CommRing R] [Algebra k R] (I : Ideal R) (a : I) :
    Blowup.Charts.Construction.blowupChart I a →ₐ[k] Localization.Away a.val where
  toRingHom := Blowup.Charts.Construction.blowupChartToLocalization I a
  commutes' c := by
    change Blowup.Charts.Construction.blowupChartToLocalization I a (Blowup.Charts.Construction.blowupChartConstants I a (algebraMap k R c)) = _
    rw [Blowup.Charts.Construction.blowupChartToLocalization_constants]
    exact (IsScalarTower.algebraMap_apply k R (Localization.Away a.val) c).symm

/-- An actual finite-type blowup chart embeds in a principal localization
of the source. Finite-type dimension comparison therefore retains the
source bound, with no integrality or nonzero-denominator assumption. -/
theorem blowupChart_ringKrullDim_le_of_finiteType (k : Type u) {R : Type u}
    [Field k] [CommRing R] [Algebra k R] [Algebra.FiniteType k R]
    (I : Ideal R) (a : I) [Algebra.FiniteType k (Blowup.Charts.Construction.blowupChart I a)] :
    ringKrullDim (Blowup.Charts.Construction.blowupChart I a) ≤ ringKrullDim R := by
  let : Algebra.FiniteType k (Localization.Away a.val) :=
    Algebra.FiniteType.trans (inferInstance : Algebra.FiniteType k R) inferInstance
  have hle := Finite.TypeEmbeddingDimension.Construction.finiteType_ringKrullDim_le_of_injective k (blowupChartToLocalizationAlgHom k I a)
    (Blowup.Charts.Construction.blowupChartToLocalization_injective I a)
  let : IsOpenImmersion (Spec.map (CommRingCat.ofHom (algebraMap R (Localization.Away a.val)))) :=
    IsOpenImmersion.of_isLocalization a.val
  exact hle.trans (Affine.OpenDimension.Construction.ringKrullDim_le_of_spec_openImmersion (algebraMap R (Localization.Away a.val)))

/-- Every denominator chart in an actual smooth blowup retains the
original dimension bound, including disconnected and empty charts. -/
theorem blowupChart_ringKrullDim_le_of_blowup_smooth (k : Type u) {R : Type u}
    [Field k] [CommRing R] [Algebra k R] [Algebra.Smooth k R]
    (I : Ideal R)
    [Smooth (ReesGrading.Construction.affineBlowupToSpec I ≫ Spec.map (CommRingCat.ofHom (algebraMap k R)))] (a : I) :
    ringKrullDim (Blowup.Charts.Construction.blowupChart I a) ≤ ringKrullDim R := by
  let : Algebra.Smooth k (Blowup.Charts.Construction.blowupChart I a) := BlowupChart.Construction.blowupChart_smooth_of_blowup_smooth k I a
  exact blowupChart_ringKrullDim_le_of_finiteType k I a

end

end OAI.AlgebraicGeometry.Resolution.Blowups.Smooth.BlowupDimension.Construction
