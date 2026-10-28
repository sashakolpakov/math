import OAI.AlgebraicGeometry.Divisors.LineBundles.GenericFiberEss

/-! # Function Unit -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles.FunctionUnit.BundleCycles

noncomputable section

/-! Algebraic nonzero functions are units in the actual normal stalk. -/

theorem algebraic_isUnit_integer (k R L : Type*) [Field k] [CommRing R] [IsDomain R]
    [IsIntegrallyClosed R] [Field L] [Algebra k R] [Algebra k L] [Algebra R L]
    [IsScalarTower k R L] [IsFractionRing R L] (g : L) (hg : g ≠ 0) (ha : IsAlgebraic k g) :
    ∃ a : R, IsUnit a ∧ algebraMap R L a = g := by
  obtain ⟨a, ha'⟩ := (isIntegrallyClosed_iff L).mp ‹IsIntegrallyClosed R› ha.isIntegral.tower_top
  obtain ⟨b, hb'⟩ := (isIntegrallyClosed_iff L).mp ‹IsIntegrallyClosed R› ha.inv.isIntegral.tower_top
  refine ⟨a, IsUnit.of_mul_eq_one b ?_, ha'⟩
  apply IsFractionRing.injective R L
  rw [map_mul, ha', hb', mul_inv_cancel₀ hg, map_one]

end

end OAI.AlgebraicGeometry.Divisors.LineBundles.FunctionUnit.BundleCycles
