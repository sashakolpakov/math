import OAI.AlgebraicGeometry.Divisors.LineBundles.Free.SymmetricProjectiveChow
import OAI.AlgebraicGeometry.Divisors.LineBundles.AffineSource.ChowRetraction

/-! # Symmetric Projective Chow Injective -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles.Free.SymmetricProjectiveChowInjective.BundleCycles

noncomputable section

/-! Fiber-generic Chow pullback to a finite free projective bundle
is injective, as witnessed by restriction to an actual basis chart. -/

open _root_.AlgebraicGeometry _root_.CategoryTheory

theorem finiteBasisComplement_card {ι : Type} [Fintype ι] (i : ι) :
    Nat.card {j : ι // j ≠ i} = Nat.card ι - 1 := by
  classical
  let : Unique {j : ι // j = i} := ⟨⟨i, rfl⟩, fun j => Subtype.ext j.property⟩
  rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card, Fintype.card_subtype_compl,
    Fintype.card_unique (α := {j : ι // j = i})]

variable {R M ι : Type} [CommRing R] [IsNoetherianRing R] [AddCommGroup M] [Module R M]
    [Module.Finite R M] [Fintype ι] [Nonempty ι] (b : Module.Basis ι R M)
    (f : Spec (.of R) ⟶ Foundations.Scheme.ProjectiveSpace.complexBase) [LocallyOfFiniteType f]

include b in
theorem freeSymmetricProjectiveChowExtension_injective (d : ℕ) :
    Function.Injective (SymmetricProjectiveChow.BundleCycles.freeSymmetricProjectiveChowExtension b f d) := by
  classical
  let i : ι := Classical.choice inferInstance
  let : Smooth (SymmetricProjective.Scheme.BundleCycles.symmetricProjectiveToBase R M) := (Symmetric.BasisAffineChart.BundleCycles.symmetricProjective_hasAffineSpaceSourceCharts b).smooth
  let : GeometricallyIntegral (SymmetricProjective.Scheme.BundleCycles.symmetricProjectiveToBase R M) := SymmetricProjective.IntegralFibers.BundleCycles.symmetricProjective_geometricallyIntegral b
  change Function.Injective (AffineSpace.SourceChowExtension.BundleCycles.affineSpaceSourceChowExtension (SymmetricProjective.Scheme.BundleCycles.symmetricProjectiveToBase R M) f
    (Nat.card ι - 1) (Symmetric.BasisAffineChart.BundleCycles.symmetricProjective_hasAffineSpaceSourceChartsOfRank b) d)
  have H (r : ℕ) (hr : Nat.card {j : ι // j ≠ i} = r)
      (hp : AffineSpace.SourceRank.BundleCycles.HasAffineSpaceSourceChartsOfRank (SymmetricProjective.Scheme.BundleCycles.symmetricProjectiveToBase R M) r) :
      Function.Injective (AffineSpace.SourceChowExtension.BundleCycles.affineSpaceSourceChowExtension (SymmetricProjective.Scheme.BundleCycles.symmetricProjectiveToBase R M) f r hp d) := by
    subst r
    exact AffineSource.ChowRetraction.BundleCycles.affineSourceChowExtension_injective (SymmetricProjective.Scheme.BundleCycles.symmetricProjectiveToBase R M) f {j : ι // j ≠ i}
      hp (Symmetric.BasisAffineChart.BundleCycles.symmetricBasisAffineChartMap b i) (Symmetric.BasisAffineChart.BundleCycles.symmetricBasisAffineChartMap_over b i) d
  exact H _ (finiteBasisComplement_card i) _

end

end OAI.AlgebraicGeometry.Divisors.LineBundles.Free.SymmetricProjectiveChowInjective.BundleCycles
