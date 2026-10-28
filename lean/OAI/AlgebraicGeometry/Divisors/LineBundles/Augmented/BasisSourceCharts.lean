import OAI.AlgebraicGeometry.Divisors.LineBundles.SymmetricProjective.IntegralFibers
import Mathlib.LinearAlgebra.Basis.Prod

/-! # Basis Source Charts -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles.Augmented.BasisSourceCharts.BundleCycles

noncomputable section

/-! A basis of the module gives projective source charts whose
relative dimension is exactly the size of that basis. -/

open _root_.AlgebraicGeometry _root_.CategoryTheory

variable {R M ι : Type} [CommRing R] [AddCommGroup M] [Module R M]
    [Fintype ι] (b : Module.Basis ι R M)

include b in
theorem symmetricAugmentedBasis_sourceCharts :
    AffineSpace.SourceRank.BundleCycles.HasAffineSpaceSourceChartsOfRank (SymmetricProjective.Scheme.BundleCycles.symmetricProjectiveToBase R (R × M)) (Nat.card ι) := by
  have H := Symmetric.BasisAffineChart.BundleCycles.symmetricProjective_hasAffineSpaceSourceChartsOfRank ((Module.Basis.singleton Unit R).prod b)
  have he : Nat.card (Unit ⊕ ι) - 1 = Nat.card ι := by rw [Nat.card_sum, Nat.card_unique]; omega
  rwa [he] at H

include b in
theorem symmetricAugmentedBasis_geometricallyIntegral :
    GeometricallyIntegral (SymmetricProjective.Scheme.BundleCycles.symmetricProjectiveToBase R (R × M)) :=
  SymmetricProjective.IntegralFibers.BundleCycles.symmetricProjective_geometricallyIntegral ((Module.Basis.singleton Unit R).prod b)

end

end OAI.AlgebraicGeometry.Divisors.LineBundles.Augmented.BasisSourceCharts.BundleCycles
