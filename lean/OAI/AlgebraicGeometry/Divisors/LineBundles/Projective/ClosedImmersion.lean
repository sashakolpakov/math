import OAI.AlgebraicGeometry.Divisors.LineBundles.Projective.MapChartPullback
import OAI.AlgebraicGeometry.Divisors.LineBundles.Graded.SurjectiveChart
import OAI.AlgebraicGeometry.Divisors.LineBundles.Global.SpecialFiber

/-! # Closed Immersion -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles.Projective.ClosedImmersion.BundleCycles

noncomputable section

/-! Surjective graded homomorphisms give closed immersions of actual
projective spectra, proved on their native affine charts. -/

open _root_.AlgebraicGeometry _root_.CategoryTheory _root_.HomogeneousLocalization

universe u

variable {A B σ τ : Type u} [CommRing A] [CommRing B]
    [SetLike σ A] [AddSubgroupClass σ A] [SetLike τ B] [AddSubgroupClass τ B]
    {𝒜 : ℕ → σ} {ℬ : ℕ → τ} [GradedRing 𝒜] [GradedRing ℬ]
    (f : 𝒜 →+*ᵍ ℬ)
    (hf : HomogeneousIdeal.irrelevant ℬ ≤ (HomogeneousIdeal.irrelevant 𝒜).map f)
    (hsurj : Function.Surjective f)

include hsurj in
theorem projectiveMap_isClosedImmersion : IsClosedImmersion (Proj.map f hf) := by
  apply Global.SpecialFiber.BundleCycles.isClosedImmersion_of_cover_pullbacks (Proj.map f hf) (Proj.affineOpenCover 𝒜).openCover
    (fun s => Spec (.of (Away ℬ (f s.2.val))))
    (fun s => Proj.awayι ℬ (f s.2.val) (f.map_mem s.2.property) s.1.property)
    (fun s => Spec.map (CommRingCat.ofHom (Away.map f s.2.val)))
  · intro s
    exact MapChartPullback.BundleCycles.projectiveMap_chart_isPullback f hf s.2.property s.1.property
  · intro s
    exact IsClosedImmersion.spec_of_surjective _ (Graded.SurjectiveChart.BundleCycles.gradedAwayMap_surjective f hsurj s.2.property)

end

end OAI.AlgebraicGeometry.Divisors.LineBundles.Projective.ClosedImmersion.BundleCycles
