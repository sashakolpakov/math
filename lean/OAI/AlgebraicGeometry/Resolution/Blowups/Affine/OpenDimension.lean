import OAI.AlgebraicGeometry.Resolution.Blowups.IsomorphicBlowupChartEtale
import Mathlib.RingTheory.KrullDimension.Basic

/-! # Open Dimension -/

namespace OAI.AlgebraicGeometry.Resolution.Blowups.Affine.OpenDimension.Construction

noncomputable section

/-! Ring dimension cannot increase along an actual affine open immersion. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

theorem ringKrullDim_le_of_spec_openImmersion {R S : Type u} [CommRing R] [CommRing S]
    (φ : R →+* S) [IsOpenImmersion (Spec.map (CommRingCat.ofHom φ))] :
    ringKrullDim S ≤ ringKrullDim R := by
  apply Order.krullDim_le_of_strictMono (PrimeSpectrum.comap φ)
  have hmono : Monotone (PrimeSpectrum.comap φ) := fun _ _ h => Ideal.comap_mono h
  exact hmono.strictMono_of_injective (Spec.map (CommRingCat.ofHom φ)).isOpenEmbedding.injective

/-- Actual denominator charts of an isomorphic blowup retain the original
affine Krull dimension bound. Empty charts are included automatically. -/
theorem blowupChart_ringKrullDim_le_of_isIso {R : Type u} [CommRing R] (I : Ideal R)
    [IsIso (ReesGrading.Construction.affineBlowupToSpec I)] (a : I) : ringKrullDim (Blowup.Charts.Construction.blowupChart I a) ≤ ringKrullDim R := by
  let : IsOpenImmersion (Spec.map (CommRingCat.ofHom (Blowup.Charts.Construction.blowupChartConstants I a))) :=
    IsomorphicBlowupChartEtale.Construction.blowupChartConstants_spec_open_of_isIso I a
  exact ringKrullDim_le_of_spec_openImmersion (Blowup.Charts.Construction.blowupChartConstants I a)

end

end OAI.AlgebraicGeometry.Resolution.Blowups.Affine.OpenDimension.Construction
