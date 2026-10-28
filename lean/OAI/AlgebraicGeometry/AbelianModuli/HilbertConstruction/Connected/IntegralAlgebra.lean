import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Connected.ArtinianReduced
import Mathlib.RingTheory.IntegralClosure.IsIntegral.Basic

/-! # Integral Algebra -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Connected.IntegralAlgebra

noncomputable section

/-! An integral reduced algebra over a field with connected spectrum is a field. -/

universe u v

theorem injective_ringHom_preconnectedSpectrum {R : Type u} {S : Type v}
    [CommRing R] [CommRing S] [PreconnectedSpace (PrimeSpectrum S)]
    (f : R →+* S) (hf : Function.Injective f) : PreconnectedSpace (PrimeSpectrum R) := by
  have hd : DenseRange (PrimeSpectrum.comap f) :=
    (PrimeSpectrum.denseRange_comap_iff_ker_le_nilRadical f).mpr
      (((RingHom.injective_iff_ker_eq_bot f).mp hf).le.trans bot_le)
  exact hd.preconnectedSpace (PrimeSpectrum.continuous_comap f)

theorem connected_integral_reduced_isField (K : Type u) (R : Type v)
    [Field K] [CommRing R] [Nontrivial R] [Algebra K R] [Algebra.IsIntegral K R]
    [IsReduced R] [PreconnectedSpace (PrimeSpectrum R)] : IsField R := by
  refine ⟨⟨0, 1, zero_ne_one⟩, mul_comm, ?_⟩
  intro a ha
  let B := Algebra.adjoin K ({a} : Set R)
  have : Module.Finite K B :=
    Algebra.finite_adjoin_simple_of_isIntegral (Algebra.IsIntegral.isIntegral a)
  have : IsArtinianRing B := IsArtinianRing.of_finite K B
  have : IsReduced B := isReduced_of_injective B.val Subtype.val_injective
  have : PreconnectedSpace (PrimeSpectrum B) :=
    injective_ringHom_preconnectedSpectrum B.val.toRingHom Subtype.val_injective
  have hB : IsField B := ArtinianReduced.connected_artinian_reduced_isField B
  let aB : B := ⟨a, Algebra.subset_adjoin (Set.mem_singleton a)⟩
  have haB : aB ≠ 0 := fun h => ha (congrArg Subtype.val h)
  obtain ⟨b, hb⟩ := hB.mul_inv_cancel haB
  exact ⟨b.val, congrArg Subtype.val hb⟩

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Connected.IntegralAlgebra
