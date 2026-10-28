import Mathlib.RingTheory.Spectrum.Prime.Noetherian
import Mathlib.RingTheory.KrullDimension.Zero
import Mathlib.Topology.Connected.TotallyDisconnected

/-! # Artinian Reduced -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Connected.ArtinianReduced

/-! A reduced Artinian ring with nonempty connected spectrum is a field. -/

universe u

theorem connected_artinian_reduced_isField (R : Type u) [CommRing R] [Nontrivial R]
    [IsArtinianRing R] [IsReduced R] [PreconnectedSpace (PrimeSpectrum R)] : IsField R := by
  have : Subsingleton (PrimeSpectrum R) := subsingleton_of_preconnected_totallyDisconnected
  exact PrimeSpectrum.subsingleton_iff_isField_of_isReduced.mp this

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Connected.ArtinianReduced
