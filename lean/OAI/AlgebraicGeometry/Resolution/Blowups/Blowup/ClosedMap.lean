import OAI.AlgebraicGeometry.Resolution.Blowups.Blowup.Functor
import OAI.AlgebraicGeometry.Resolution.Blowups.ProjectiveClosedImmersion

/-! # Closed Map -/

namespace OAI.AlgebraicGeometry.Resolution.Blowups.Blowup.ClosedMap.Construction

noncomputable section

/-! Closed immersions induced by surjective coefficient maps on actual Rees blowups. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

variable {R S : Type u} [CommRing R] [CommRing S]

/-- A surjective coefficient map is surjective on the extended Rees algebra. -/
theorem reesRingMap_surjective (I : Ideal R) (φ : R →+* S)
    (hφ : Function.Surjective φ) : Function.Surjective (ReesMap.Construction.reesRingMap I φ) := by
  intro p
  have hp : p ∈ Algebra.adjoin S
      (Set.range (fun a : I => ReesMap.Construction.reesRingMap I φ (Charts.Construction.reesGenerator I a))) := by
    rw [ReesMap.Construction.reesMappedGenerators_adjoin]
    trivial
  induction hp using Algebra.adjoin_induction with
  | mem p hp =>
    obtain ⟨a, rfl⟩ := hp
    exact ⟨Charts.Construction.reesGenerator I a, rfl⟩
  | algebraMap s =>
    obtain ⟨r, rfl⟩ := hφ s
    exact ⟨algebraMap R (reesAlgebra I) r, ReesMap.Construction.reesRingMap_constants I φ r⟩
  | add p q _ _ hp hq =>
    obtain ⟨p, rfl⟩ := hp
    obtain ⟨q, rfl⟩ := hq
    exact ⟨p + q, map_add _ _ _⟩
  | mul p q _ _ hp hq =>
    obtain ⟨p, rfl⟩ := hp
    obtain ⟨q, rfl⟩ := hq
    exact ⟨p * q, map_mul _ _ _⟩

/-- Blowing up the extended center on a closed affine carrier gives a closed
immersion into the ambient blowup. -/
theorem affineBlowupMap_isClosedImmersion (I : Ideal R) (φ : R →+* S)
    (hφ : Function.Surjective φ) : IsClosedImmersion (ReesMap.Construction.affineBlowupMap I φ) :=
  ProjectiveClosedImmersion.Construction.projMap_isClosedImmersion_of_surjective (ReesMap.Construction.reesGradedMap I φ)
    (ReesMap.Construction.reesGradedMap_irrelevant_le I φ) (reesRingMap_surjective I φ hφ)

/-- The same closed immersion with an explicitly identified target center. -/
theorem affineBlowupMapTo_isClosedImmersion (I : Ideal R) (J : Ideal S)
    (φ : R →+* S) (h : I.map φ = J) (hφ : Function.Surjective φ) :
    IsClosedImmersion (Functor.Construction.affineBlowupMapTo I J φ h) := by
  subst J
  exact affineBlowupMap_isClosedImmersion I φ hφ

end

end OAI.AlgebraicGeometry.Resolution.Blowups.Blowup.ClosedMap.Construction
