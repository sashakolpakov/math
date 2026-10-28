import Mathlib.RingTheory.Smooth.StandardSmoothCotangent
import Mathlib.RingTheory.Smooth.Flat
import Mathlib.RingTheory.Etale.Kaehler

/-! # Standard Smooth Localization -/

namespace OAI.RepresentationTheory.Theta.Geometric.StandardSmoothLocalization

noncomputable section

/-! Localizing an actual standard smooth chart preserves its formal
smoothness, flatness, and finite free relative differential rank. -/

open KaehlerDifferential
open scoped TensorProduct

variable {R P S : Type*} [CommRing R] [CommRing P] [CommRing S]
    [Algebra R P] [Algebra R S] [Algebra P S] [IsScalarTower R P S]
    [Nontrivial S] (W : Submonoid P) [IsLocalization W S]
    (n : ℕ) [Algebra.IsStandardSmoothOfRelativeDimension n R P]

include W in
theorem standardSmooth_localization_properties :
    Algebra.FormallySmooth R S ∧ Module.Flat R S ∧
      Module.Free S Ω[S⁄R] ∧ Module.Finite S Ω[S⁄R] ∧ Module.finrank S Ω[S⁄R] = n := by
  have : Nontrivial P := RingHom.domain_nontrivial (algebraMap P S)
  have : Algebra.IsStandardSmooth R P := Algebra.IsStandardSmoothOfRelativeDimension.isStandardSmooth n
  have : Algebra.FormallyEtale P S := Algebra.FormallyEtale.of_isLocalization W
  have : Algebra.FormallySmooth R S := Algebra.FormallySmooth.comp R P S
  have : Module.Flat P S := IsLocalization.flat S W
  have : Module.Flat R S := Module.Flat.trans R P S
  let e := tensorKaehlerEquivOfFormallyEtale R P S
  have : Module.Free S Ω[S⁄R] := Module.Free.of_equiv e
  have : Module.Finite S Ω[S⁄R] := Module.Finite.of_surjective e.toLinearMap e.surjective
  refine ⟨inferInstance, inferInstance, inferInstance, inferInstance, ?_⟩
  have h := e.finrank_eq
  rw [Module.finrank_baseChange] at h
  exact h.symm.trans (Module.finrank_eq_of_rank_eq
    (Algebra.IsStandardSmoothOfRelativeDimension.rank_kaehlerDifferential (R := R) (S := P) n))

end

end OAI.RepresentationTheory.Theta.Geometric.StandardSmoothLocalization
