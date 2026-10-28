import Mathlib.AlgebraicGeometry.ResidueField

/-! # Residue Detection -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.AffineOpen.ResidueDetection

noncomputable section

/-! An open subset of an affine scheme is the whole scheme exactly when every residue-field point factors through it. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

theorem affineResiduePoint_image (R : CommRingCat.{u}) (p : PrimeSpectrum R) :
    (Spec.map (CommRingCat.ofHom (algebraMap R p.asIdeal.ResidueField)))
      (⊥ : PrimeSpectrum p.asIdeal.ResidueField) = p := by
  apply PrimeSpectrum.ext
  change RingHom.ker (algebraMap R p.asIdeal.ResidueField) = p.asIdeal
  exact p.asIdeal.ker_algebraMap_residueField

theorem affineOpen_eq_top_iff_residuePoints (R : CommRingCat.{u}) (U : (Spec R).Opens) :
    U = ⊤ ↔ ∀ p : PrimeSpectrum R,
      (Spec.map (CommRingCat.ofHom (algebraMap R p.asIdeal.ResidueField))) ⁻¹ᵁ U = ⊤ := by
  constructor
  · intro h p
    rw [h, Scheme.Hom.preimage_top]
  · intro h
    apply top_unique
    intro p _
    change PrimeSpectrum R at p
    have hp : (⊥ : PrimeSpectrum p.asIdeal.ResidueField) ∈
        (Spec.map (CommRingCat.ofHom (algebraMap R p.asIdeal.ResidueField))) ⁻¹ᵁ U := by
      rw [h p]
      trivial
    change (Spec.map (CommRingCat.ofHom (algebraMap R p.asIdeal.ResidueField)))
      (⊥ : PrimeSpectrum p.asIdeal.ResidueField) ∈ U at hp
    rwa [affineResiduePoint_image] at hp

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.AffineOpen.ResidueDetection
