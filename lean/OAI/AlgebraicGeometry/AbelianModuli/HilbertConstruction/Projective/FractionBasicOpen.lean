import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Basic

/-! # Fraction Basic Open -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Projective.FractionBasicOpen

noncomputable section

/-! The regular homogeneous fraction on a projective chart has the expected basic open. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.HomogeneousLocalization

universe u

variable {R A : Type u} [CommRing R] [CommRing A] [Algebra R A]
variable (𝒜 : ℕ → Submodule R A) [GradedAlgebra 𝒜]
variable {f g : A} {d e : ℕ} (hf : f ∈ 𝒜 d) (hd : 0 < d) (hg : g ∈ 𝒜 e) (he : 0 < e)

theorem projectiveAway_preimage_section_basicOpen (z : Away 𝒜 f) :
    Proj.awayι 𝒜 f hf hd ⁻¹ᵁ (Proj 𝒜).basicOpen (Proj.awayToSection 𝒜 f z) =
      PrimeSpectrum.basicOpen z := by
  have h : Proj.basicOpenToSpec 𝒜 f ⁻¹ᵁ PrimeSpectrum.basicOpen z =
      (Proj.basicOpen 𝒜 f).ι ⁻¹ᵁ (Proj 𝒜).basicOpen (Proj.awayToSection 𝒜 f z) := by
    change ((Proj.basicOpen 𝒜 f).toSpecΓ ≫ Spec.map (Proj.awayToSection 𝒜 f)) ⁻¹ᵁ
      PrimeSpectrum.basicOpen z = _
    exact (Scheme.Hom.comp_preimage _ _ _).trans
      ((congrArg (fun V : (Spec Γ(Proj 𝒜, Proj.basicOpen 𝒜 f)).Opens =>
        (Proj.basicOpen 𝒜 f).toSpecΓ ⁻¹ᵁ V)
        (SpecMap_preimage_basicOpen (Proj.awayToSection 𝒜 f) z)).trans
          (Scheme.Opens.toSpecΓ_preimage_basicOpen (Proj.basicOpen 𝒜 f) (Proj.awayToSection 𝒜 f z)))
  let E := Proj.basicOpenIsoSpec 𝒜 f hf hd
  have h' : E.hom ⁻¹ᵁ PrimeSpectrum.basicOpen z =
      (Proj.basicOpen 𝒜 f).ι ⁻¹ᵁ (Proj 𝒜).basicOpen (Proj.awayToSection 𝒜 f z) := h
  have hi := congrArg (fun V : (Proj.basicOpen 𝒜 f).toScheme.Opens => E.inv ⁻¹ᵁ V) h'.symm
  exact hi.trans ((Scheme.Hom.comp_preimage E.inv E.hom _).symm.trans
    (congrArg (fun a : Spec (.of (Away 𝒜 f)) ⟶ Spec (.of (Away 𝒜 f)) =>
      a ⁻¹ᵁ (show (Spec (.of (Away 𝒜 f))).Opens from PrimeSpectrum.basicOpen z)) E.inv_hom_id))

include hd he in
theorem projectiveFraction_basicOpen :
    (Proj 𝒜).basicOpen (Proj.awayToSection 𝒜 f (Away.isLocalizationElem hf hg)) =
      Proj.basicOpen 𝒜 f ⊓ Proj.basicOpen 𝒜 g := by
  let i := Proj.awayι 𝒜 f hf hd
  let r := Proj.awayToSection 𝒜 f (Away.isLocalizationElem hf hg)
  have hpre : i ⁻¹ᵁ (Proj 𝒜).basicOpen r = i ⁻¹ᵁ Proj.basicOpen 𝒜 g :=
    (projectiveAway_preimage_section_basicOpen 𝒜 hf hd _).trans
      (Proj.awayι_preimage_basicOpen 𝒜 hf hd hg he).symm
  have hleft : i ''ᵁ (i ⁻¹ᵁ (Proj 𝒜).basicOpen r) = (Proj 𝒜).basicOpen r := by
    rw [Scheme.Hom.image_preimage_eq_opensRange_inf, Proj.opensRange_awayι]
    exact inf_eq_right.mpr ((Proj 𝒜).basicOpen_le r)
  calc
    (Proj 𝒜).basicOpen r = i ''ᵁ (i ⁻¹ᵁ (Proj 𝒜).basicOpen r) := hleft.symm
    _ = i ''ᵁ (i ⁻¹ᵁ Proj.basicOpen 𝒜 g) := congrArg (fun V => i ''ᵁ V) hpre
    _ = Proj.basicOpen 𝒜 f ⊓ Proj.basicOpen 𝒜 g := by
      rw [Scheme.Hom.image_preimage_eq_opensRange_inf, Proj.opensRange_awayι]

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Projective.FractionBasicOpen
