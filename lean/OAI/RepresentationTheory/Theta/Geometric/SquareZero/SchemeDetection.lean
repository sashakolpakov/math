import OAI.RepresentationTheory.Theta.Geometric.SquareZero.AffineDetection
import OAI.RepresentationTheory.Theta.Geometric.SquareZero.Spectrum
import Mathlib.AlgebraicGeometry.OpenImmersion

/-! # Scheme Detection -/

namespace OAI.RepresentationTheory.Theta.Geometric.SquareZero.SchemeDetection

noncomputable section

/-! Actual maps from an arbitrary split square-zero complex test are
determined by all of its ordinary dual-number linear quotients. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

variable {M : Type} [AddCommGroup M] [Module ℂ M] [Module ℂᵐᵒᵖ M] [IsCentralScalar ℂ M]

theorem squareZero_scheme_maps_ext (X : Scheme)
    (f g : Spec (.of (TrivSqZeroExt ℂ M)) ⟶ X)
    (h : ∀ l : M →ₗ[ℂ] ℂ,
      Spec.map (CommRingCat.ofHom (TrivSqZeroExt.map l).toRingHom) ≫ f =
        Spec.map (CommRingCat.ofHom (TrivSqZeroExt.map l).toRingHom) ≫ g) : f = g := by
  let : Subsingleton (Spec (.of (TrivSqZeroExt ℂ M))) := Spectrum.squareZero_primeSpectrum_subsingleton
  let d : Spec (.of (DualNumber ℂ)) :=
    PrimeSpectrum.comap (TrivSqZeroExt.fstHom ℂ ℂ ℂ).toRingHom (⊥ : PrimeSpectrum ℂ)
  let q := (Spec.map (CommRingCat.ofHom (TrivSqZeroExt.map (0 : M →ₗ[ℂ] ℂ)).toRingHom)) d
  have hfgq : f q = g q := congrArg (fun a : Spec (.of (DualNumber ℂ)) ⟶ X => a d) (h 0)
  obtain ⟨U, hU, hfU, _⟩ := exists_isAffineOpen_mem_and_subset
    (show f q ∈ (⊤ : X.Opens) by trivial)
  let : IsAffine U.toScheme := hU
  have hRf : Set.range f ⊆ Set.range U.ι := by
    rintro _ ⟨v, rfl⟩
    have hv : f v ∈ U := (congrArg f (Subsingleton.elim q v)) ▸ hfU
    exact ⟨⟨f v, hv⟩, rfl⟩
  have hRg : Set.range g ⊆ Set.range U.ι := by
    rintro _ ⟨v, rfl⟩
    have hv : g v ∈ U := (hfgq.trans (congrArg g (Subsingleton.elim q v))) ▸ hfU
    exact ⟨⟨g v, hv⟩, rfl⟩
  let f' := IsOpenImmersion.lift U.ι f hRf
  let g' := IsOpenImmersion.lift U.ι g hRg
  have hf : f' ≫ U.ι = f := IsOpenImmersion.lift_fac U.ι f hRf
  have hg : g' ≫ U.ι = g := IsOpenImmersion.lift_fac U.ι g hRg
  have he : f' = g' := by
    apply AffineDetection.squareZero_affine_maps_ext
    intro l
    apply (cancel_mono U.ι).mp
    rw [Category.assoc, Category.assoc, hf, hg]
    exact h l
  exact hf.symm.trans ((congrArg (fun a => a ≫ U.ι) he).trans hg)

end

end OAI.RepresentationTheory.Theta.Geometric.SquareZero.SchemeDetection
