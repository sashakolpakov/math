import OAI.NumberTheory.PadicHodge.IntegralComparison.Affine.FrobeniusSections
import OAI.NumberTheory.PadicHodge.IntegralComparison.PowerScalarLocalization

/-! # Frobenius Restriction -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Affine.FrobeniusRestriction

noncomputable section

/-! The native affine section isomorphism transports localization to the actual restriction map. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry Opposite

universe u

private theorem cancel_source {R : Type*} [CommRing R] (S : Submonoid R)
    {M N P : ModuleCat.{u} R} (e : M ⟶ N) (f : N ⟶ P) (g : M ⟶ P)
    (h : e ≫ f = g) (he : Function.Bijective e) (hg : IsLocalizedModule S g.hom) :
    IsLocalizedModule S f.hom := by
  apply (IsLocalizedModule.comp_iff_of_bijective_right S e.hom he).mp
  change IsLocalizedModule S ((e ≫ f).hom)
  rw [h]
  exact hg

variable (k C : Type u) [Field k] [Fintype k] [CommRing C] [Algebra k C]

theorem restriction (c : C) (n : ℕ)
    (h : IsLocalizedModule (Submonoid.powers c)
      (FrobeniusSections.map k C (PrimeSpectrum.basicOpen c) n).hom) : IsLocalizedModule (Submonoid.powers c)
    (FrobeniusSections.restrictionMap k C c n).hom :=
  @cancel_source C inferInstance (Submonoid.powers c)
    (Frobenius.DeRhamComplex.forms k C n)
    ((FrobeniusSections.presheaf k C n).obj (op ⊤))
    ((FrobeniusSections.presheaf k C n).obj (op (PrimeSpectrum.basicOpen c)))
    (FrobeniusSections.map k C ⊤ n)
    (FrobeniusSections.restrictionMap k C c n)
    (FrobeniusSections.map k C (PrimeSpectrum.basicOpen c) n)
    (FrobeniusSections.principal_naturality k C c n)
    (FrobeniusSections.top_bijective k C n) h

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Affine.FrobeniusRestriction
