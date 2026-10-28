import OAI.NumberTheory.PadicHodge.GeometricComparison.Affine.OverSpec
import OAI.NumberTheory.PadicHodge.GeometricComparison.Affine.CechSectionEpi

/-! # Chart Section Epi -/

namespace OAI.NumberTheory.PadicHodge.GeometricComparison.Affine.ChartSectionEpi.AffineCechAcyclic

noncomputable section

/-! The affine Čech condition gives surjectivity on sections of every actual affine chart over the base. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry Opposite

theorem spectrum_image_one (A : CommRingCat) {Y : Scheme} (f : Spec A ⟶ Y) [IsIso f] :
    f ''ᵁ (PrimeSpectrum.basicOpen (1 : A)) = ⊤ := by
  have ht : (PrimeSpectrum.basicOpen (1 : A) : (Spec A).Opens) = ⊤ := PrimeSpectrum.basicOpen_one
  exact (congrArg (fun U : (Spec A).Opens => f ''ᵁ U) ht).trans
    ((Scheme.Hom.image_top_eq_opensRange f).trans (Scheme.Hom.opensRange_of_isIso f))

variable (R : Type) [CommRing R] (X : Over (Spec (CommRingCat.of R)))
  [IsAffine X.left] [Algebra ℚ Γ(X.left, ⊤)]

local instance : Algebra R Γ(X.left, ⊤) := AlgebraicGeometry.Crystalline.Cohomology.AlgebraicForms.AlgebraicDeRham.sectionAlgebra R X ⊤

theorem affine_section_epi
    (S : ShortComplex (AlgebraicGeometry.Crystalline.Cohomology.DeRhamGlobalId.DeRhamGlobal.Sheaves R X)) (hS : S.ShortExact)
    (hA : CechAcyclic.AffineCechAcyclic.Acyclic R X S.X₁) : Epi (S.g.hom.app (op ⊤)) := by
  let f : RelativeSectionCoefficients.AffineCoordinates.relativeSpecModel R Γ(X.left, ⊤) ⟶ X := (OverSpec.AffineOverSpec.iso R X).inv
  have : IsIso f := (OverSpec.AffineOverSpec.iso R X).isIso_inv
  have hleftIso : IsIso f.left := (Over.forget _).map_isIso f
  have : IsOpenImmersion f.left := inferInstance
  have h := CechSectionEpi.AffineCechAcyclic.principal_section_epi R X S hS hA Γ(X.left, ⊤) f 1
  have he : f.left ''ᵁ (PrimeSpectrum.basicOpen (1 : Γ(X.left, ⊤))) = (⊤ : X.left.Opens) :=
    @spectrum_image_one (CommRingCat.of Γ(X.left, ⊤)) X.left f.left hleftIso
  change Epi (S.g.hom.app (op (f.left ''ᵁ (PrimeSpectrum.basicOpen (1 : Γ(X.left, ⊤)))))) at h
  exact he ▸ h

end

end OAI.NumberTheory.PadicHodge.GeometricComparison.Affine.ChartSectionEpi.AffineCechAcyclic
