import OAI.AlgebraicGeometry.Crystalline.Cohomology.BaseAffine.OrdinaryFormSections
import OAI.AlgebraicGeometry.Crystalline.Cohomology.OrdinaryFormEq
import OAI.NumberTheory.PadicHodge.IntegralComparison.Affine.LocalizingModule
import OAI.NumberTheory.PadicHodge.IntegralComparison.DifferentialFormFiniteness

/-! # Ordinary Form Coherence -/

namespace OAI.AlgebraicGeometry.Crystalline.Cohomology.BaseAffine.OrdinaryFormCoherence.BaseAffineOrdinaryFormCoherence

noncomputable section

/-! # Ordinary form sheaves are coherent on etale-coordinate affine charts over any commutative base -/

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

variable (k A : Type u) [CommRing k] [CommRing A] [Algebra k A]

theorem finiteTop [Algebra.FiniteType k A] (n : ℕ) :
    Module.Finite A ((OrdinaryFormSections.BaseAffineOrdinaryFormSections.presheaf k A n).obj (op ⊤)) := by
  let : Module.Finite A (DeRhamPresentationTo.DeRhamPresentation.Form k A n) := NumberTheory.PadicHodge.IntegralComparison.DifferentialFormFiniteness.forms_finite k A n
  let f : DeRhamPresentationTo.DeRhamPresentation.Form k A n →ₗ[A]
      ((OrdinaryFormSections.BaseAffineOrdinaryFormSections.presheaf k A n).obj (op ⊤)) :=
    (OrdinaryFormSections.BaseAffineOrdinaryFormSections.map k A ⊤ n).hom
  exact Module.Finite.of_surjective f
    (OrdinaryFormSections.BaseAffineOrdinaryFormSections.top_bijective k A n).surjective

variable (σ : Type u) [LinearOrder σ] [Algebra (MvPolynomial σ k) A]
  [IsScalarTower k (MvPolynomial σ k) A] [Algebra.FormallyEtale (MvPolynomial σ k) A]

include σ in
theorem principal_map (a : A) (n : ℕ) : IsLocalizedModule (Submonoid.powers a)
    (OrdinaryFormSections.BaseAffineOrdinaryFormSections.map k A (PrimeSpectrum.basicOpen a) n).hom := by
  let U : (Spec (CommRingCat.of A)).Opens := PrimeSpectrum.basicOpen a
  let B : CommAlgCat.{u} k :=
    (AlgebraicForms.AlgebraicDeRham.sectionAlgebras k (SectionTowers.BaseAffineSectionTowers.affineScheme k A)).obj (op U)
  let : Algebra A B := SectionTowers.BaseAffineSectionTowers.coordinateAlgebra A U
  let : IsScalarTower k A B := SectionTowers.BaseAffineSectionTowers.tower k A U
  let : Algebra (MvPolynomial σ k) B := SectionCoordinates.BaseAffineSectionCoordinates.polynomialAlgebra k A σ U
  let : IsScalarTower k (MvPolynomial σ k) B := SectionCoordinates.BaseAffineSectionCoordinates.base_tower k A σ U
  let : IsScalarTower (MvPolynomial σ k) A B := SectionCoordinates.BaseAffineSectionCoordinates.coordinate_tower k A σ U
  let : Algebra.FormallyEtale (MvPolynomial σ k) B := SectionCoordinates.BaseAffineSectionCoordinates.principal_etale k A σ a
  let : IsLocalization.Away a B := NumberTheory.PadicHodge.IntegralComparison.Affine.CoordinateSections.principal_localization A a
  exact OrdinaryFormEq.OrdinaryFormScalarLocalization.localized k A B σ (Submonoid.powers a) n

include σ in
theorem restriction (a : A) (n : ℕ) : IsLocalizedModule (Submonoid.powers a)
    (OrdinaryFormSections.BaseAffineOrdinaryFormSections.restrictionMap k A a n).hom :=
  cancel_source (Submonoid.powers a)
    (OrdinaryFormSections.BaseAffineOrdinaryFormSections.map k A ⊤ n) (OrdinaryFormSections.BaseAffineOrdinaryFormSections.restrictionMap k A a n)
    (OrdinaryFormSections.BaseAffineOrdinaryFormSections.map k A (PrimeSpectrum.basicOpen a) n)
    (OrdinaryFormSections.BaseAffineOrdinaryFormSections.principal_naturality k A a n)
    (OrdinaryFormSections.BaseAffineOrdinaryFormSections.top_bijective k A n) (principal_map k A σ a n)

include σ in
theorem quasicoherent (n : ℕ) :
    (OrdinaryFormBase.OrdinaryFormModulePresheaf.sheaf k (SectionTowers.BaseAffineSectionTowers.affineScheme k A) n).IsQuasicoherent :=
  NumberTheory.PadicHodge.IntegralComparison.Affine.LocalizingModule.quasicoherent A
    (OrdinaryFormBase.OrdinaryFormModulePresheaf.presheaf k
      (AlgebraicForms.AlgebraicDeRham.sectionAlgebras k (SectionTowers.BaseAffineSectionTowers.affineScheme k A)) n)
    (fun a => restriction k A σ a n)

include σ in
theorem finiteType [Algebra.FiniteType k A] (n : ℕ) :
    (OrdinaryFormBase.OrdinaryFormModulePresheaf.sheaf k (SectionTowers.BaseAffineSectionTowers.affineScheme k A) n).IsFiniteType := by
  let : Module.Finite A ((NumberTheory.PadicHodge.IntegralComparison.Affine.LocalizingModule.scalars A
      (OrdinaryFormBase.OrdinaryFormModulePresheaf.presheaf k
        (AlgebraicForms.AlgebraicDeRham.sectionAlgebras k (SectionTowers.BaseAffineSectionTowers.affineScheme k A)) n)).obj (op ⊤)) :=
    finiteTop k A n
  exact NumberTheory.PadicHodge.IntegralComparison.Affine.LocalizingModule.finiteType A
    (OrdinaryFormBase.OrdinaryFormModulePresheaf.presheaf k
      (AlgebraicForms.AlgebraicDeRham.sectionAlgebras k (SectionTowers.BaseAffineSectionTowers.affineScheme k A)) n)
    (fun a => restriction k A σ a n)

omit [Algebra.FormallyEtale (MvPolynomial σ k) A] in
include σ in
theorem finiteType_etale [Fintype σ] [Algebra.Etale (MvPolynomial σ k) A] (n : ℕ) :
    (OrdinaryFormBase.OrdinaryFormModulePresheaf.sheaf k (SectionTowers.BaseAffineSectionTowers.affineScheme k A) n).IsFiniteType := by
  let : Algebra.FiniteType k A := Algebra.FiniteType.trans (S := MvPolynomial σ k) inferInstance inferInstance
  exact finiteType k A σ n

end

end OAI.AlgebraicGeometry.Crystalline.Cohomology.BaseAffine.OrdinaryFormCoherence.BaseAffineOrdinaryFormCoherence
