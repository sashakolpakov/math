import OAI.NumberTheory.PadicHodge.IntegralComparison.AffinePrincipal.Cohomology
import OAI.NumberTheory.PadicHodge.IntegralComparison.PurityBaseChangeIdeals
import OAI.NumberTheory.PadicHodge.IntegralComparison.AffinePrincipal.Augmentation

/-! # Oriented Purity -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.AffinePrincipal.OrientedPurity

noncomputable section

/-! The normalized scalar purity coordinate on the actual cohomology
sheaf restricts by the literal quotient map on a principal affine subopen. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry Opposite
open scoped TensorProduct

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u
open OAI.NumberTheory.PadicHodge.IntegralComparison.AffinePrincipal.Sections OAI.NumberTheory.PadicHodge.IntegralComparison.AffineOpen.InternalHom OAI.NumberTheory.PadicHodge.IntegralComparison.AffinePrincipal.LinearHom

variable {X : Scheme.{u}} (U : X.Opens) (hU : IsAffineOpen U) (r : Γ(X, U))

include hU in
theorem regular {c : ℕ} (s : Fin c → Γ(X, U))
    (hreg : RingTheory.Sequence.IsWeaklyRegular Γ(X, U) (List.ofFn s)) :
    RingTheory.Sequence.IsWeaklyRegular Γ(X, Sections.openSubset U r)
      (List.ofFn (algebraMap Γ(X, U) Γ(X, Sections.openSubset U r) ∘ s)) := by
  let : IsLocalization.Away r Γ(X, Sections.openSubset U r) := hU.isLocalization_basicOpen r
  let : Module.Flat Γ(X, U) Γ(X, Sections.openSubset U r) :=
    IsLocalization.flat Γ(X, Sections.openSubset U r) (Submonoid.powers r)
  exact Koszul.AugmentationBaseChange.regular Γ(X, U) Γ(X, Sections.openSubset U r) s hreg

variable (N : X.Modules) [N.IsQuasicoherent] (K : ChainComplex X.Modules ℕ)
  [∀ i, (K.X i).IsQuasicoherent]
  [∀ i, Module.Free Γ(X, U) ((AffineOpen.InternalHom.sections U hU).obj (K.X i))]
  [∀ i, Module.Finite Γ(X, U) ((AffineOpen.InternalHom.sections U hU).obj (K.X i))]
  [∀ i, Projective ((AffineOpen.InternalHom.sections U hU).obj (K.X i))]
  [∀ i, Projective ((AffineOpen.InternalHom.sections (Sections.openSubset U r) (hU.basicOpen r)).obj (K.X i))]
  [∀ i, ((Affine.LinearResolutionPurity.internalComplex N K).X i).IsQuasicoherent]
  (M : X.Modules) [M.IsQuasicoherent]
  (ε : K ⟶ (ChainComplex.single₀ X.Modules).obj M) [QuasiIso ε]
  (I : Ideal Γ(X, U)) (J : Ideal Γ(X, Sections.openSubset U r))
  (hIJ : I ≤ J.comap (algebraMap Γ(X, U) Γ(X, Sections.openSubset U r)))
  (eM : (AffineOpen.InternalHom.sections U hU).obj M ≅ ModuleCat.of Γ(X, U) (Γ(X, U) ⧸ I))
  (eM' : (AffineOpen.InternalHom.sections (Sections.openSubset U r) (hU.basicOpen r)).obj M ≅
    ModuleCat.of Γ(X, Sections.openSubset U r) (Γ(X, Sections.openSubset U r) ⧸ J))
  (he : (Hom.Comparison.chartIso U hU r M).hom ≫ eM'.hom =
    (PrincipalComplex.tensorFunctor U r).map eM.hom ≫ ModuleCat.ofHom
      (PurityBaseChangeIdeals.Linear.tensorQuotient Γ(X, U) Γ(X, Sections.openSubset U r) I J hIJ))
  {c : ℕ} (s : Fin c → Γ(X, U))
  (hs : Koszul.OrientedTopCohomology.ideal Γ(X, U) s = I)
  (ht : Koszul.OrientedTopCohomology.ideal Γ(X, Sections.openSubset U r)
    (algebraMap Γ(X, U) Γ(X, Sections.openSubset U r) ∘ s) = J)
  (hreg : RingTheory.Sequence.IsWeaklyRegular Γ(X, U) (List.ofFn s))
  (e : (AffineOpen.InternalHom.sections U hU).obj N ≅ ModuleCat.of Γ(X, U) Γ(X, U))

include he in
omit [∀ (i : ℕ), ((Affine.LinearResolutionPurity.internalComplex N K).X i).IsQuasicoherent] in
theorem linear_purity
    (x : (LinearHomBaseChange.homComplex Γ(X, U)
      (Affine.OrientedPurity.resolution U hU K M ε I eM).complex
      ((AffineOpen.InternalHom.sections U hU).obj N)).homology c) :
    (LinearHomOrientedPurity.iso Γ(X, Sections.openSubset U r) J
      (algebraMap Γ(X, U) Γ(X, Sections.openSubset U r) ∘ s) ht (regular U hU r s hreg)
      (Affine.OrientedPurity.resolution (Sections.openSubset U r) (hU.basicOpen r) K M ε J eM')
      ((AffineOpen.InternalHom.sections (Sections.openSubset U r) (hU.basicOpen r)).obj N) (LinearHom.targetFrame U hU r N e)).hom
      ((Cohomology.Comparison.baseChange U hU N K r e c).hom
        (1 ⊗ₜ[Γ(X, U)] x)) =
    PurityBaseChangeIdeals.Linear.quotientMap Γ(X, U) Γ(X, Sections.openSubset U r) I J hIJ
      ((LinearHomOrientedPurity.iso Γ(X, U) I s hs hreg
        (Affine.OrientedPurity.resolution U hU K M ε I eM)
        ((AffineOpen.InternalHom.sections U hU).obj N) e).hom x) := by

  let : IsLocalization.Away r Γ(X, Sections.openSubset U r) := hU.isLocalization_basicOpen r
  let : Module.Flat Γ(X, U) Γ(X, Sections.openSubset U r) :=
    IsLocalization.flat Γ(X, Sections.openSubset U r) (Submonoid.powers r)
  let P := Affine.OrientedPurity.resolution U hU K M ε I eM
  let P' := Affine.OrientedPurity.resolution (Sections.openSubset U r) (hU.basicOpen r) K M ε J eM'
  let (i : ℕ) : Module.Free Γ(X, U) (P.complex.X i) :=
    inferInstanceAs (Module.Free Γ(X, U) ((AffineOpen.InternalHom.sections U hU).obj (K.X i)))
  let (i : ℕ) : Module.Finite Γ(X, U) (P.complex.X i) :=
    inferInstanceAs (Module.Finite Γ(X, U) ((AffineOpen.InternalHom.sections U hU).obj (K.X i)))
  let eP : ((PrincipalComplex.tensorFunctor U r).mapHomologicalComplex (.down ℕ)).obj
      P.complex ≅ P'.complex := PrincipalComplex.chartIso U hU r (.down ℕ) K
  have hP := Augmentation.augmentation_square U hU r K M ε I J eM eM'
    (ModuleCat.ofHom (PurityBaseChangeIdeals.Linear.tensorQuotient
      Γ(X, U) Γ(X, Sections.openSubset U r) I J hIJ)) he
  have hp := PurityBaseChangeIdeals.Linear.purity Γ(X, U) Γ(X, Sections.openSubset U r)
    I J hIJ s hs ht hreg P P' eP hP ((AffineOpen.InternalHom.sections U hU).obj N)
    ((AffineOpen.InternalHom.sections (Sections.openSubset U r) (hU.basicOpen r)).obj N) e (LinearHom.targetFrame U hU r N e) 1
    x
  rw [one_smul] at hp
  exact hp

omit [∀ i, Projective ((AffineOpen.InternalHom.sections U hU).obj (K.X i))]
  [∀ i, Projective ((AffineOpen.InternalHom.sections (Sections.openSubset U r) (hU.basicOpen r)).obj (K.X i))] in
theorem comparison_restriction
    (z : Γ((Affine.LinearResolutionPurity.internalComplex N K).homology c, U)) :
    (Cohomology.Comparison.baseChange U hU N K r e c).hom
      (1 ⊗ₜ[Γ(X, U)] (Cohomology.Comparison.comparison U hU N K c).hom z) =
    (Cohomology.Comparison.comparison (Sections.openSubset U r) (hU.basicOpen r) N K c).hom
      (((Affine.LinearResolutionPurity.internalComplex N K).homology c).presheaf.map
        (Sections.inclusion U r).op z) := by
  have hn := Cohomology.Comparison.naturality U hU N K r e c
  have hx := ConcreteCategory.congr_hom hn (1 ⊗ₜ[Γ(X, U)] z)
  change (Cohomology.Comparison.baseChange U hU N K r e c).hom
      (1 ⊗ₜ[Γ(X, U)] (Cohomology.Comparison.comparison U hU N K c).hom z) =
    (Cohomology.Comparison.comparison (Sections.openSubset U r) (hU.basicOpen r) N K c).hom
      (Homology.component U r
        ((Affine.LinearResolutionPurity.internalComplex N K).homology c) (1 ⊗ₜ[Γ(X, U)] z)) at hx
  rw [Homology.component_tmul, one_smul] at hx
  exact hx

include he in
theorem restriction (z : Γ((Affine.LinearResolutionPurity.internalComplex N K).homology c, U)) :
    (Affine.OrientedPurity.iso (Sections.openSubset U r) (hU.basicOpen r) N K M ε J eM'
      (algebraMap Γ(X, U) Γ(X, Sections.openSubset U r) ∘ s) ht (regular U hU r s hreg)
      (LinearHom.targetFrame U hU r N e)).hom
      (((Affine.LinearResolutionPurity.internalComplex N K).homology c).presheaf.map
        (Sections.inclusion U r).op z) =
    PurityBaseChangeIdeals.Linear.quotientMap Γ(X, U) Γ(X, Sections.openSubset U r) I J hIJ
      ((Affine.OrientedPurity.iso U hU N K M ε I eM s hs hreg e).hom z) := by
  have hp := linear_purity U hU r N K M ε I J hIJ eM eM' he s hs ht hreg e
    ((Cohomology.Comparison.comparison U hU N K c).hom z)
  have hx := comparison_restriction U hU r N K e z
  rw [hx] at hp
  exact hp

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.AffinePrincipal.OrientedPurity
