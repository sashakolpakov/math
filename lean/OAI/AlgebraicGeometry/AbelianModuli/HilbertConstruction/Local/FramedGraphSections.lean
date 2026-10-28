import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Affine.EmbeddedTorsionDetection
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.GraphPower.BasisGeometricCompleteness
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.GraphPower.SectionsProjective
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Local.SpectrumLineBundleFrames
import Mathlib.RingTheory.LocalRing.Module

/-! # Framed Graph Sections -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction

noncomputable section

/-! On a local noetherian affine base, the complete basis and all
torsion fiber frames required for section detection exist. The basis
comes from the proved finite projectivity of positive graph sections. -/
open _root_.CategoryTheory _root_.AlgebraicGeometry
universe u
variable {R : Type u} [CommRing R] [IsLocalRing R]
variable [IsNoetherianRing Γ(Spec (.of R), ⊤)]
variable {g N n : ℕ} {δ : Fin g → ℕ}
variable (A : PolarizationData.PolarizedAbelianWithFullLevel g δ N (Spec (.of R)))

theorem PolarizationData.PolarizedAbelianWithFullLevel.local_exists_completeFramedEvenGraphSections
    (hN : 3 ≤ N) (hunit : IsUnit (N : Γ(Spec (.of R), ⊤)))
    (level : A.abelian.FullLevel n) (t : ℕ) (ht : 0 < t) :
    Nonempty (A.CompleteFramedEvenGraphSections level t) := by
  let C := Γ(Spec (.of R), ⊤)
  let e := (Scheme.ΓSpecIso (.of R)).commRingCatIsoToRingEquiv
  have : Nontrivial C := ⟨⟨e.symm 0, e.symm 1, e.symm.injective.ne zero_ne_one⟩⟩
  have : IsLocalRing C := IsLocalRing.of_surjective' e.symm.toRingHom e.symm.surjective
  let L := A.graphBundle.tensorPower (2 * t)
  let V := (Coefficient.GlobalSectionsFunctor.coefficientGlobalSectionsFunctor A.abelian.scheme.hom.appTop.hom).obj L.sheaf
  obtain ⟨hf, hp⟩ := A.graphBundle_positivePower_sections_finite_projective hN hunit
    (2 * t) (Nat.mul_pos (by decide) ht)
  have : Module.Finite C V := hf
  have : Module.Projective C V := hp
  have : Module.Free C V := Module.free_of_flat_of_isLocalRing
  let b := Module.finBasis C V
  refine ⟨{
    rank := Module.finrank C V
    basis := Affine.CoefficientSectionBasis.affineCoefficientSectionBasis A.abelian.scheme.hom L.sheaf b
    geometricComplete := ?_
    frames := fun c => Local.SpectrumLineBundleFrames.localSpectrumLineBundleIso
      (L.pullback (A.abelian.fullLevelGlobalSection level c)) }⟩
  rw [Affine.CoefficientSectionBasis.affineCoefficientSectionBasis_family]
  exact A.graphPower_coefficientBasis_geometricComplete hN hunit
    (2 * t) (Nat.mul_pos (by decide) ht) b

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction
