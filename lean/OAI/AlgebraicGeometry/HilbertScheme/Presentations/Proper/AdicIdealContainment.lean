import OAI.AlgebraicGeometry.HilbertScheme.Presentations.SpectrumIdealCoordinates
import OAI.AlgebraicGeometry.HilbertScheme.Presentations.Ideal.ClosedStalkContainment
import OAI.AlgebraicGeometry.HilbertScheme.Presentations.Proper.ClosedStalkJacobson
import OAI.AlgebraicGeometry.HilbertScheme.Presentations.AdicIdealSeparation

/-! # Adic Ideal Containment -/

namespace OAI.AlgebraicGeometry.HilbertScheme.Presentations.Proper.AdicIdealContainment

noncomputable section

/-! Ideal containment on a proper source is separated with respect to
an ideal in the Jacobson radical of a Noetherian affine base. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u
variable (R : CommRingCat.{u}) [IsNoetherianRing R]
variable {X : Scheme.{u}} (f : X ⟶ Spec R) [IsProper f]

theorem proper_adic_ideal_containment (I : Ideal R)
    (hI : I ≤ Ideal.jacobson (⊥ : Ideal R)) (J : Ideal R) (K : X.IdealSheafData)
    (h : ∀ n : ℕ, K ≤ ((SpectrumIdealCoordinates.spectrumIdealCoordinates R).symm (J ⊔ I ^ n)).comap f) :
    K ≤ ((SpectrumIdealCoordinates.spectrumIdealCoordinates R).symm J).comap f := by
  let : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
  let : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace f
  apply Presentations.Ideal.ClosedStalkContainment.ideal_le_of_closed_localSpectra
  intro x hx
  let A := X.presheaf.stalk x
  let φ : R ⟶ A := Spec.preimage (X.fromSpecStalk x ≫ f)
  have hφ : Spec.map φ = X.fromSpecStalk x ≫ f := Spec.map_preimage _
  let IA := I.map φ.hom
  have hIA : IA ≤ Ideal.jacobson (⊥ : Ideal A) :=
    (ClosedStalkJacobson.proper_closed_stalk_jacobson R f x hx I hI).trans
      (IsLocalRing.maximalIdeal_le_jacobson ⊥)
  apply (SpectrumIdealCoordinates.spectrumIdealCoordinates A).le_iff_le.mp
  rw [← Scheme.IdealSheafData.comap_comp, ← hφ, SpectrumIdealCoordinates.spectrumIdealCoordinates_comap,
    OrderIso.apply_symm_apply]
  apply (AdicIdealSeparation.adic_ideal_le_iff IA hIA _ (J.map φ.hom)).mpr
  intro n
  have hn := Scheme.IdealSheafData.comap_mono (X.fromSpecStalk x) (h n)
  dsimp only at hn
  have hc := (SpectrumIdealCoordinates.spectrumIdealCoordinates A).monotone hn
  rw [← Scheme.IdealSheafData.comap_comp, ← hφ, SpectrumIdealCoordinates.spectrumIdealCoordinates_comap,
    OrderIso.apply_symm_apply, Ideal.map_sup, Ideal.map_pow] at hc
  exact hc

end

end OAI.AlgebraicGeometry.HilbertScheme.Presentations.Proper.AdicIdealContainment
