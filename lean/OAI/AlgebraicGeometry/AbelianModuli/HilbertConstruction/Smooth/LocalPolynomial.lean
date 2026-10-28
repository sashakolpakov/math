import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Noetherian.LocalCoefficientPolynomial
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Smooth.ProjectiveFamilyDescent

/-! # Local Polynomial -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction

noncomputable section

/-! Smooth projective families over arbitrary local rings have one field-fiber Hilbert polynomial. A constructed Noetherian coefficient model is localized at the image of the closed point. -/
open _root_.CategoryTheory _root_.AlgebraicGeometry
universe u

theorem Closed.Families.FlatClosedFamily.noetherianModel_localCoefficientFieldHilbertPolynomial
    {C R : Type u} [CommRing C] [IsNoetherianRing C] [CommRing R] [IsLocalRing R] {n : ℕ}
    (G : Closed.Families.FlatClosedFamily (Projective.ProjectivePresentations.affineProjectiveSpace C n)) (ψ : CommRingCat.of C ⟶ CommRingCat.of R) :
    ∃ P : Polynomial ℚ, ∀ (K : Type u) [Field K] (φ : CommRingCat.of R ⟶ CommRingCat.of K),
      HilbertScheme.Presentations.Hilbert.Polynomial.GradedHilbert.HasHilbertPolynomial (Closed.Families.FlatClosedFamily.homogeneousIdeal (R := K) (n := n) ((G.coefficientPullback ψ).coefficientPullback φ)).toIdeal P := by
  let S := Spec (.of C)
  let b := Spec.map ψ
  let s := b (IsLocalRing.closedPoint R)
  let c := S.fromSpecStalk s
  let σ : CommRingCat.of C ⟶ CommRingCat.of (S.presheaf.stalk s) := (Spec.fullyFaithful.preimage c).unop
  let χ : CommRingCat.of (S.presheaf.stalk s) ⟶ CommRingCat.of R := Scheme.stalkClosedPointTo b
  have hσ : Spec.map σ = c := Spec.fullyFaithful.map_preimage c
  have hσχ : σ ≫ χ = ψ := by
    apply Spec.map_injective
    rw [Spec.map_comp, hσ]
    exact Scheme.Spec_stalkClosedPointTo_fromSpecStalk b
  have hN : IsNoetherianRing (S.presheaf.stalk s) :=
    AlgebraicGeometry.instIsNoetherianRingCarrierStalkCommRingCatPresheafOfIsLocallyNoetherian
      (X := S) (x := s)
  have hlocal : IsLocalRing (S.presheaf.stalk s) := S.toLocallyRingedSpace.isLocalRing s
  obtain ⟨P, hP⟩ := @Closed.Families.FlatClosedFamily.exists_localCoefficientFieldHilbertPolynomial
    (S.presheaf.stalk s) _ hN hlocal n (G.coefficientPullback σ)
  refine ⟨P, fun K _ φ => ?_⟩
  have he : (G.coefficientPullback ψ).coefficientPullback φ =
      (G.coefficientPullback σ).coefficientPullback (χ ≫ φ) := by
    exact (Closed.Families.FlatClosedFamily.coefficientPullback_comp G ψ φ).trans
      ((congrArg (fun z => G.coefficientPullback z)
        ((congrArg (fun z => z ≫ φ) hσχ).symm.trans (Category.assoc σ χ φ))).trans
          (Closed.Families.FlatClosedFamily.coefficientPullback_comp G σ (χ ≫ φ)).symm)
  rw [he]
  exact hP K (χ ≫ φ)

theorem Closed.Families.FlatClosedFamily.smooth_exists_localCoefficientFieldHilbertPolynomial
    {R : Type u} [CommRing R] [IsLocalRing R] {n : ℕ}
    (F : Closed.Families.FlatClosedFamily (Projective.ProjectivePresentations.affineProjectiveSpace R n)) [Smooth F.scheme.hom] :
    ∃ P : Polynomial ℚ, ∀ (K : Type u) [Field K] (φ : CommRingCat.of R ⟶ CommRingCat.of K),
      HilbertScheme.Presentations.Hilbert.Polynomial.GradedHilbert.HasHilbertPolynomial (Closed.Families.FlatClosedFamily.homogeneousIdeal (R := K) (n := n) (F.coefficientPullback φ)).toIdeal P := by
  obtain ⟨C, _, hC, G, _, hF⟩ := F.exists_smooth_noetherian_projective_family
  have := hC
  let ψ : CommRingCat.of C ⟶ CommRingCat.of R := CommRingCat.ofHom C.val.toRingHom
  have hF' : F = G.coefficientPullback ψ := hF
  rw [hF']
  exact Closed.Families.FlatClosedFamily.noetherianModel_localCoefficientFieldHilbertPolynomial G ψ

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction
