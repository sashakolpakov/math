import OAI.RepresentationTheory.Theta.Geometric.Affine.QuotientProjection
import OAI.RepresentationTheory.Theta.Geometric.QuotientJacobianFlatness

/-! # Quotient Spec Projection -/

namespace OAI.RepresentationTheory.Theta.Geometric.Affine.QuotientSpecProjection

noncomputable section

/-! Quotient projections to Spec R use the literal ring R, through the
canonical global-function map supplied by the spectrum adjunction. -/

set_option backward.isDefEq.respectTransparency false
open _root_.AlgebraicGeometry _root_.CategoryTheory KaehlerDifferential

universe u

theorem affineQuotientComposite_toSpec {S : Scheme.{u}} [IsAffine S]
    {R : Type u} [CommRing R] (p : S ⟶ Spec (.of R)) (I : Ideal Γ(S, ⊤)) :
    (QuotientPoints.affineQuotientScheme S I).hom ≫ p = Spec.map (CommRingCat.ofHom
      ((Ideal.Quotient.mk I).comp (AlgebraicGeometry.FormalGeometry.Completion.Affine.BaseAlgebraPoints.Construction.globalRingPointEquiv S (.of R) p))) := by
  let q := (QuotientPoints.affineQuotientScheme S I).hom
  calc
    q ≫ p = ((q ≫ p) ≫ (Spec (.of R)).toSpecΓ) ≫ Spec.map (Scheme.ΓSpecIso (.of R)).inv := by
      rw [Category.assoc, toSpecΓ_SpecMap_ΓSpecIso_inv, Category.comp_id]
    _ = Spec.map (CommRingCat.ofHom ((Ideal.Quotient.mk I).comp p.appTop.hom)) ≫
        Spec.map (Scheme.ΓSpecIso (.of R)).inv := by
      rw [Category.assoc q p, QuotientProjection.affineQuotientComposite_spec]
    _ = _ := (Spec.map_comp (Scheme.ΓSpecIso (.of R)).inv
      (CommRingCat.ofHom ((Ideal.Quotient.mk I).comp p.appTop.hom))).symm

theorem affineQuotientProjection_toSpec_flat {S : Scheme.{u}} [IsAffine S]
    [IsLocalRing Γ(S, ⊤)] [IsNoetherianRing Γ(S, ⊤)]
    {R : Type u} [CommRing R] (p : S ⟶ Spec (.of R)) (I : Ideal Γ(S, ⊤)) (hI : I ≠ ⊤)
    [FormallyUnramified ((QuotientPoints.affineQuotientScheme S I).hom ≫ p)] :
    letI : Algebra R Γ(S, ⊤) := (AlgebraicGeometry.FormalGeometry.Completion.Affine.BaseAlgebraPoints.Construction.globalRingPointEquiv S (.of R) p).toAlgebra
    ∀ [Algebra.FormallySmooth R Γ(S, ⊤)] [Module.Flat R Γ(S, ⊤)]
      [Module.Free Γ(S, ⊤) Ω[Γ(S, ⊤)⁄R]] [Module.Finite Γ(S, ⊤) Ω[Γ(S, ⊤)⁄R]],
      ∀ {n : ℕ} (v : Fin n → Γ(S, ⊤)), Ideal.span (Set.range v) = I →
        n ≤ Module.finrank Γ(S, ⊤) Ω[Γ(S, ⊤)⁄R] →
        Flat ((QuotientPoints.affineQuotientScheme S I).hom ≫ p) := by
  let : Algebra R Γ(S, ⊤) := (AlgebraicGeometry.FormalGeometry.Completion.Affine.BaseAlgebraPoints.Construction.globalRingPointEquiv S (.of R) p).toAlgebra
  intro _ _ _ _ n v hv hn
  have he : (QuotientPoints.affineQuotientScheme S I).hom ≫ p =
      Spec.map (CommRingCat.ofHom (algebraMap R (Γ(S, ⊤) ⧸ I))) := affineQuotientComposite_toSpec p I
  have : FormallyUnramified (Spec.map (CommRingCat.ofHom (algebraMap R (Γ(S, ⊤) ⧸ I)))) := by
    rw [← he]
    infer_instance
  rw [he]
  exact QuotientJacobianFlatness.quotientSpec_flat_of_few_equations I hI v hv hn

end

end OAI.RepresentationTheory.Theta.Geometric.Affine.QuotientSpecProjection
