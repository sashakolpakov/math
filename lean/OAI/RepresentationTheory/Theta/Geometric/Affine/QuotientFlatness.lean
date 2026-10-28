import OAI.RepresentationTheory.Theta.Geometric.Affine.QuotientProjection
import OAI.RepresentationTheory.Theta.Geometric.QuotientJacobianFlatness

/-! # Quotient Flatness -/

namespace OAI.RepresentationTheory.Theta.Geometric.Affine.QuotientFlatness

noncomputable section

/-! The local equation bound proves flatness of the actual quotient
projection over an affine base, through its canonical ring map. -/

set_option backward.isDefEq.respectTransparency false
open _root_.AlgebraicGeometry _root_.CategoryTheory KaehlerDifferential

universe u

theorem affineQuotientProjection_flat {B S : Scheme.{u}} [IsAffine B] [IsAffine S]
    [IsLocalRing Γ(S, ⊤)] [IsNoetherianRing Γ(S, ⊤)]
    (p : S ⟶ B) (I : Ideal Γ(S, ⊤)) (hI : I ≠ ⊤)
    [FormallyUnramified ((QuotientPoints.affineQuotientScheme S I).hom ≫ p)] :
    letI : Algebra Γ(B, ⊤) Γ(S, ⊤) := p.appTop.hom.toAlgebra
    ∀ [Algebra.FormallySmooth Γ(B, ⊤) Γ(S, ⊤)] [Module.Flat Γ(B, ⊤) Γ(S, ⊤)]
      [Module.Free Γ(S, ⊤) Ω[Γ(S, ⊤)⁄Γ(B, ⊤)]] [Module.Finite Γ(S, ⊤) Ω[Γ(S, ⊤)⁄Γ(B, ⊤)]],
      ∀ {n : ℕ} (v : Fin n → Γ(S, ⊤)), Ideal.span (Set.range v) = I →
        n ≤ Module.finrank Γ(S, ⊤) Ω[Γ(S, ⊤)⁄Γ(B, ⊤)] →
        Flat ((QuotientPoints.affineQuotientScheme S I).hom ≫ p) := by
  let : Algebra Γ(B, ⊤) Γ(S, ⊤) := p.appTop.hom.toAlgebra
  intro _ _ _ _ n v hv hn
  let q := (QuotientPoints.affineQuotientScheme S I).hom
  have he : (q ≫ p) ≫ B.toSpecΓ =
      Spec.map (CommRingCat.ofHom (algebraMap Γ(B, ⊤) (Γ(S, ⊤) ⧸ I))) := by
    rw [Category.assoc]
    exact QuotientProjection.affineQuotientComposite_spec p I
  have hu : FormallyUnramified ((q ≫ p) ≫ B.toSpecΓ) :=
    MorphismProperty.comp_mem _ _ _ inferInstance inferInstance
  have : FormallyUnramified (Spec.map (CommRingCat.ofHom (algebraMap Γ(B, ⊤) (Γ(S, ⊤) ⧸ I)))) :=
    he ▸ hu
  have hf := QuotientJacobianFlatness.quotientSpec_flat_of_few_equations (R := Γ(B, ⊤)) I hI v hv hn
  have : Flat ((q ≫ p) ≫ B.toSpecΓ) := he.symm ▸ hf
  exact (MorphismProperty.cancel_right_of_respectsIso (P := @Flat) (q ≫ p) B.toSpecΓ).mp this

theorem overIso_projection_flat {B S : Scheme.{u}} (p : S ⟶ B)
    (M N : Over S) (e : M ≅ N) [Flat (N.hom ≫ p)] : Flat (M.hom ≫ p) := by
  have : IsIso e.hom.left := (Over.forget S).map_isIso e.hom
  have he : M.hom ≫ p = e.hom.left ≫ (N.hom ≫ p) := by
    rw [← Category.assoc, e.hom.w]
  rw [he]
  infer_instance

theorem overIso_projection_formallyUnramified {B S : Scheme.{u}} (p : S ⟶ B)
    (M N : Over S) (e : M ≅ N) [FormallyUnramified (N.hom ≫ p)] :
    FormallyUnramified (M.hom ≫ p) := by
  have : IsIso e.hom.left := (Over.forget S).map_isIso e.hom
  have he : M.hom ≫ p = e.hom.left ≫ (N.hom ≫ p) := by
    rw [← Category.assoc, e.hom.w]
  rw [he]
  exact MorphismProperty.comp_mem _ _ _ inferInstance inferInstance

end

end OAI.RepresentationTheory.Theta.Geometric.Affine.QuotientFlatness
