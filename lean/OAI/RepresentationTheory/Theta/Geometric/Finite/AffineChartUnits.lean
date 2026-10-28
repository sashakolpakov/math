import OAI.RepresentationTheory.Theta.Geometric.Finite.TensorUnits
import OAI.RepresentationTheory.Theta.Geometric.AffineChartSectionCoordinates

/-! # Affine Chart Units -/

namespace OAI.RepresentationTheory.Theta.Geometric.Finite.AffineChartUnits

noncomputable section

/-! A finite family of actual regular units on flat affine charts
descends to one finitely generated parameter subalgebra. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped TensorProduct

theorem exists_fg_subalgebra_finite_affine_chart_units
    {A R ι : Type} [CommRing A] [CommRing R] [Algebra A R] [Fintype ι]
    (B : ι → Type) [∀ i, CommRing (B i)] [∀ i, Algebra A (B i)] [∀ i, Module.Flat A (B i)]
    (XR : ι → Scheme) (XS : Subalgebra A R → ι → Scheme)
    (eR : ∀ i, XR i ≅ Spec (.of (B i ⊗[A] R)))
    (eS : ∀ S i, XS S i ≅ Spec (.of (B i ⊗[A] S)))
    (b : ∀ S i, XR i ⟶ XS S i)
    (hb : ∀ S i, (eR i).hom ≫
      Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.map (AlgHom.id A (B i)) S.val).toRingHom) =
        b S i ≫ (eS S i).hom)
    (u : ∀ i, Γ(XR i, ⊤)ˣ) :
    ∃ S : Subalgebra A R, S.FG ∧ ∃ v : ∀ i, Γ(XS S i, ⊤)ˣ,
      ∀ i, Units.map (b S i).appTop.hom.toMonoidHom (v i) = u i := by
  obtain ⟨S, hS, w, hw⟩ := TensorUnits.exists_fg_subalgebra_finite_right_tensor_units B
    (fun i => Units.map (AffineChartSectionCoordinates.affineChartSectionEquiv (eR i)).toMonoidHom (u i))
  refine ⟨S, hS, (fun i => Units.map (AffineChartSectionCoordinates.affineChartSectionEquiv (eS S i)).symm.toMonoidHom (w i)), ?_⟩
  intro i
  apply Units.ext
  apply (AffineChartSectionCoordinates.affineChartSectionEquiv (eR i)).injective
  change AffineChartSectionCoordinates.affineChartSectionEquiv (eR i)
      ((b S i).appTop ((AffineChartSectionCoordinates.affineChartSectionEquiv (eS S i)).symm (w i : B i ⊗[A] S))) =
    AffineChartSectionCoordinates.affineChartSectionEquiv (eR i) (u i : Γ(XR i, ⊤))
  rw [AffineChartSectionCoordinates.affineChartSectionEquiv_natural (eR i) (eS S i) (b S i) _ (hb S i), RingEquiv.apply_symm_apply]
  exact hw i

end

end OAI.RepresentationTheory.Theta.Geometric.Finite.AffineChartUnits
