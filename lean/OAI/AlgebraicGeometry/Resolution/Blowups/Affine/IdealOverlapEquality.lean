import OAI.AlgebraicGeometry.Resolution.Blowups.GlobalCoefficient.ComponentGluing

/-! # Ideal Overlap Equality -/

namespace OAI.AlgebraicGeometry.Resolution.Blowups.Affine.IdealOverlapEquality.Construction

noncomputable section

/-! Actual common affine diagrams identify the pulled-back ideals and labelled boundary equations. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

theorem complexSpecStructure_specMap_algHom
    (R S : CommRingCat) [Algebra ℂ R] [Algebra ℂ S] (φ : R →ₐ[ℂ] S) :
    Spec.map (CommRingCat.ofHom φ.toRingHom) ≫ ComplexAffineDifferentialIdeal.Construction.complexSpecStructure R = ComplexAffineDifferentialIdeal.Construction.complexSpecStructure S := by
  change Spec.map (CommRingCat.ofHom φ.toRingHom) ≫
    Spec.map (CommRingCat.ofHom (algebraMap ℂ R)) = Spec.map (CommRingCat.ofHom (algebraMap ℂ S))
  rw [← Spec.map_comp]
  apply congrArg Spec.map
  ext c
  exact φ.commutes c

theorem affine_ideal_maps_eq_of_common_diagram
    {X : Scheme.{0}} (J : X.IdealSheafData) (R S T : CommRingCat)
    (j : Spec R ⟶ X) (l : Spec S ⟶ X) (φ : R →+* T) (ψ : S →+* T)
    (hcomm : Spec.map (CommRingCat.ofHom φ) ≫ j = Spec.map (CommRingCat.ofHom ψ) ≫ l)
    (I : Ideal R) (K : Ideal S) (hI : J.comap j = QuotientKernel.Construction.affineQuotientKernel I)
    (hK : J.comap l = QuotientKernel.Construction.affineQuotientKernel K) : I.map φ = K.map ψ := by
  apply (GlobalCoefficient.ComponentGluing.Construction.affineQuotientKernel_eq_iff _ _).mp
  rw [← IdealChartDescent.Construction.affineQuotientKernel_comap_hom, ← IdealChartDescent.Construction.affineQuotientKernel_comap_hom, ← hI, ← hK,
    ← Scheme.IdealSheafData.comap_comp, ← Scheme.IdealSheafData.comap_comp, hcomm]

theorem affine_boundary_spans_eq_of_common_diagram
    {X : Scheme.{0}} {β : Type} (D : β → X.IdealSheafData) (R S T : CommRingCat)
    (j : Spec R ⟶ X) (l : Spec S ⟶ X) (φ : R →+* T) (ψ : S →+* T)
    (hcomm : Spec.map (CommRingCat.ofHom φ) ≫ j = Spec.map (CommRingCat.ofHom ψ) ≫ l)
    (w : β → R) (v : β → S)
    (hw : ∀ i, (D i).comap j = QuotientKernel.Construction.affineQuotientKernel (Ideal.span {w i}))
    (hv : ∀ i, (D i).comap l = QuotientKernel.Construction.affineQuotientKernel (Ideal.span {v i})) (i : β) :
    Ideal.span {φ (w i)} = Ideal.span {ψ (v i)} := by
  have he := affine_ideal_maps_eq_of_common_diagram (D i) R S T j l φ ψ hcomm
    (Ideal.span {w i}) (Ideal.span {v i}) (hw i) (hv i)
  simpa only [Ideal.map_span, Set.image_singleton] using he

end

end OAI.AlgebraicGeometry.Resolution.Blowups.Affine.IdealOverlapEquality.Construction
