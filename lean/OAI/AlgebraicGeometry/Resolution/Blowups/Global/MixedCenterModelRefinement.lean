import OAI.AlgebraicGeometry.Resolution.Blowups.Global.AtlasFromAffineCover
import OAI.AlgebraicGeometry.Resolution.Blowups.Global.CanonicalBoundaryAtlas
import OAI.AlgebraicGeometry.Resolution.Blowups.BoundaryModel.Operations

/-! # Mixed Center Model Refinement -/

namespace OAI.AlgebraicGeometry.Resolution.Blowups.Global

noncomputable section

/-! Refine a native common-center atlas to affine opens with actual boundary coordinate models. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

theorem CanonicalBoundaryAtlas.Construction.GlobalMixedCenterAtlas.exists_model_refinement
    {X : Scheme} {f : X ⟶ Foundations.Scheme.ProjectiveSpace.complexBase} {I : X.IdealSheafData}
    {β : Type} {D : β → X.IdealSheafData} (A : CanonicalBoundaryAtlas.Construction.GlobalMixedCenterAtlas f I D) :
    ∃ B : CanonicalBoundaryAtlas.Construction.GlobalMixedCenterAtlas f I D, ∀ i,
      letI := Smooth.DifferentialIdealSheaf.Construction.affineComplexAlgebra f (B.opens i)
      Nonempty (Blowups.Etale.BoundaryModel.Construction.EtaleBoundaryModel ℂ Γ(X, B.opens i) β (B.equations i)) := by
  classical
  let : ∀ i, Algebra ℂ Γ(X, A.opens i) := fun i => Smooth.DifferentialIdealSheaf.Construction.affineComplexAlgebra f (A.opens i)
  let κ := (i : A.indices) × PrimeSpectrum Γ(X, A.opens i)
  let C (p : κ) := Classical.choice (A.boundary p.1 p.2)
  let j (p : κ) : Spec (C p).carrier ⟶ X :=
    Spec.map (CommRingCat.ofHom (C p).map.toRingHom) ≫ (A.opens p.1).2.fromSpec
  let : ∀ p, IsOpenImmersion (j p) := fun p => by
    let : IsOpenImmersion (A.opens p.1).2.fromSpec := (A.opens p.1).2.isOpenImmersion_fromSpec
    exact inferInstanceAs (IsOpenImmersion (_ ≫ _))
  have hcover (x : X) : ∃ p : κ, x ∈ Set.range (j p) := by
    obtain ⟨i, q, hq⟩ := MonomialBoundaryAtlas.Construction.exists_point_on_chosen_affine_spec A.opens A.cover x
    refine ⟨⟨i, q⟩, (C ⟨i, q⟩).point, ?_⟩
    change (A.opens i).2.fromSpec (PrimeSpectrum.comap (C ⟨i, q⟩).map.toRingHom (C ⟨i, q⟩).point) = x
    rw [(C ⟨i, q⟩).point_over]
    exact hq
  let Q : X.AffineOpenCover :=
    { I₀ := κ
      X := fun p => (C p).carrier
      f := j
      map_prop := fun _ => inferInstance
      idx := fun x => (hcover x).choose
      covers := fun x => (hcover x).choose_spec }
  let : ∀ p : Q.I₀, Algebra ℂ (Q.X p) := fun p => (C p).algebra
  have hg (p : κ) : j p ≫ f = ComplexAffineDifferentialIdeal.Construction.complexSpecStructure (C p).carrier := by
    dsimp only [j]
    rw [Category.assoc, ← Affine.ComplexNaturality.Construction.affineComplexScalars_spec f (A.opens p.1), ← Spec.map_comp]
    apply congrArg Spec.map
    ext c
    exact (C p).map.commutes c
  let K (p : κ) := (I.ideal (A.opens p.1)).map (C p).map.toRingHom
  let w (p : κ) (l : β) := (C p).map (A.equations p.1 l)
  have hI (p : κ) : I.comap (j p) = Affine.QuotientKernel.Construction.affineQuotientKernel (K p) :=
    Affine.IdealSheafIdentification.Construction.idealSheaf_comap_affineMap_eq_quotient_kernel I (A.opens p.1) (C p).map.toRingHom
  have hD (p : κ) (l : β) : (D l).comap (j p) = Affine.QuotientKernel.Construction.affineQuotientKernel (Ideal.span {w p l}) := by
    change (D l).comap (Spec.map (CommRingCat.ofHom (C p).map.toRingHom) ≫ (A.opens p.1).2.fromSpec) = _
    rw [Affine.IdealSheafIdentification.Construction.idealSheaf_comap_affineMap_eq_quotient_kernel, A.component, Ideal.map_span, Set.image_singleton]
  have hc (p : κ) : MixedBoundary.CenterCharts.Construction.HasMixedBoundaryCenterCharts ℂ (C p).carrier (K p) (w p) (A.divided p.1) := by
    apply (A.center p.1).etale_baseChange (C p).map
    exact (HasRingHomProperty.Spec_iff (P := @Etale)).mp
      (inferInstance : Etale (Spec.map (CommRingCat.ofHom (C p).map.toRingHom)))
  let B := CanonicalBoundaryAtlas.Construction.GlobalMixedCenterAtlas.ofAffineCover f I D Q hg K w (fun p => A.divided p.1)
    hI hD (fun p => (C p).model.hasEtaleBoundaryCharts) hc
  refine ⟨B, ?_⟩
  intro p
  change κ at p
  let : Algebra ℂ Γ(X, Affine.OpenBoundaryTransport.Construction.specOpenImage (C p).carrier (j p)) :=
    Smooth.DifferentialIdealSheaf.Construction.affineComplexAlgebra f (Affine.OpenBoundaryTransport.Construction.specOpenImage (C p).carrier (j p))
  let e := Affine.OpenBoundaryTransport.Construction.specOpenSectionAlgEquiv f (C p).carrier (j p) (hg p)
  exact ⟨(C p).model.baseChange e.symm.toAlgHom (RingHom.Etale.of_bijective e.symm.bijective)⟩

end

end OAI.AlgebraicGeometry.Resolution.Blowups.Global
