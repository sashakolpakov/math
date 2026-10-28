import OAI.RepresentationTheory.Theta.Geometric.ChartJets
import OAI.AlgebraicGeometry.ComplexPoints.Analytic.IntrinsicSmoothSchemeMaps

/-! # Jet Open Naturality -/

namespace OAI.RepresentationTheory.Theta.Geometric.JetOpenNaturality

noncomputable section

section

/-! The derivative in scheme charts respects an actual affine factorization
through a common neighborhood. -/

open scoped ContDiff _root_.Topology
open _root_.CategoryTheory _root_.AlgebraicGeometry OAI.AlgebraicGeometry.ComplexPoints.Analytic.IntrinsicSmoothSchemeMaps

variable {Y : Over AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.complexBase} (A B C : CommAlgCat ℂ)
  (i : AlgebraicGeometry.Foundations.Scheme.AffineComplexPoints.affineSchemeOver ℂ A ⟶ Y) (j : AlgebraicGeometry.Foundations.Scheme.AffineComplexPoints.affineSchemeOver ℂ B ⟶ Y)
  [IsOpenImmersion j.left]
  (g : A →ₐ[ℂ] C) (h : B →ₐ[ℂ] C)
  (hfac : AlgebraicGeometry.Foundations.Scheme.AffineComplexPoints.affineAlgHomOverSpecEquiv ℂ B C h ≫ j =
    AlgebraicGeometry.Foundations.Scheme.AffineComplexPoints.affineAlgHomOverSpecEquiv ℂ A C g ≫ i)
  {n m l : ℕ}
  (e : OpenPartialHomeomorph (AlgebraicGeometry.Foundations.Scheme.AffineComplexPoints.affineComplexPoints A) (Fin n → ℂ))
  (f : OpenPartialHomeomorph (AlgebraicGeometry.Foundations.Scheme.AffineComplexPoints.affineComplexPoints B) (Fin m → ℂ))
  (k : OpenPartialHomeomorph (AlgebraicGeometry.Foundations.Scheme.AffineComplexPoints.affineComplexPoints C) (Fin l → ℂ))
  (he : e ∈ AlgebraicGeometry.ComplexPoints.Analytic.SmoothSchemeManifold.affineRegularAtlas A n) (hf : f ∈ AlgebraicGeometry.ComplexPoints.Analytic.SmoothSchemeManifold.affineRegularAtlas B m)
  (hk : k ∈ AlgebraicGeometry.ComplexPoints.Analytic.SmoothSchemeManifold.affineRegularAtlas C l)
  (x : AlgebraicGeometry.Foundations.Scheme.AffineComplexPoints.affineComplexPoints C) (hx : x ∈ k.source)
  (hex : x.comp g ∈ e.source) (hfx : x.comp h ∈ f.source)

include hfac

omit [IsOpenImmersion j.left] in
theorem affineFactorization_point (z : AlgebraicGeometry.Foundations.Scheme.AffineComplexPoints.affineComplexPoints C) :
    AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.affinePointMap B j (z.comp h) =
      AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.affinePointMap A i (z.comp g) := by
  exact (AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.affinePointMap_comap B C h j z).symm.trans
    ((congrArg (fun q : AlgebraicGeometry.Foundations.Scheme.AffineComplexPoints.affineSchemeOver ℂ C ⟶ Y =>
      AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.affinePointMap C q z) hfac).trans
        (AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.affinePointMap_comap A C g i z))

include he hf hk hx hex hfx

theorem regularChart_factorization_derivative (v : Fin l → ℂ) :
    fderiv ℂ (fun z => f ((k.symm z).comp h)) (k x) v =
      fderiv ℂ (fun z => AlgebraicGeometry.ComplexPoints.Analytic.SmoothSchemeManifold.affineChartOnScheme B j f
        (AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.affinePointMap A i (e.symm z))) (e (x.comp g))
        (fderiv ℂ (fun z => e ((k.symm z).comp g)) (k x) v) := by
  let F := fun z => AlgebraicGeometry.ComplexPoints.Analytic.SmoothSchemeManifold.affineChartOnScheme B j f
    (AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.affinePointMap A i (e.symm z))
  let G := fun z => e ((k.symm z).comp g)
  let H := fun z => f ((k.symm z).comp h)
  have hG : DifferentiableAt ℂ G (k x) :=
    (AlgebraicGeometry.ComplexPoints.Analytic.SmoothClosedImmersion.contDiffAt_affineChartComap g k e hk he x hx hex).differentiableAt (by simp)
  have hGx : G (k x) = e (x.comp g) := by dsimp [G]; rw [k.left_inv hx]
  have hD : IsOpen (e.target ∩ {z | AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.affinePointMap A i (e.symm z) ∈
      (AlgebraicGeometry.ComplexPoints.Analytic.SmoothSchemeManifold.affineChartOnScheme B j f).source}) := e.isOpen_inter_preimage_symm
    ((AlgebraicGeometry.ComplexPoints.Analytic.SmoothSchemeManifold.affineChartOnScheme B j f).open_source.preimage
      (AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.continuous_affinePointMap A i))
  have hmem : e (x.comp g) ∈ e.target ∩
      {z | AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.affinePointMap A i (e.symm z) ∈
        (AlgebraicGeometry.ComplexPoints.Analytic.SmoothSchemeManifold.affineChartOnScheme B j f).source} := by
    refine ⟨e.map_source hex, ?_⟩
    change AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.affinePointMap A i (e.symm (e (x.comp g))) ∈
      AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.affinePointMap B j '' f.source
    rw [e.left_inv hex]
    exact ⟨x.comp h, hfx, affineFactorization_point A B C i j g h hfac x⟩
  have hF : DifferentiableAt ℂ F (G (k x)) := by
    rw [hGx]
    exact ((AlgebraicGeometry.ComplexPoints.Analytic.IntrinsicSmoothSchemeMaps.contDiffOn_affineMap_regularCharts A B i j e f he hf).contDiffAt
      (hD.mem_nhds hmem)).differentiableAt (by simp)
  have heq : H =ᶠ[nhds (k x)] F ∘ G := by
    filter_upwards [AlgebraicGeometry.ComplexPoints.Analytic.SmoothClosedImmersion.affineChartComap_neighborhood g k e x hx hex] with z hz
    dsimp [F, G, H]
    rw [e.left_inv hz.2, ← affineFactorization_point A B C i j g h hfac,
      AlgebraicGeometry.ComplexPoints.Analytic.SmoothSchemeManifold.affineChartOnScheme_apply]
  have hd := heq.fderiv_eq.trans (fderiv_comp (k x) hF hG)
  rw [hGx] at hd
  exact congrArg (fun d : (Fin l → ℂ) →L[ℂ] (Fin m → ℂ) => d v) hd

end

section

/-! Tangent lifting along an actual affine open immersion turns the local
factorization calculation into naturality for every source tangent vector. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry OAI.AlgebraicGeometry.ComplexPoints.Analytic.IntrinsicSmoothSchemeMaps

variable {Y : Over AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.complexBase} (A B C : CommAlgCat ℂ)
  (i : AlgebraicGeometry.Foundations.Scheme.AffineComplexPoints.affineSchemeOver ℂ A ⟶ Y) (j : AlgebraicGeometry.Foundations.Scheme.AffineComplexPoints.affineSchemeOver ℂ B ⟶ Y)
  [IsOpenImmersion j.left]
  (g : A →ₐ[ℂ] C) (h : B →ₐ[ℂ] C)
  [IsOpenImmersion (AlgebraicGeometry.Foundations.Scheme.AffineComplexPoints.affineAlgHomOverSpecEquiv ℂ A C g).left]
  [Algebra.Smooth ℂ C]
  (hfac : AlgebraicGeometry.Foundations.Scheme.AffineComplexPoints.affineAlgHomOverSpecEquiv ℂ B C h ≫ j =
    AlgebraicGeometry.Foundations.Scheme.AffineComplexPoints.affineAlgHomOverSpecEquiv ℂ A C g ≫ i)
  {n m l : ℕ}
  (e : OpenPartialHomeomorph (AlgebraicGeometry.Foundations.Scheme.AffineComplexPoints.affineComplexPoints A) (Fin n → ℂ))
  (f : OpenPartialHomeomorph (AlgebraicGeometry.Foundations.Scheme.AffineComplexPoints.affineComplexPoints B) (Fin m → ℂ))
  (k : OpenPartialHomeomorph (AlgebraicGeometry.Foundations.Scheme.AffineComplexPoints.affineComplexPoints C) (Fin l → ℂ))
  (he : e ∈ AlgebraicGeometry.ComplexPoints.Analytic.SmoothSchemeManifold.affineRegularAtlas A n) (hf : f ∈ AlgebraicGeometry.ComplexPoints.Analytic.SmoothSchemeManifold.affineRegularAtlas B m)
  (hk : k ∈ AlgebraicGeometry.ComplexPoints.Analytic.SmoothSchemeManifold.affineRegularAtlas C l)
  (x : AlgebraicGeometry.Foundations.Scheme.AffineComplexPoints.affineComplexPoints C) (hx : x ∈ k.source)
  (hex : x.comp g ∈ e.source) (hfx : x.comp h ∈ f.source)

omit i j h hfac f hf hfx in
theorem exists_chartJet_lift (v : Fin n → ℂ) :
    ∃ u : Fin l → ℂ,
      ChartJets.regularChartSpecJet k hk x hx u ≫ AlgebraicGeometry.Foundations.Scheme.AffineComplexPoints.affineAlgHomOverSpecEquiv ℂ A C g =
        ChartJets.regularChartSpecJet e he (x.comp g) hex v := by
  let t : SchemeTangents.schemeTangentPoints (AlgebraicGeometry.Foundations.Scheme.AffineComplexPoints.affineSchemeOver ℂ A)
      (AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.affineSchemePointEquiv C x ≫ AlgebraicGeometry.Foundations.Scheme.AffineComplexPoints.affineAlgHomOverSpecEquiv ℂ A C g) :=
    ⟨ChartJets.regularChartSpecJet e he (x.comp g) hex v, by
      rw [ChartJets.regularChartSpecJet_origin]
      exact AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.affineSchemePointEquiv_comap g x⟩
  let z := (SchemeTangents.schemeTangentNeighborhoodEquiv _ _
    (AlgebraicGeometry.Foundations.Scheme.AffineComplexPoints.affineAlgHomOverSpecEquiv ℂ A C g) (AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.affineSchemePointEquiv C x)).symm t
  obtain ⟨u, hu⟩ := (ChartJets.regularChartSpecJetEquiv k hk x hx).surjective z
  refine ⟨u, ?_⟩
  have hzu := congrArg (fun q : SchemeTangents.schemeTangentPoints (AlgebraicGeometry.Foundations.Scheme.AffineComplexPoints.affineSchemeOver ℂ C)
    (AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.affineSchemePointEquiv C x) => q.val) hu
  have hz := congrArg (fun q : SchemeTangents.schemeTangentPoints (AlgebraicGeometry.Foundations.Scheme.AffineComplexPoints.affineSchemeOver ℂ A)
    (AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.affineSchemePointEquiv C x ≫ AlgebraicGeometry.Foundations.Scheme.AffineComplexPoints.affineAlgHomOverSpecEquiv ℂ A C g) => q.val)
    ((SchemeTangents.schemeTangentNeighborhoodEquiv _ _
      (AlgebraicGeometry.Foundations.Scheme.AffineComplexPoints.affineAlgHomOverSpecEquiv ℂ A C g) (AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.affineSchemePointEquiv C x)).apply_symm_apply t)
  exact (congrArg (fun q : AlgebraicGeometry.AbelianModuli.ReferenceFamily.LieRanks.dualNumberTest ℂ ⟶ AlgebraicGeometry.Foundations.Scheme.AffineComplexPoints.affineSchemeOver ℂ C =>
    q ≫ AlgebraicGeometry.Foundations.Scheme.AffineComplexPoints.affineAlgHomOverSpecEquiv ℂ A C g) hzu).trans hz

include hfac he hf hk hx hex hfx

theorem regularChartSpecJet_openFactorization (v : Fin n → ℂ) :
    ChartJets.regularChartSpecJet f hf (x.comp h) hfx
      (fderiv ℂ (fun z => AlgebraicGeometry.ComplexPoints.Analytic.SmoothSchemeManifold.affineChartOnScheme B j f
        (AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.affinePointMap A i (e.symm z))) (e (x.comp g)) v) ≫ j =
      ChartJets.regularChartSpecJet e he (x.comp g) hex v ≫ i := by
  obtain ⟨u, hu⟩ := exists_chartJet_lift A C g e k he hk x hx hex v
  have hGu : fderiv ℂ (fun z => e ((k.symm z).comp g)) (k x) u = v :=
    ChartJets.regularChartSpecJet_injective e he (x.comp g) hex
      ((ChartJets.regularChartSpecJet_naturality k hk x hx g e he hex u).trans hu)
  have hdu := regularChart_factorization_derivative A B C i j g h hfac
    e f k he hf hk x hx hex hfx u
  rw [hGu] at hdu
  rw [← hdu, ChartJets.regularChartSpecJet_naturality k hk x hx h f hf hfx u, Category.assoc, hfac,
    ← Category.assoc, hu]

end

/-! Native affine charts commute with every actual scheme morphism. The
common affine factorization is supplied by its genuine open target chart. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry OAI.AlgebraicGeometry.ComplexPoints.Analytic.IntrinsicSmoothSchemeMaps

variable {Y : Over AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.complexBase} (A B : CommAlgCat ℂ)
  [IsDomain A] [Algebra.Smooth ℂ A]
  (i : AlgebraicGeometry.Foundations.Scheme.AffineComplexPoints.affineSchemeOver ℂ A ⟶ Y) (j : AlgebraicGeometry.Foundations.Scheme.AffineComplexPoints.affineSchemeOver ℂ B ⟶ Y)
  [IsOpenImmersion j.left] {n m : ℕ}
  (e : OpenPartialHomeomorph (AlgebraicGeometry.Foundations.Scheme.AffineComplexPoints.affineComplexPoints A) (Fin n → ℂ))
  (f : OpenPartialHomeomorph (AlgebraicGeometry.Foundations.Scheme.AffineComplexPoints.affineComplexPoints B) (Fin m → ℂ))
  (he : e ∈ AlgebraicGeometry.ComplexPoints.Analytic.SmoothSchemeManifold.affineRegularAtlas A n) (hf : f ∈ AlgebraicGeometry.ComplexPoints.Analytic.SmoothSchemeManifold.affineRegularAtlas B m)
  (x : AlgebraicGeometry.Foundations.Scheme.AffineComplexPoints.affineComplexPoints A) (hx : x ∈ e.source)
  (y : AlgebraicGeometry.Foundations.Scheme.AffineComplexPoints.affineComplexPoints B) (hy : y ∈ f.source)
  (hxy : AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.affinePointMap B j y =
    AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.affinePointMap A i x)

include he hf hx hy hxy

theorem regularChartSpecJet_schemeMap (v : Fin n → ℂ) :
    ChartJets.regularChartSpecJet f hf y hy
      (fderiv ℂ (fun z => AlgebraicGeometry.ComplexPoints.Analytic.SmoothSchemeManifold.affineChartOnScheme B j f
        (AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.affinePointMap A i (e.symm z))) (e x) v) ≫ j =
      ChartJets.regularChartSpecJet e he x hx v ≫ i := by
  obtain ⟨a, ha, h, hfac, hpoint⟩ :=
    AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.exists_affineLocalizationTransition A B i j x ⟨y, hxy⟩
  let C := CommAlgCat.of ℂ (Localization.Away a)
  let g : A →ₐ[ℂ] C := Algebra.algHom ℂ A (Localization.Away a)
  let z : AlgebraicGeometry.Foundations.Scheme.AffineComplexPoints.affineComplexPoints C := AlgebraicGeometry.Foundations.Scheme.LocalizationComplexPoints.Algebraic.localizePoint x a ha
  have hxz : z.comp g = x := AlgebraicGeometry.Foundations.Scheme.LocalizationComplexPoints.Algebraic.localizePoint_comp x a ha
  have hyz : z.comp h = y :=
    (AlgebraicGeometry.ComplexPoints.Analytic.SmoothSchemeManifold.isOpenEmbedding_affinePointMap B j).injective ((hpoint ⟨x, ha⟩).trans hxy.symm)
  have ha0 : a ≠ 0 := by intro h; apply ha; rw [h, map_zero]
  let : IsDomain C := Localization.Away.isDomain ha0
  let : Algebra.Smooth A C := Algebra.Smooth.of_isLocalization_Away a
  let : Algebra.Smooth ℂ C := Algebra.Smooth.comp ℂ A C
  let : IsOpenImmersion (AlgebraicGeometry.Foundations.Scheme.AffineComplexPoints.affineAlgHomOverSpecEquiv ℂ A C g).left := by
    change IsOpenImmersion (Spec.map (CommRingCat.ofHom (algebraMap A (Localization.Away a))))
    infer_instance
  obtain ⟨k, hk, hzk⟩ := AlgebraicGeometry.ComplexPoints.Analytic.SmoothSchemeManifold.exists_smoothDomain_affineRegularChart z
  have hex : z.comp g ∈ e.source := hxz.symm ▸ hx
  have hfy : z.comp h ∈ f.source := hyz.symm ▸ hy
  have ht := regularChartSpecJet_openFactorization A B C i j g h hfac
    e f k he hf hk z hzk hex hfy v
  simpa only [hxz, hyz] using ht

end

end OAI.RepresentationTheory.Theta.Geometric.JetOpenNaturality
