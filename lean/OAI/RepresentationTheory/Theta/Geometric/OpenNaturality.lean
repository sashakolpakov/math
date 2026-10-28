import OAI.RepresentationTheory.Theta.Geometric.PointNaturality
import OAI.RepresentationTheory.Theta.Geometric.JetOpenNaturality

/-! # Open Naturality -/

namespace OAI.RepresentationTheory.Theta.Geometric.OpenNaturality

noncomputable section

section

/-! Geometric tangent naturality through a common affine open follows
from actual infinitesimal lifting and scalar extension of the derivative. -/

open scoped TensorProduct
open _root_.CategoryTheory _root_.AlgebraicGeometry

variable (F : Type) [Field F] [Algebra ℂ F]
  {Y : Over AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.complexBase} (A B C : CommAlgCat ℂ)
  [Algebra.Smooth ℂ A] [Algebra.Smooth ℂ B] [Algebra.Smooth ℂ C]
  (i : AlgebraicGeometry.Foundations.Scheme.AffineComplexPoints.affineSchemeOver ℂ A ⟶ Y) (j : AlgebraicGeometry.Foundations.Scheme.AffineComplexPoints.affineSchemeOver ℂ B ⟶ Y)
  [IsOpenImmersion j.left]
  (g : A →ₐ[ℂ] C) (h : B →ₐ[ℂ] C)
  [IsOpenImmersion (AlgebraicGeometry.Foundations.Scheme.AffineComplexPoints.affineAlgHomOverSpecEquiv ℂ A C g).left]
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

omit B [Algebra.Smooth ℂ B] i j h hfac f hf hfx in
theorem exists_geometricChartLift (v : F ⊗[ℂ] (Fin n → ℂ)) :
    ∃ u : F ⊗[ℂ] (Fin l → ℂ),
      (PointCharts.pointChartGeometricEquiv F k hk x hx u).val ≫ AlgebraicGeometry.Foundations.Scheme.AffineComplexPoints.affineAlgHomOverSpecEquiv ℂ A C g =
        (PointCharts.pointChartGeometricEquiv F e he (x.comp g) hex v).val := by
  have hp : ExtendedComplexPoints.extendedComplexPoint F (AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.affineSchemePointEquiv A (x.comp g)) =
      ExtendedComplexPoints.extendedComplexPoint F (AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.affineSchemePointEquiv C x) ≫ AlgebraicGeometry.Foundations.Scheme.AffineComplexPoints.affineAlgHomOverSpecEquiv ℂ A C g :=
    (congrArg (fun p : AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints (AlgebraicGeometry.Foundations.Scheme.AffineComplexPoints.affineSchemeOver ℂ A) => ExtendedComplexPoints.extendedComplexPoint F p)
      (AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.affineSchemePointEquiv_comap g x)).trans (Category.assoc _ _ _).symm
  let t : TangentSources.extendedSchemeTangentPoints ℂ F (AlgebraicGeometry.Foundations.Scheme.AffineComplexPoints.affineSchemeOver ℂ A)
      (ExtendedComplexPoints.extendedComplexPoint F (AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.affineSchemePointEquiv C x) ≫ AlgebraicGeometry.Foundations.Scheme.AffineComplexPoints.affineAlgHomOverSpecEquiv ℂ A C g) :=
    ⟨(PointCharts.pointChartGeometricEquiv F e he (x.comp g) hex v).val,
      (PointCharts.pointChartGeometricEquiv F e he (x.comp g) hex v).property.trans hp⟩
  let z := (TangentSources.extendedTangentNeighborhoodEquiv ℂ F _ _
    (AlgebraicGeometry.Foundations.Scheme.AffineComplexPoints.affineAlgHomOverSpecEquiv ℂ A C g) (ExtendedComplexPoints.extendedComplexPoint F (AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.affineSchemePointEquiv C x))).symm t
  obtain ⟨u, hu⟩ := (PointCharts.pointChartGeometricEquiv F k hk x hx).surjective z
  refine ⟨u, ?_⟩
  have hzu := congrArg (fun q : TangentSources.extendedSchemeTangentPoints ℂ F (AlgebraicGeometry.Foundations.Scheme.AffineComplexPoints.affineSchemeOver ℂ C)
    (ExtendedComplexPoints.extendedComplexPoint F (AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.affineSchemePointEquiv C x)) => q.val) hu
  have hz := congrArg (fun q : TangentSources.extendedSchemeTangentPoints ℂ F (AlgebraicGeometry.Foundations.Scheme.AffineComplexPoints.affineSchemeOver ℂ A)
    (ExtendedComplexPoints.extendedComplexPoint F (AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.affineSchemePointEquiv C x) ≫ AlgebraicGeometry.Foundations.Scheme.AffineComplexPoints.affineAlgHomOverSpecEquiv ℂ A C g) => q.val)
    ((TangentSources.extendedTangentNeighborhoodEquiv ℂ F _ _ (AlgebraicGeometry.Foundations.Scheme.AffineComplexPoints.affineAlgHomOverSpecEquiv ℂ A C g)
      (ExtendedComplexPoints.extendedComplexPoint F (AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.affineSchemePointEquiv C x))).apply_symm_apply t)
  exact (congrArg (fun q : LieFieldTests.extendedDualTest ℂ F ⟶ AlgebraicGeometry.Foundations.Scheme.AffineComplexPoints.affineSchemeOver ℂ C =>
    q ≫ AlgebraicGeometry.Foundations.Scheme.AffineComplexPoints.affineAlgHomOverSpecEquiv ℂ A C g) hzu).trans hz

include hfac he hf hk hx hex hfx

theorem pointChartGeometric_openFactorization (v : F ⊗[ℂ] (Fin n → ℂ)) :
    (PointCharts.pointChartGeometricEquiv F f hf (x.comp h) hfx
      ((fderiv ℂ (fun z => AlgebraicGeometry.ComplexPoints.Analytic.SmoothSchemeManifold.affineChartOnScheme B j f
        (AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.affinePointMap A i (e.symm z))) (e (x.comp g))).toLinearMap.baseChange F v)).val ≫ j =
      (PointCharts.pointChartGeometricEquiv F e he (x.comp g) hex v).val ≫ i := by
  obtain ⟨u, hu⟩ := exists_geometricChartLift F A C g e k he hk x hx hex v
  have hGu : (fderiv ℂ (fun z => e ((k.symm z).comp g)) (k x)).toLinearMap.baseChange F u = v := by
    apply (PointCharts.pointChartGeometricEquiv F e he (x.comp g) hex).injective
    apply Subtype.ext
    exact (PointNaturality.pointChartGeometric_naturality F g k e hk he x hx hex u).trans hu
  have hdu : (fderiv ℂ (fun z => f ((k.symm z).comp h)) (k x)).toLinearMap.baseChange F u =
      (fderiv ℂ (fun z => AlgebraicGeometry.ComplexPoints.Analytic.SmoothSchemeManifold.affineChartOnScheme B j f
        (AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.affinePointMap A i (e.symm z))) (e (x.comp g))).toLinearMap.baseChange F
        ((fderiv ℂ (fun z => e ((k.symm z).comp g)) (k x)).toLinearMap.baseChange F u) := by
    clear hu hGu
    induction u using TensorProduct.inductionOn with
    | add u w hu hw => simp only [map_add, hu, hw]
    | tmul c w =>
        simp only [LinearMap.baseChange_tmul]
        exact congrArg (fun z : Fin m → ℂ => c ⊗ₜ[ℂ] z)
          (JetOpenNaturality.regularChart_factorization_derivative A B C i j g h hfac e f k he hf hk x hx hex hfx w)
  rw [hGu] at hdu
  rw [← hdu, PointNaturality.pointChartGeometric_naturality F h k f hk hf x hx hfx u,
    Category.assoc, hfac, ← Category.assoc, hu]

end

/-! On an arbitrary affine chart overlap, extended tangent coordinates
commute with the actual scheme morphism. -/

open scoped TensorProduct
open _root_.CategoryTheory _root_.AlgebraicGeometry

variable (F : Type) [Field F] [Algebra ℂ F]
  {Y : Over AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.complexBase} (A B : CommAlgCat ℂ)
  [IsDomain A] [Algebra.Smooth ℂ A] [Algebra.Smooth ℂ B]
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

theorem pointChartGeometric_schemeMap (v : F ⊗[ℂ] (Fin n → ℂ)) :
    (PointCharts.pointChartGeometricEquiv F f hf y hy
      ((fderiv ℂ (fun z => AlgebraicGeometry.ComplexPoints.Analytic.SmoothSchemeManifold.affineChartOnScheme B j f
        (AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.affinePointMap A i (e.symm z))) (e x)).toLinearMap.baseChange F v)).val ≫ j =
      (PointCharts.pointChartGeometricEquiv F e he x hx v).val ≫ i := by
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
  have ht := pointChartGeometric_openFactorization F A B C i j g h hfac
    e f k he hf hk z hzk hex hfy v
  have hv := congrArg (fun w : AlgebraicGeometry.Foundations.Scheme.AffineComplexPoints.affineComplexPoints A =>
    (fderiv ℂ (fun t => AlgebraicGeometry.ComplexPoints.Analytic.SmoothSchemeManifold.affineChartOnScheme B j f
      (AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.affinePointMap A i (e.symm t))) (e w)).toLinearMap.baseChange F v) hxz
  have hleft := PointCharts.pointChartGeometricEquiv_congr F f hf (z.comp h) hfy y hy hyz _ _ hv
  have hright := PointCharts.pointChartGeometricEquiv_congr F e he (z.comp g) hex x hx hxz v v rfl
  exact (congrArg (fun t : LieFieldTests.extendedDualTest ℂ F ⟶ AlgebraicGeometry.Foundations.Scheme.AffineComplexPoints.affineSchemeOver ℂ B => t ≫ j) hleft).symm.trans
    (ht.trans (congrArg (fun t : LieFieldTests.extendedDualTest ℂ F ⟶ AlgebraicGeometry.Foundations.Scheme.AffineComplexPoints.affineSchemeOver ℂ A => t ≫ i) hright))

end

end OAI.RepresentationTheory.Theta.Geometric.OpenNaturality
