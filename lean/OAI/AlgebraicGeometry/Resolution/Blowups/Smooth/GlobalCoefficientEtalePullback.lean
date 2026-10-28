import OAI.AlgebraicGeometry.Resolution.Blowups.GlobalCoefficient.AffineCharts
import OAI.AlgebraicGeometry.Resolution.Blowups.IdealSheaf.AffinePullback
import OAI.AlgebraicGeometry.Resolution.Blowups.Global.MonomialBoundaryAtlas

/-! # Global Coefficient Etale Pullback -/

namespace OAI.AlgebraicGeometry.Resolution.Blowups.Smooth.GlobalCoefficientEtalePullback.Construction

noncomputable section

section

/-! The native ordinary differential filtration commutes exactly with actual étale pullback. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

theorem smoothDifferentialIdealSheaf_comap_etale
    {X Y : Scheme} (f : X ⟶ Foundations.Scheme.ProjectiveSpace.complexBase) [Smooth f] (I : X.IdealSheafData) (n : ℕ)
    (g : Y ⟶ X) [Etale g] :
    (DifferentialIdealSheaf.Construction.smoothDifferentialIdealSheaf f I n).comap g =
      DifferentialIdealSheaf.Construction.smoothDifferentialIdealSheaf (g ≫ f) (I.comap g) n := by
  let : IsLocallyNoetherian Y := LocallyOfFiniteType.isLocallyNoetherian (g ≫ f)
  choose U V hsub hmem using IdealSheaf.ProductPullback.Construction.exists_affine_pair_at_point g
  have hcover : ⨆ y : Y, (V y).1 = ⊤ := by
    apply top_le_iff.mp
    intro y _
    exact TopologicalSpace.Opens.mem_iSup.mpr ⟨y, hmem y⟩
  apply IdealSheaf.EqualityGluing.Construction.idealSheaf_eq_of_openCover _ _ (Global.MonomialBoundaryAtlas.Construction.chosenAffineSpecCover V hcover).openCover
  intro y
  change Y at y
  let : Algebra ℂ Γ(X, U y) := DifferentialIdealSheaf.Construction.affineComplexAlgebra f (U y)
  let : Algebra ℂ Γ(Y, V y) := DifferentialIdealSheaf.Construction.affineComplexAlgebra (g ≫ f) (V y)
  let : Algebra.Smooth ℂ Γ(X, U y) := DifferentialIdealSheaf.Construction.affineComplexAlgebra_smooth f (U y)
  let φ : Γ(X, U y) →ₐ[ℂ] Γ(Y, V y) := {
    __ := (g.appLE (U y).1 (V y).1 (hsub y)).hom
    commutes' := fun c => RingHom.congr_fun (Affine.ComplexNaturality.Construction.affineComplexScalars_appLE f g (V y) (U y) (hsub y)) c }
  have hφ : φ.toRingHom.Etale := g.etale_appLE (U y).2 (V y).2 (hsub y)
  have he : ((DifferentialIdealSheaf.Construction.smoothDifferentialIdealSheaf f I n).comap g).ideal (V y) =
      (DifferentialIdealSheaf.Construction.smoothDifferentialIdealSheaf (g ≫ f) (I.comap g) n).ideal (V y) := by
    rw [IdealSheaf.AffinePullback.Construction.idealSheaf_comap_ideal_of_le _ g (U y) (V y) (hsub y)]
    change (Relative.DifferentialBlowup.Construction.iteratedRelativeDifferentialIdeal ℂ (I.ideal (U y)) n).map φ.toRingHom =
      Relative.DifferentialBlowup.Construction.iteratedRelativeDifferentialIdeal ℂ ((I.comap g).ideal (V y)) n
    rw [IdealSheaf.AffinePullback.Construction.idealSheaf_comap_ideal_of_le I g (U y) (V y) (hsub y)]
    exact DifferentialMap.Construction.smooth_iteratedRelativeDifferentialIdeal_map ℂ φ hφ (I.ideal (U y)) n
  change ((DifferentialIdealSheaf.Construction.smoothDifferentialIdealSheaf f I n).comap g).comap (V y).2.fromSpec =
    (DifferentialIdealSheaf.Construction.smoothDifferentialIdealSheaf (g ≫ f) (I.comap g) n).comap (V y).2.fromSpec
  rw [Affine.IdealSheafIdentification.Construction.idealSheaf_comap_fromSpec_eq_quotient_kernel, Affine.IdealSheafIdentification.Construction.idealSheaf_comap_fromSpec_eq_quotient_kernel, he]

theorem smoothDifferentialIdealSheaf_comap_etale_affine
    {X : Scheme} (f : X ⟶ Foundations.Scheme.ProjectiveSpace.complexBase) [Smooth f] (J : X.IdealSheafData) (n : ℕ)
    (R : CommRingCat) [Algebra ℂ R] (j : Spec R ⟶ X) [Etale j]
    (hj : j ≫ f = ComplexAffineDifferentialIdeal.Construction.complexSpecStructure R) (K : Ideal R) (hK : J.comap j = Affine.QuotientKernel.Construction.affineQuotientKernel K) :
    (DifferentialIdealSheaf.Construction.smoothDifferentialIdealSheaf f J n).comap j =
      Affine.QuotientKernel.Construction.affineQuotientKernel (Relative.DifferentialBlowup.Construction.iteratedRelativeDifferentialIdeal ℂ K n) := by
  have hs : Smooth (ComplexAffineDifferentialIdeal.Construction.complexSpecStructure R) := hj ▸ inferInstanceAs (Smooth (j ≫ f))
  let : Algebra.Smooth ℂ R := RingHom.smooth_algebraMap.mp
    ((HasRingHomProperty.Spec_iff (P := @Smooth) (φ := CommRingCat.ofHom (algebraMap ℂ R))).mp hs)
  rw [smoothDifferentialIdealSheaf_comap_etale, hK]
  exact (DifferentialUnitGluing.Construction.smoothDifferentialIdealSheaf_structure_congr (j ≫ f) _ hj _ n).trans
    (ComplexAffineDifferentialIdeal.Construction.smoothDifferentialIdealSheaf_affineQuotientKernel R K n)

end

/-! Exact étale base change and affine quotient formulas for native coefficient ideal sheaves. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

theorem smoothCoefficientIdealSheaf_comap_etale_square
    {X Y X' Y' : Scheme} (f : X ⟶ Foundations.Scheme.ProjectiveSpace.complexBase) [Smooth f]
    (J : X.IdealSheafData) (b : ℕ) (q : Y ⟶ X) (q' : Y' ⟶ X')
    (j : X' ⟶ X) [Etale j] (l : Y' ⟶ Y) (hcomm : l ≫ q = q' ≫ j) :
    (GlobalCoefficient.CoefficientSheaf.Construction.smoothCoefficientIdealSheaf f J b q).comap l =
      GlobalCoefficient.CoefficientSheaf.Construction.smoothCoefficientIdealSheaf (j ≫ f) (J.comap j) b q' := by
  rw [GlobalCoefficient.CoefficientSheaf.Construction.smoothCoefficientIdealSheaf_comap]
  simp only [GlobalCoefficient.CoefficientSheaf.Construction.smoothCoefficientIdealSheaf, hcomm, Scheme.IdealSheafData.comap_comp,
    smoothDifferentialIdealSheaf_comap_etale]

theorem smoothCoefficientIdealSheaf_comap_etale_quotient_chart
    {X Y : Scheme} (f : X ⟶ Foundations.Scheme.ProjectiveSpace.complexBase) [Smooth f] (J : X.IdealSheafData) (b : ℕ) (q : Y ⟶ X)
    (R : CommRingCat) [Algebra ℂ R] (j : Spec R ⟶ X) [Etale j]
    (hj : j ≫ f = ComplexAffineDifferentialIdeal.Construction.complexSpecStructure R) (K L : Ideal R) (hK : J.comap j = Affine.QuotientKernel.Construction.affineQuotientKernel K)
    (l : Spec (.of (R ⧸ L)) ⟶ Y)
    (hcomm : l ≫ q = Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk L)) ≫ j) :
    (GlobalCoefficient.CoefficientSheaf.Construction.smoothCoefficientIdealSheaf f J b q).comap l =
      Affine.QuotientKernel.Construction.affineQuotientKernel (WeightedCoefficientIdeal.Construction.weightedCoefficientIdeal b
        (fun r => (Relative.DifferentialBlowup.Construction.iteratedRelativeDifferentialIdeal ℂ K r.val).map (Ideal.Quotient.mk L))) := by
  rw [GlobalCoefficient.CoefficientSheaf.Construction.smoothCoefficientIdealSheaf_comap]
  simp only [GlobalCoefficient.CoefficientSheaf.Construction.smoothCoefficientIdealSheaf, hcomm, Scheme.IdealSheafData.comap_comp]
  simp_rw [smoothDifferentialIdealSheaf_comap_etale_affine f J _ R j hj K hK,
    Affine.IdealChartDescent.Construction.affineQuotientKernel_comap_hom]
  simp only [WeightedCoefficientIdeal.Construction.weightedCoefficientIdeal, Affine.KernelSums.Construction.affineQuotientKernel_iSup, Affine.QuotientKernel.Construction.affineQuotientKernel_pow]

theorem smoothCoefficientIdealSheaf_comap_etale_hypersurface_chart
    {X Y : Scheme} (f : X ⟶ Foundations.Scheme.ProjectiveSpace.complexBase) [Smooth f] (J : X.IdealSheafData) (b : ℕ) (q : Y ⟶ X)
    (R : CommRingCat) [Algebra ℂ R] (j : Spec R ⟶ X) [Etale j]
    (hj : j ≫ f = ComplexAffineDifferentialIdeal.Construction.complexSpecStructure R) (K : Ideal R) (z : R) (hK : J.comap j = Affine.QuotientKernel.Construction.affineQuotientKernel K)
    (l : Spec (.of (R ⧸ Ideal.span {z})) ⟶ Y)
    (hcomm : l ≫ q = Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (Ideal.span {z}))) ≫ j) :
    (GlobalCoefficient.CoefficientSheaf.Construction.smoothCoefficientIdealSheaf f J b q).comap l = Affine.QuotientKernel.Construction.affineQuotientKernel (Relative.CoefficientIdeal.Construction.relativeCoefficientIdeal ℂ z K b) :=
  smoothCoefficientIdealSheaf_comap_etale_quotient_chart f J b q R j hj K (Ideal.span {z}) hK l hcomm

end

end OAI.AlgebraicGeometry.Resolution.Blowups.Smooth.GlobalCoefficientEtalePullback.Construction
