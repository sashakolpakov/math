import OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.ReferenceAlbanese
import OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.Intrinsic.ProjectivePullback

/-! # Intrinsic Hecke -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.IntrinsicHecke.Intrinsic

noncomputable section

section

/-! Actual reference projections reconstruct native Betti H¹. This follows
from the geometric component decomposition and the Albanese Betti isomorphism. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj

theorem reference_projection_reconstruction
    {S : Scheme} {T : Over S} {r : ℕ} (C : PELModuli.IntegralModel.Components.ComponentAlbaneseData T r)
    (c : Foundations.Scheme.ProjectiveSpace.complexBase ⟶ S) (eT : (∐ C.S) ≅ T)
    (ha : Function.Injective (PELModuli.IntegralModel.Product.bettiPullbackQ (C.totalComplexMap c eT) 1))
    (B : Fin r → ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety)
    (b : ∀ j, C.complexSurface c j ⟶ (B j).toOver)
    (ψ : ∀ j, (C.complexAbelian c j).X ⟶ (B j).toOver)
    (hb : ∀ j, C.complexMap c j ≫ ψ j = b j)
    (e : ∀ j, (B j).variety.rationalCohomology 1 ≃ₗ[ℚ]
      PELModuli.IntegralModel.Product.bettiQ (C.complexSurface c j) 1)
    (he : ∀ j, (e j).toLinearMap = PELModuli.IntegralModel.Product.bettiPullbackQ (b j) 1)
    (x : PELModuli.IntegralModel.Product.bettiQ ((Over.pullback c).obj C.product) 1) :
    ∑ j, PELModuli.IntegralModel.Product.bettiPullbackQ
      ((Over.pullback c).map (Pi.π (fun k => (C.A k).X) j) ≫ ψ j) 1
      ((e j).symm (C.complexComponentBettiEquiv c eT 1
        (PELModuli.IntegralModel.Product.bettiPullbackQ (C.totalComplexMap c eT) 1 x) j)) = x := by
  let R := C.complexComponentBettiEquiv c eT 1
  let a := PELModuli.IntegralModel.Product.bettiPullbackQ (C.totalComplexMap c eT) 1
  let y := fun j => PELModuli.IntegralModel.Product.bettiPullbackQ (ψ j) 1 ((e j).symm (R (a x) j))
  have hsum : C.complexProjectionSum c 1 y =
      ∑ j, PELModuli.IntegralModel.Product.bettiPullbackQ
        ((Over.pullback c).map (Pi.π (fun k => (C.A k).X) j) ≫ ψ j) 1
          ((e j).symm (R (a x) j)) := by
    simp only [PELModuli.IntegralModel.Components.ComponentAlbaneseData.complexProjectionSum,
      LinearMap.sum_apply, LinearMap.comp_apply, LinearMap.proj_apply,
      PELModuli.IntegralModel.Product.bettiPullbackQ_comp]
    rfl
  rw [← hsum]
  apply ha
  apply R.injective
  have h := LinearMap.congr_fun (C.complexTotalMap_projectionSum c eT 1 (by decide)) y
  change R (a (C.complexProjectionSum c 1 y)) = _ at h
  refine h.trans ?_
  funext j
  change PELModuli.IntegralModel.Product.bettiPullbackQ (C.complexMap c j) 1
    (PELModuli.IntegralModel.Product.bettiPullbackQ (ψ j) 1 ((e j).symm (R (a x) j))) = R (a x) j
  have hcomp := LinearMap.congr_fun (PELModuli.IntegralModel.Product.bettiPullbackQ_comp
    (C.complexMap c j) (ψ j) 1) ((e j).symm (R (a x) j))
  rw [hb j, ← he j] at hcomp
  exact hcomp.symm.trans ((e j).apply_symm_apply _)

variable {E K : Type} [Field E] [NumberField E] [NumberField.IsCMField E]
  [Field K] [NumberField K] {s q : ℕ} [Fact q.Prime]
  {Index Ga MpR MpF MpA : Type} [Fintype Index] [DecidableEq Index]
  [Group Ga] [TopologicalSpace Ga] [Group MpR] [Group MpF] [Group MpA]
  (D : RepresentationTheory.Theta.Geometric.Data.ActiveHeckeThetaData E K s q Index Ga MpR MpF MpA)

def nativeReferenceProjection (B : Fin D.pel.componentCount → ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety)
    (ψ : ∀ j, (D.pel.components.complexAbelian D.pel.complexPoint j).X ⟶ (B j).toOver)
    (j : Fin D.pel.componentCount) : D.pel.complexAlbanese.X ⟶ (B j).toOver :=
  (Intrinsic.Base.singleBaseAlbaneseIso D).inv ≫
    (Over.pullback D.pel.complexPoint).map (Pi.π (fun k => (D.pel.components.A k).X) j) ≫ ψ j

def nativeReferenceCoordinates (hg : D.pel.HasIntegralModelGeometry) :
    D.pel.H1 →ₗ[ℚ] (∀ j, (ReferenceAlbanese.Intrinsic.singleBaseComponentVariety D hg j).rationalCohomology 1) := by
  let : IsIso D.pel.componentAssembly := hg.decomposition
  exact (D.pel.components.complexComponentBettiEquiv D.pel.complexPoint
    (asIso D.pel.componentAssembly) 1).toLinearMap.comp
      (Intrinsic.Base.nativeAlbaneseBettiEquiv D hg).toLinearMap

theorem nativeReferenceCoordinates_isHodgeMap
    (hHodgeDecomposition : Mem.HodgeDecompositionInput) (hg : D.pel.HasIntegralModelGeometry)
    (j : Fin D.pel.componentCount) :
    ComplexMultiplication.WeightOne.CM.IsHodgeMap (Intrinsic.Base.nativeH1 D hHodgeDecomposition hg)
      (Mem.canonicalH1 hHodgeDecomposition (ReferenceAlbanese.Intrinsic.singleBaseComponentVariety D hg j).presentation)
      ((LinearMap.proj j).comp (nativeReferenceCoordinates D hg)) := by
  let : IsIso D.pel.componentAssembly := hg.decomposition
  let f : (ReferenceAlbanese.Intrinsic.singleBaseComponentVariety D hg j).toOver ⟶
      (Intrinsic.Base.singleBaseSpacePresentation D hg).toOver :=
    (Over.pullback D.pel.complexPoint).map
      (Sigma.ι D.pel.components.S j ≫ (asIso D.pel.componentAssembly).hom)
  have h := (Naturality.canonicalH1_pullback hHodgeDecomposition
    (ReferenceAlbanese.Intrinsic.singleBaseComponentVariety D hg j).presentation (Intrinsic.Base.singleBaseSpacePresentation D hg) f).comp
      (Intrinsic.Base.nativeAlbaneseBettiEquiv_isHodgeMap D hHodgeDecomposition hg)
  have he : (PELModuli.IntegralModel.Product.bettiPullbackQ f 1).comp (Intrinsic.Base.nativeAlbaneseBettiEquiv D hg).toLinearMap =
      (LinearMap.proj j).comp (nativeReferenceCoordinates D hg) := by
    ext x
    exact (D.pel.components.complexComponentBettiEquiv_apply D.pel.complexPoint
      (asIso D.pel.componentAssembly) 1 ((Intrinsic.Base.nativeAlbaneseBettiEquiv D hg) x) j).symm
  exact he ▸ h

theorem native_reference_reconstruction (hg : D.pel.HasIntegralModelGeometry)
    (B : Fin D.pel.componentCount → ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety)
    (b : ∀ j, (ReferenceAlbanese.Intrinsic.singleBaseComponentVariety D hg j).toOver ⟶ (B j).toOver)
    (ψ : ∀ j, (D.pel.components.complexAbelian D.pel.complexPoint j).X ⟶ (B j).toOver)
    (hb : ∀ j, D.pel.components.complexMap D.pel.complexPoint j ≫ ψ j = b j)
    (e : ∀ j, (B j).variety.rationalCohomology 1 ≃ₗ[ℚ]
      (ReferenceAlbanese.Intrinsic.singleBaseComponentVariety D hg j).rationalCohomology 1)
    (he : ∀ j, (e j).toLinearMap = PELModuli.IntegralModel.Product.bettiPullbackQ (b j) 1) (x : D.pel.H1) :
    ∑ j, PELModuli.IntegralModel.Product.bettiPullbackQ (nativeReferenceProjection D B ψ j) 1
      ((e j).symm (nativeReferenceCoordinates D hg x j)) = x := by
  let : IsIso D.pel.componentAssembly := hg.decomposition
  let U := PELModuli.IntegralModel.ProductDimensions.bettiIso (Intrinsic.Base.singleBaseAlbaneseIso D) 1
  apply U.injective
  rw [map_sum]
  have hterm (j : Fin D.pel.componentCount) :
      U (PELModuli.IntegralModel.Product.bettiPullbackQ (nativeReferenceProjection D B ψ j) 1
        ((e j).symm (nativeReferenceCoordinates D hg x j))) =
      PELModuli.IntegralModel.Product.bettiPullbackQ
        ((Over.pullback D.pel.complexPoint).map (Pi.π (fun k => (D.pel.components.A k).X) j) ≫ ψ j) 1
          ((e j).symm (nativeReferenceCoordinates D hg x j)) := by
    change ((PELModuli.IntegralModel.Product.bettiPullbackQ (Intrinsic.Base.singleBaseAlbaneseIso D).hom 1).comp
      (PELModuli.IntegralModel.Product.bettiPullbackQ (nativeReferenceProjection D B ψ j) 1)) _ = _
    rw [← PELModuli.IntegralModel.Product.bettiPullbackQ_comp]
    unfold nativeReferenceProjection
    rw [Iso.hom_inv_id_assoc]
  simp_rw [hterm]
  exact reference_projection_reconstruction D.pel.components D.pel.complexPoint
    (asIso D.pel.componentAssembly) hg.betti.1 B b ψ hb e he (U x)

end

/-! Native Hecke operators preserve the Hodge structure by geometric
pullback, reference reconstruction, and actual clearing of denominators. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped TensorProduct _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj

variable {E K : Type} [Field E] [NumberField E] [NumberField.IsCMField E]
  [Field K] [NumberField K] {s q : ℕ} [Fact q.Prime]
  {Index Ga MpR MpF MpA : Type} [Fintype Index] [DecidableEq Index]
  [Group Ga] [TopologicalSpace Ga] [Group MpR] [Group MpF] [Group MpA]
  (D : RepresentationTheory.Theta.Geometric.Data.ActiveHeckeThetaData E K s q Index Ga MpR MpF MpA)

/-- No preservation predicate is an input: every actual algebraic self-map
of the native complex Albanese preserves its transported geometric Hodge structure. -/
theorem native_algebraic_pullback_isHodgeMap
    (hHodgeDecomposition : Mem.HodgeDecompositionInput) (hConstruction : PELModuli.IntegralModel.Albanese.ConstructionInput) (hHodgeComparison : PELModuli.IntegralModel.AlbaneseCohomology.HodgeComparisonInput)
    (hg : D.pel.HasIntegralModelGeometry) (f : D.pel.complexAlbanese.X ⟶ D.pel.complexAlbanese.X) :
    ComplexMultiplication.WeightOne.CM.IsHodgeMap (Intrinsic.Base.nativeH1 D hHodgeDecomposition hg) (Intrinsic.Base.nativeH1 D hHodgeDecomposition hg) (PELModuli.IntegralModel.Product.bettiPullbackQ f 1) := by
  choose B b ψ e _ hb he hback using ReferenceAlbanese.Intrinsic.native_component_reference D hHodgeDecomposition hConstruction hHodgeComparison hg
  let u := fun j => (e j).symm.toLinearMap.comp
    ((LinearMap.proj j).comp (nativeReferenceCoordinates D hg))
  let g := nativeReferenceProjection D B ψ
  have hu (j : Fin D.pel.componentCount) :
      ComplexMultiplication.WeightOne.CM.IsHodgeMap (Intrinsic.Base.nativeH1 D hHodgeDecomposition hg)
        (Mem.canonicalH1 hHodgeDecomposition (B j).variety.presentation) (u j) :=
    (hback j).comp (nativeReferenceCoordinates_isHodgeMap D hHodgeDecomposition hg j)
  have hr : (∑ j, (PELModuli.IntegralModel.Product.bettiPullbackQ (g j) 1).comp (u j)) = LinearMap.id := by
    ext x
    simp only [LinearMap.sum_apply, LinearMap.comp_apply, LinearMap.id_apply]
    exact native_reference_reconstruction D hg B b ψ hb e he x
  have hrc (x : ComplexMultiplication.WeightOne.CM.Complexification D.pel.H1) :
      ∑ j, (PELModuli.IntegralModel.Product.bettiPullbackQ (g j) 1).baseChange ℂ ((u j).baseChange ℂ x) = x := by
    have h := congrArg (LinearMap.baseChangeHom ℚ ℂ D.pel.H1 D.pel.H1) hr
    simp only [map_sum, LinearMap.baseChangeHom_apply, LinearMap.baseChange_comp,
      LinearMap.baseChange_id] at h
    simpa only [LinearMap.sum_apply, LinearMap.comp_apply, LinearMap.id_apply] using
      LinearMap.congr_fun h x
  intro x hx
  rw [← hrc x, map_sum]
  apply (Intrinsic.Base.nativeH1 D hHodgeDecomposition hg).holomorphic.sum_mem
  intro j _
  have hj := Intrinsic.ProjectivePullback.native_projective_pullback_isHodgeMap D hHodgeDecomposition hg (B j).variety.presentation
    (f ≫ g j) ((u j).baseChange ℂ x) (hu j x hx)
  rw [PELModuli.IntegralModel.Product.bettiPullbackQ_comp, LinearMap.baseChange_comp] at hj
  exact hj

theorem native_integral_pullback_isHodgeMap
    (hHodgeDecomposition : Mem.HodgeDecompositionInput) (hConstruction : PELModuli.IntegralModel.Albanese.ConstructionInput) (hHodgeComparison : PELModuli.IntegralModel.AlbaneseCohomology.HodgeComparisonInput)
    (hg : D.pel.HasIntegralModelGeometry) (a : D.pel.EndK) :
    ComplexMultiplication.WeightOne.CM.IsHodgeMap (Intrinsic.Base.nativeH1 D hHodgeDecomposition hg) (Intrinsic.Base.nativeH1 D hHodgeDecomposition hg) (D.pel.pullbackH1Integral a) :=
  native_algebraic_pullback_isHodgeMap D hHodgeDecomposition hConstruction hHodgeComparison hg
    ((Over.pullback D.pel.complexGenericPoint).map (AbelianScheme.TateComparison.End.endSchemeMap D.pel.albaneseGroup.X a))

theorem native_rational_pullback_isHodgeMap
    (hHodgeDecomposition : Mem.HodgeDecompositionInput) (hConstruction : PELModuli.IntegralModel.Albanese.ConstructionInput) (hHodgeComparison : PELModuli.IntegralModel.AlbaneseCohomology.HodgeComparisonInput)
    (hg : D.pel.HasIntegralModelGeometry) (a : D.pel.EndQ) (f : Module.End ℚ D.pel.H1)
    (hf : D.pel.IsRationalH1Pullback a f) :
    ComplexMultiplication.WeightOne.CM.IsHodgeMap (Intrinsic.Base.nativeH1 D hHodgeDecomposition hg) (Intrinsic.Base.nativeH1 D hHodgeDecomposition hg) f := by
  obtain ⟨n, hn, b, hb⟩ := hf.1
  have hden := hf.2 n hn b hb
  have hnq : (n : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.ne_of_gt hn)
  intro x hx
  have h := native_integral_pullback_isHodgeMap D hHodgeDecomposition hConstruction hHodgeComparison hg b x hx
  rw [← hden, LinearMap.baseChange_smul, LinearMap.smul_apply] at h
  exact (Submodule.smul_mem_iff ((Intrinsic.Base.nativeH1 D hHodgeDecomposition hg).holomorphic.restrictScalars ℚ) hnq).mp h

theorem native_hecke_isHodgeMap
    (hHodgeDecomposition : Mem.HodgeDecompositionInput) (hConstruction : PELModuli.IntegralModel.Albanese.ConstructionInput) (hHodgeComparison : PELModuli.IntegralModel.AlbaneseCohomology.HodgeComparisonInput)
    (hg : D.pel.HasIntegralModelGeometry) (hq : D.pel.IsGoodCompletelySplitPrime)
    (hIsogenyQuotient : D.pel.RealizesIsogenyQuotient) (A : RepresentationTheory.Theta.Geometric.TateComparison.Action D.pel)
    (hA : A.IsRealization D.pel hg hq hIsogenyQuotient) (t : AbelianScheme.TateComparison.HeckeKernel.Hecke s q) :
    ComplexMultiplication.WeightOne.CM.IsHodgeMap (Intrinsic.Base.nativeH1 D hHodgeDecomposition hg) (Intrinsic.Base.nativeH1 D hHodgeDecomposition hg) (A.cohomologyAction t) :=
  native_rational_pullback_isHodgeMap D hHodgeDecomposition hConstruction hHodgeComparison hg
    (A.algebraAction t) (A.cohomologyAction t) (hA.cohomology t)

theorem native_active_hecke_isHodgeMap
    (hHodgeDecomposition : Mem.HodgeDecompositionInput) (hConstruction : PELModuli.IntegralModel.Albanese.ConstructionInput) (hHodgeComparison : PELModuli.IntegralModel.AlbaneseCohomology.HodgeComparisonInput)
    (hg : D.pel.HasIntegralModelGeometry) (hq : D.pel.IsGoodCompletelySplitPrime)
    (hIsogenyQuotient : D.pel.RealizesIsogenyQuotient) (A : RepresentationTheory.Theta.Geometric.TateComparison.Action D.pel)
    (hA : A.IsRealization D.pel hg hq hIsogenyQuotient)
    (e : RepresentationTheory.Theta.Geometric.SphericalGU.Spherical.SL3Hecke q ≃ₐ[ℚ] RepresentationTheory.Theta.Geometric.SphericalGU.Spherical.activeAlgebra q D.pel.reference.distinguished)
    (t : RepresentationTheory.Theta.Geometric.SphericalGU.Spherical.SL3Hecke q) :
    ComplexMultiplication.WeightOne.CM.IsHodgeMap (Intrinsic.Base.nativeH1 D hHodgeDecomposition hg) (Intrinsic.Base.nativeH1 D hHodgeDecomposition hg) (Intrinsic.Forms.activeBettiAction D A e t) :=
  native_hecke_isHodgeMap D hHodgeDecomposition hConstruction hHodgeComparison hg hq hIsogenyQuotient A hA
    (RepresentationTheory.Theta.Geometric.Intrinsic.Action.activeHeckeMap q D.pel.reference.distinguished e t)

end

end OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.IntrinsicHecke.Intrinsic
