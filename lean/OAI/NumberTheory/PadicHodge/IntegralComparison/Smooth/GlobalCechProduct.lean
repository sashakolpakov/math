import OAI.NumberTheory.PadicHodge.IntegralComparison.Smooth.CechAnalyticCoordinates
import OAI.NumberTheory.PadicHodge.IntegralComparison.Global.SmoothCohomologyCup

/-! # Global Cech Product -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Smooth.GlobalCechProduct.Comparison

noncomputable section

section

/-! The global-to-native comparison is actual restriction of a
smooth form to the cover, followed by its degree-zero Čech inclusion. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry _root_.TopologicalSpace Opposite
open scoped Simplicial

variable (X : Over AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.complexBase) [IsIntegral X.left] [Smooth X.hom]
  {ι : Type} (U : ι → X.left.Opens)

def restrictionComponent (p : ℕ) (t : Fin 1 → ι) :
    ModuleCat.of ℂ (Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm (AlgebraicGeometry.Comparison.Betti.RegularSmoothness.NativeModel X) (AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X) p) ⟶
      ((AlgebraicGeometry.Comparison.Betti.Smooth.SheafMap.zariskiSmoothPresheafComplex X).X p).obj (op (∏ᶜ (U ∘ t))) :=
  ModuleCat.ofHom (Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm.onOpen
    (E := AlgebraicGeometry.Comparison.Betti.RegularSmoothness.NativeModel X) (M := AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X)
    (AlgebraicGeometry.Comparison.Betti.Open.AffineIsoEvaluation.analyticOpen X (∏ᶜ (U ∘ t))))

def restriction (p : ℕ) :
    Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm (AlgebraicGeometry.Comparison.Betti.RegularSmoothness.NativeModel X) (AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X) p →ₗ[ℂ]
      (AlgebraicSmoothCechProduct.smoothCochains X (CechAnalyticCoordinates.GlobalComparison.nerve X U) p).obj ⦋0⦌ :=
  (Pi.lift (restrictionComponent X U p)).hom

theorem projection_restriction (p : ℕ) (a : Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm
    (AlgebraicGeometry.Comparison.Betti.RegularSmoothness.NativeModel X) (AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X) p) (t : Fin 1 → ι) :
    Cech.BilinearPairing.projection (CechAnalyticCoordinates.GlobalComparison.nerve X U) ((AlgebraicGeometry.Comparison.Betti.Smooth.SheafMap.zariskiSmoothPresheafComplex X).X p) ⦋0⦌ t
        (restriction X U p a) =
      Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm.onOpen (AlgebraicGeometry.Comparison.Betti.Open.AffineIsoEvaluation.analyticOpen X (∏ᶜ (U ∘ t))) a :=
  ConcreteCategory.congr_hom (Pi.lift_comp_π (restrictionComponent X U p) t) a

theorem sectionCoordinates_apply (p a : ℕ)
    (z : (AlgebraicSmoothCechProduct.smoothCochains X (CechAnalyticCoordinates.GlobalComparison.nerve X U) p).obj ⦋a⦌)
    (t : Fin (a + 1) → ι) :
    (CechAnalyticCoordinates.GlobalComparison.sectionCoordinates X U p a).hom z t =
      (AlgebraicGeometry.Comparison.Betti.Cech.PushforwardCoordinates.cechPushforwardSectionIso (AlgebraicGeometry.Comparison.Betti.Analytification.Base.analytificationMap X) U
        (Analysis.DifferentialForms.Manifold.ManifoldSheaf.manifoldFormPresheaf (AlgebraicGeometry.Comparison.Betti.RegularSmoothness.NativeModel X) (AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X) p) t).hom
        ((AlgebraicGeometry.Comparison.Betti.Module.CechCoordinates.cechIntersectionSectionIso
          ((AlgebraicGeometry.Comparison.Betti.Smooth.SheafMap.zariskiSmoothPresheafComplex X).X p) U t).hom
          (Cech.BilinearPairing.projection (CechAnalyticCoordinates.GlobalComparison.nerve X U) ((AlgebraicGeometry.Comparison.Betti.Smooth.SheafMap.zariskiSmoothPresheafComplex X).X p) ⦋a⦌ t z)) := by
  change (AlgebraicGeometry.Comparison.Betti.Cech.PushforwardCoordinates.cechPushforwardSectionIso (AlgebraicGeometry.Comparison.Betti.Analytification.Base.analytificationMap X) U
      (Analysis.DifferentialForms.Manifold.ManifoldSheaf.manifoldFormPresheaf (AlgebraicGeometry.Comparison.Betti.RegularSmoothness.NativeModel X) (AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X) p) t).hom
    ((AlgebraicGeometry.Comparison.Betti.Module.CechCoordinates.moduleCechCoordinatesIso ((AlgebraicGeometry.Comparison.Betti.Smooth.SheafMap.zariskiSmoothPresheafComplex X).X p) U a).hom z t) = _
  exact congrArg _ (AlgebraicGeometry.Comparison.Betti.Module.CechCoordinates.moduleCechCoordinatesIso_hom_apply
    ((AlgebraicGeometry.Comparison.Betti.Smooth.SheafMap.zariskiSmoothPresheafComplex X).X p) U a z t)

theorem restriction_coordinates (p : ℕ) (a : Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm
    (AlgebraicGeometry.Comparison.Betti.RegularSmoothness.NativeModel X) (AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X) p) :
    (CechAnalyticCoordinates.GlobalComparison.sectionCoordinates X U p 0).hom (restriction X U p a) =
      Analysis.DifferentialForms.Manifold.CechAugmentation.manifoldCechAugmentation (fun i => AlgebraicGeometry.Comparison.Betti.Open.AffineIsoEvaluation.analyticOpen X (U i)) p a := by
  funext t
  let W₀ : Opens (AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X) := AlgebraicGeometry.Comparison.Betti.Open.AffineIsoEvaluation.analyticOpen X (∏ᶜ (U ∘ t))
  let W₁ : Opens (AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X) := AlgebraicGeometry.Comparison.Betti.Open.AffineIsoEvaluation.analyticOpen X (AlgebraicTopology.DeRham.Comparison.SmoothCech.cechIntersection U t)
  let W₂ : Opens (AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X) :=
    AlgebraicTopology.DeRham.Comparison.SmoothCech.cechIntersection (fun i => AlgebraicGeometry.Comparison.Betti.Open.AffineIsoEvaluation.analyticOpen X (U i)) t
  have h₀₁ : W₁ ≤ W₀ :=
    AlgebraicGeometry.Comparison.Betti.Open.SmoothForms.analyticOpen_mono X (le_of_eq (AlgebraicGeometry.Comparison.Betti.Cech.Intersections.cechIntersection_eq_categorical U t))
  have h₁₂ : W₂ ≤ W₁ :=
    le_of_eq (show W₁ = W₂ from AlgebraicGeometry.Comparison.Betti.Cech.PushforwardCoordinates.cechIntersection_preimage (AlgebraicGeometry.Comparison.Betti.Analytification.Base.analytificationMap X) U t).symm
  let e₁ := AlgebraicGeometry.Comparison.Betti.Module.CechCoordinates.cechIntersectionSectionIso ((AlgebraicGeometry.Comparison.Betti.Smooth.SheafMap.zariskiSmoothPresheafComplex X).X p) U t
  let e₂ := AlgebraicGeometry.Comparison.Betti.Cech.PushforwardCoordinates.cechPushforwardSectionIso (AlgebraicGeometry.Comparison.Betti.Analytification.Base.analytificationMap X) U
    (Analysis.DifferentialForms.Manifold.ManifoldSheaf.manifoldFormPresheaf (AlgebraicGeometry.Comparison.Betti.RegularSmoothness.NativeModel X) (AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X) p) t
  have h₁ : e₁.hom (Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm.onOpen W₀ a) = Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm.onOpen W₁ a :=
    Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm.restrict_onOpen h₀₁ a
  have h₂ : e₂.hom (Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm.onOpen W₁ a) = Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm.onOpen W₂ a :=
    Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm.restrict_onOpen h₁₂ a
  exact (sectionCoordinates_apply X U p 0 (restriction X U p a) t).trans
    ((congrArg e₂.hom ((congrArg e₁.hom (projection_restriction X U p a t)).trans h₁)).trans h₂)

theorem globalToNative_apply (p : ℕ) (a : Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm
    (AlgebraicGeometry.Comparison.Betti.RegularSmoothness.NativeModel X) (AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X) p) :
    (CechAnalyticCoordinates.GlobalComparison.globalToNative X U).f p a =
      (AlgebraicSmoothCechProduct.smoothBicomplex X (CechAnalyticCoordinates.GlobalComparison.nerve X U)).ιTotal
        (.up ℕ) p 0 p rfl (restriction X U p a) := by
  let e := (HomologicalComplex.eval (ModuleCat.{0} ℂ) (.up ℕ) p).mapIso (CechAnalyticCoordinates.GlobalComparison.nativeToAnalyticIso X U)
  apply e.toLinearEquiv.injective
  have hg := ConcreteCategory.congr_hom (C := ModuleCat.{0} ℂ)
    (congrArg (fun f => f.f p) (CechAnalyticCoordinates.GlobalComparison.globalToNative_comp_iso X U)) a
  have hi := ConcreteCategory.congr_hom (C := ModuleCat.{0} ℂ)
    (CechAnalyticCoordinates.GlobalComparison.inclusion_zero_iso X U p) (restriction X U p a)
  have hr := congrArg (Analysis.DifferentialForms.Manifold.CechDeRham.manifoldCechTotalInclusion (E := AlgebraicGeometry.Comparison.Betti.RegularSmoothness.NativeModel X)
    (fun i => AlgebraicGeometry.Comparison.Betti.Open.AffineIsoEvaluation.analyticOpen X (U i)) 0 p p (Nat.zero_add p))
      (restriction_coordinates X U p a)
  exact hg.trans (hi.trans hr).symm

end

section

/-! Restriction from global smooth forms to the original native
Čech total preserves exterior products and the induced cohomology products. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry _root_.TopologicalSpace Opposite
open scoped Simplicial _root_.Manifold ContDiff

theorem onOpen_wedge {E M : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
    (W : Opens M) (p q : ℕ) (a : Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm E M p) (b : Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm E M q) :
    Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm.onOpen W (AlgebraicTopology.Kunneth.ManifoldWedge.Constructions.manifoldWedge a b) =
      Open.SmoothProducts.wedge W p q (Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm.onOpen W a) (Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm.onOpen W b) := by
  apply Analysis.DifferentialForms.Manifold.Open.SmoothOpenManifoldForm.ext
  intro x
  change AlgebraicTopology.Kunneth.ManifoldWedge.Constructions.manifoldWedge a b x = AlgebraicGeometry.DivisorClass.Chern.Open.ManifoldWedge.openManifoldWedge _ _ x
  rw [AlgebraicGeometry.DivisorClass.Chern.Open.ManifoldWedge.openManifoldWedge_apply, Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm.onOpen_apply, Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm.onOpen_apply]
  exact AlgebraicTopology.Kunneth.ManifoldWedge.Constructions.manifoldWedge_apply a b x

variable (X : Over AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.complexBase) [IsIntegral X.left] [Smooth X.hom]
  {ι : Type} (U : ι → X.left.Opens)

theorem restriction_pairing (p q : ℕ)
    (a : Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm (AlgebraicGeometry.Comparison.Betti.RegularSmoothness.NativeModel X) (AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X) p)
    (b : Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm (AlgebraicGeometry.Comparison.Betti.RegularSmoothness.NativeModel X) (AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X) q) :
    AlgebraicSmoothCechProduct.pairing X (CechAnalyticCoordinates.GlobalComparison.nerve X U) p q ⦋0⦌
        (restriction X U p a) (restriction X U q b) =
      restriction X U (p + q) (AlgebraicTopology.Kunneth.ManifoldWedge.Constructions.manifoldWedge a b) := by
  apply Module.ProductScalarKernel.element_ext
    (fun t : Fin 1 → ι => ((AlgebraicGeometry.Comparison.Betti.Smooth.SheafMap.zariskiSmoothPresheafComplex X).X (p + q)).obj (op (∏ᶜ (U ∘ t))))
  intro t
  let W := AlgebraicGeometry.Comparison.Betti.Open.AffineIsoEvaluation.analyticOpen X (∏ᶜ (U ∘ t))
  have hp := TotalD.AlgebraicCechProduct.native_projection_pairing X (CechAnalyticCoordinates.GlobalComparison.nerve X U) p q ⦋0⦌ t
    (restriction X U p a) (restriction X U q b)
  have ha := projection_restriction X U p a t
  have hb := projection_restriction X U q b t
  have hr := projection_restriction X U (p + q) (AlgebraicTopology.Kunneth.ManifoldWedge.Constructions.manifoldWedge a b) t
  exact hp.trans ((congrArg₂
    (fun (s : Analysis.DifferentialForms.Manifold.Open.SmoothOpenManifoldForm (AlgebraicGeometry.Comparison.Betti.RegularSmoothness.NativeModel X) W p)
      (t : Analysis.DifferentialForms.Manifold.Open.SmoothOpenManifoldForm (AlgebraicGeometry.Comparison.Betti.RegularSmoothness.NativeModel X) W q) => Open.SmoothProducts.wedge W p q s t)
    ha hb).trans ((onOpen_wedge W p q a b).symm.trans hr.symm))

theorem cup_zero_zero (p q : ℕ)
    (a : (AlgebraicSmoothCechProduct.smoothCochains X (CechAnalyticCoordinates.GlobalComparison.nerve X U) p).obj ⦋0⦌)
    (b : (AlgebraicSmoothCechProduct.smoothCochains X (CechAnalyticCoordinates.GlobalComparison.nerve X U) q).obj ⦋0⦌) :
    AlgebraicSmoothCechProduct.cup X (CechAnalyticCoordinates.GlobalComparison.nerve X U) p q 0 0 a b =
      AlgebraicSmoothCechProduct.pairing X (CechAnalyticCoordinates.GlobalComparison.nerve X U) p q ⦋0⦌ a b := by
  have hf : AlgebraicTopology.Products.SimplexFaceIdentities.frontInclusion 0 0 = 𝟙 ⦋0⦌ := by ext i; rfl
  have hb : AlgebraicTopology.Products.SimplexFaceIdentities.backInclusion 0 0 = 𝟙 ⦋0⦌ := by ext i; rfl
  change AlgebraicSmoothCechProduct.pairing X (CechAnalyticCoordinates.GlobalComparison.nerve X U) p q ⦋0⦌
    ((AlgebraicSmoothCechProduct.smoothCochains X (CechAnalyticCoordinates.GlobalComparison.nerve X U) p).map (AlgebraicTopology.Products.SimplexFaceIdentities.frontInclusion 0 0) a)
    ((AlgebraicSmoothCechProduct.smoothCochains X (CechAnalyticCoordinates.GlobalComparison.nerve X U) q).map (AlgebraicTopology.Products.SimplexFaceIdentities.backInclusion 0 0) b) = _
  simp only [hf, hb]
  exact congrArg₂ (fun x y => AlgebraicSmoothCechProduct.pairing X (CechAnalyticCoordinates.GlobalComparison.nerve X U) p q ⦋0⦌ x y)
    (ConcreteCategory.congr_hom
      ((AlgebraicSmoothCechProduct.smoothCochains X (CechAnalyticCoordinates.GlobalComparison.nerve X U) p).map_id ⦋0⦌) a)
    (ConcreteCategory.congr_hom
      ((AlgebraicSmoothCechProduct.smoothCochains X (CechAnalyticCoordinates.GlobalComparison.nerve X U) q).map_id ⦋0⦌) b)

theorem globalToNative_wedge (p q : ℕ)
    (a : Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm (AlgebraicGeometry.Comparison.Betti.RegularSmoothness.NativeModel X) (AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X) p)
    (b : Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm (AlgebraicGeometry.Comparison.Betti.RegularSmoothness.NativeModel X) (AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X) q) :
    (CechAnalyticCoordinates.GlobalComparison.globalToNative X U).f (p + q) (AlgebraicTopology.Kunneth.ManifoldWedge.Constructions.manifoldWedge a b) =
      AlgebraicSmoothCechProduct.totalPairing X (CechAnalyticCoordinates.GlobalComparison.nerve X U) p q
        ((CechAnalyticCoordinates.GlobalComparison.globalToNative X U).f p a) ((CechAnalyticCoordinates.GlobalComparison.globalToNative X U).f q b) := by
  rw [globalToNative_apply, globalToNative_apply, globalToNative_apply]
  have h := TotalD.AlgebraicCechProduct.totalPairing_ι X (CechAnalyticCoordinates.GlobalComparison.nerve X U) p q p 0 q 0 rfl rfl
    (restriction X U p a) (restriction X U q b)
  simp only [Nat.zero_mul, pow_zero, one_smul] at h
  exact (congrArg
    ((AlgebraicSmoothCechProduct.smoothBicomplex X (CechAnalyticCoordinates.GlobalComparison.nerve X U)).ιTotal
      (.up ℕ) (p + q) 0 (p + q) rfl)
    ((cup_zero_zero X U p q (restriction X U p a) (restriction X U q b)).trans
      (restriction_pairing X U p q a b))).symm.trans h.symm

theorem globalToNative_cohomologyCup (p q : ℕ)
    (a : Analysis.DifferentialForms.Manifold.ManifoldDeRham.manifoldDeRhamCohomology (AlgebraicGeometry.Comparison.Betti.RegularSmoothness.NativeModel X) (AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X) p)
    (b : Analysis.DifferentialForms.Manifold.ManifoldDeRham.manifoldDeRhamCohomology (AlgebraicGeometry.Comparison.Betti.RegularSmoothness.NativeModel X) (AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X) q) :
    HomologicalComplex.homologyMap (CechAnalyticCoordinates.GlobalComparison.globalToNative X U) (p + q)
        (Global.SmoothCohomologyCup.cohomologyCup (AlgebraicGeometry.Comparison.Betti.RegularSmoothness.NativeModel X) (AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X) p q a b) =
      AlgebraicSmoothCohomologyProduct.Cech.cohomologyCup X (CechAnalyticCoordinates.GlobalComparison.nerve X U) p q
        (HomologicalComplex.homologyMap (CechAnalyticCoordinates.GlobalComparison.globalToNative X U) p a)
        (HomologicalComplex.homologyMap (CechAnalyticCoordinates.GlobalComparison.globalToNative X U) q b) :=
  Cochain.CupNaturality.Cohomology.cohomologyMap_cup
    (Global.SmoothCohomologyCup.cup (AlgebraicGeometry.Comparison.Betti.RegularSmoothness.NativeModel X) (AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X))
    (AlgebraicSmoothCechProduct.totalPairing X (CechAnalyticCoordinates.GlobalComparison.nerve X U))
    (Global.SmoothCohomologyCup.differential_cup (AlgebraicGeometry.Comparison.Betti.RegularSmoothness.NativeModel X) (AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X))
    (TotalLeibniz.AlgebraicCechProduct.differential_totalPairing X (CechAnalyticCoordinates.GlobalComparison.nerve X U))
    (CechAnalyticCoordinates.GlobalComparison.globalToNative X U) (globalToNative_wedge X U) p q a b

end

/-! The inverse of the genuine global/Čech cohomology comparison
also preserves the proved products. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry _root_.TopologicalSpace

variable (X : Over AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.complexBase) [IsIntegral X.left] [Smooth X.hom]
  [IsSeparated X.hom] [QuasiCompact X.hom]
  {ι : Type} (U : ι → X.left.Opens) (hU : ⨆ i, U i = ⊤)

theorem globalCohomologyIso_inv_cup (p q : ℕ)
    (a : (AlgebraicSmoothCechProduct.smoothTotal X (CechAnalyticCoordinates.GlobalComparison.nerve X U)).homology p)
    (b : (AlgebraicSmoothCechProduct.smoothTotal X (CechAnalyticCoordinates.GlobalComparison.nerve X U)).homology q) :
    (CechAnalyticCoordinates.GlobalComparison.globalCohomologyIso X U hU (p + q)).inv
        (AlgebraicSmoothCohomologyProduct.Cech.cohomologyCup X (CechAnalyticCoordinates.GlobalComparison.nerve X U) p q a b) =
      Global.SmoothCohomologyCup.cohomologyCup (AlgebraicGeometry.Comparison.Betti.RegularSmoothness.NativeModel X) (AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X) p q
        ((CechAnalyticCoordinates.GlobalComparison.globalCohomologyIso X U hU p).inv a) ((CechAnalyticCoordinates.GlobalComparison.globalCohomologyIso X U hU q).inv b) := by
  let e := fun n => (CechAnalyticCoordinates.GlobalComparison.globalCohomologyIso X U hU n).toLinearEquiv
  apply (e (p + q)).injective
  have h := globalToNative_cohomologyCup X U p q ((e p).symm a) ((e q).symm b)
  have h' := h.trans (congrArg₂
    (fun x y => AlgebraicSmoothCohomologyProduct.Cech.cohomologyCup X (CechAnalyticCoordinates.GlobalComparison.nerve X U) p q x y)
    ((e p).apply_symm_apply a) ((e q).apply_symm_apply b))
  exact ((e (p + q)).apply_symm_apply
    (AlgebraicSmoothCohomologyProduct.Cech.cohomologyCup X (CechAnalyticCoordinates.GlobalComparison.nerve X U) p q a b)).trans h'.symm

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Smooth.GlobalCechProduct.Comparison
