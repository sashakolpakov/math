import OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.Intrinsic.IntrinsicForms
import OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.TwoEnergy

/-! # Closed Forms -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.Intrinsic.ClosedForms

noncomputable section

/-! Native theta forms are closed by projective geometry, and hence define actual Betti classes. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

theorem projectiveKaehlerForm_closed (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety)
    (form : AbelianScheme.TateComparison.FormConstants.OneForms V.toOver) :
    letI : IsIntegral V.toOver.left := V.property
    letI : Smooth V.toOver.hom := V.presentation.smooth
    letI : V.toOver.left.IsSeparated := IntrinsicForms.integralProjective_separated V
    Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm.d (KaehlerGluing.globalSmoothForm V.toOver form) = 0 := by
  let : IsIntegral V.toOver.left := V.property
  let : Smooth V.toOver.hom := V.presentation.smooth
  let : V.toOver.left.IsSeparated := IntrinsicForms.integralProjective_separated V
  exact TwoEnergy.Closedness.projective_type10_with_type20_derivative_closed V
    (KaehlerGluing.globalSmoothForm V.toOver form)
    (OpenPurity.Kaehler.globalSmoothForm_pure V.toOver form)
    (OpenPurity.Kaehler.globalSmoothForm_d_pure V.toOver form)

variable {E K : Type} [Field E] [NumberField E] [NumberField.IsCMField E]
  [Field K] [NumberField K] {s q : ℕ} [Fact q.Prime]
  {Index Ga MpR MpF MpA : Type} [Fintype Index] [DecidableEq Index]
  [Group Ga] [TopologicalSpace Ga] [Group MpR] [Group MpF] [Group MpA]
  (D : RepresentationTheory.Theta.Geometric.Data.ActiveHeckeThetaData E K s q Index Ga MpR MpF MpA)

theorem thetaSmoothComponent_closed (hg : D.pel.HasIntegralModelGeometry)
    (Θ : D.sphericalInputs →ₗ[ℂ] D.pel.OneFormsA) (i : Fin D.pel.componentCount)
    (φ : D.sphericalInputs) :
    Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm.d (IntrinsicForms.thetaSmoothComponent D hg Θ i φ) = 0 := by
  exact projectiveKaehlerForm_closed (D.componentVariety hg i) _

def thetaClosedComponent (hg : D.pel.HasIntegralModelGeometry)
    (Θ : D.sphericalInputs →ₗ[ℂ] D.pel.OneFormsA) (i : Fin D.pel.componentCount) :
    D.sphericalInputs →ₗ[ℂ]
      Analysis.DifferentialForms.Manifold.ManifoldDeRham.manifoldClosedForms (D.componentVariety hg i).analyticModel
        (D.componentVariety hg i).analyticSpace 1 :=
  (IntrinsicForms.thetaSmoothComponent D hg Θ i).codRestrict _ (thetaSmoothComponent_closed D hg Θ i)

/-- The class map uses the comparison defined by integration over genuine smooth simplices. -/
def thetaBettiComponent (hg : D.pel.HasIntegralModelGeometry)
    (Θ : D.sphericalInputs →ₗ[ℂ] D.pel.OneFormsA) (i : Fin D.pel.componentCount) :
    D.sphericalInputs →ₗ[ℂ] (D.componentVariety hg i).complexCohomology 1 where
  toFun φ := ((D.componentVariety hg i).deRhamBettiIso 1).hom
    ((D.componentVariety hg i).deRhamClass 1 (thetaClosedComponent D hg Θ i φ))
  map_add' φ ψ := by simp only [map_add]
  map_smul' z φ := by simp only [map_smul, RingHom.id_apply]

theorem thetaBettiComponent_pure (hg : D.pel.HasIntegralModelGeometry)
    (Θ : D.sphericalInputs →ₗ[ℂ] D.pel.OneFormsA) (i : Fin D.pel.componentCount)
    (φ : D.sphericalInputs) :
    thetaBettiComponent D hg Θ i φ ∈ (D.componentVariety hg i).pureBettiSubspace 1 0 := by
  apply ((D.componentVariety hg i).mem_pureBettiSubspace_iff 1 0 _).mpr
  exact ⟨thetaClosedComponent D hg Θ i φ,
    (Analysis.DifferentialForms.Manifold.CovectorAction.hasManifoldBidegree_iff_tangentBidegree _).mp (IntrinsicForms.thetaSmoothComponent_pure D hg Θ i φ), rfl⟩

theorem thetaBettiComponent_integrates (hg : D.pel.HasIntegralModelGeometry)
    (Θ : D.sphericalInputs →ₗ[ℂ] D.pel.OneFormsA) (i : Fin D.pel.componentCount)
    (φ : D.sphericalInputs) :
    (D.componentVariety hg i).bettiToSmoothSingular 1 (thetaBettiComponent D hg Θ i φ) =
      AlgebraicTopology.Cohomology.Singular.Representatives.cochainClass (D.componentVariety hg i).smoothSingularComplex 1
        (AlgebraicTopology.DeRham.Comparison.SmoothSimplexClass.smoothSimplexIntegrationCocycle
          (D.componentVariety hg i).analyticModel (D.componentVariety hg i).analyticSpace 1
          (thetaClosedComponent D hg Θ i φ)) :=
  (D.componentVariety hg i).deRhamBettiIso_formClass 1 (thetaClosedComponent D hg Θ i φ)

def thetaComplexifiedComponent (hg : D.pel.HasIntegralModelGeometry)
    (Θ : D.sphericalInputs →ₗ[ℂ] D.pel.OneFormsA) (i : Fin D.pel.componentCount) :
    D.sphericalInputs →ₗ[ℂ] ComplexMultiplication.WeightOne.CM.Complexification ((D.componentVariety hg i).rationalCohomology 1) :=
  (Mem.bettiComplexification (D.componentVariety hg i).presentation 1).symm.toLinearMap.comp
    (thetaBettiComponent D hg Θ i)

theorem thetaComplexifiedComponent_holomorphic (hHodgeDecomposition : Mem.HodgeDecompositionInput)
    (hg : D.pel.HasIntegralModelGeometry)
    (Θ : D.sphericalInputs →ₗ[ℂ] D.pel.OneFormsA) (i : Fin D.pel.componentCount)
    (φ : D.sphericalInputs) :
    thetaComplexifiedComponent D hg Θ i φ ∈
      (Mem.canonicalH1 hHodgeDecomposition (D.componentVariety hg i).presentation).holomorphic := by
  rw [Naturality.canonicalH1_integral_holomorphic]
  change (Mem.bettiComplexification (D.componentVariety hg i).presentation 1)
    ((Mem.bettiComplexification (D.componentVariety hg i).presentation 1).symm
      (thetaBettiComponent D hg Θ i φ)) ∈ (D.componentVariety hg i).pureBettiSubspace 1 0
  rw [LinearEquiv.apply_symm_apply]
  exact thetaBettiComponent_pure D hg Θ i φ

end

end OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.Intrinsic.ClosedForms
