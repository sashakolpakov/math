import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Intrinsic.ComplexKernelFaithfulness
import OAI.RepresentationTheory.Theta.Geometric.Holomorphic.DimensionBound
import OAI.AlgebraicGeometry.Foundations.Scheme.OpenFunctionField
import OAI.AlgebraicGeometry.Foundations.Scheme.ComplexPointExistence
import OAI.AlgebraicGeometry.Foundations.Scheme.SupportDimension

/-! # Fine PEL Dimension -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily

noncomputable section

section

/-! Actual smooth integral subspaces of the fine PEL model have
injective holomorphic ball periods and complex dimension at most two. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped Classical

open OAI.RepresentationTheory.Theta.Geometric.Holomorphic.DimensionBound

attribute [local irreducible] Models.FinePELModel.complexTestFamily

variable {E K : Type} [Field E] [NumberField E] [NumberField.IsCMField E] [IsGalois ℚ E]
    [Field K] {s N : ℕ} {P : Datum.RankThreePELDatum E s} {iota : E →+* K}
    (M : Models.FinePELModel P iota N) (hM : M.IsFine) (κ : K →+* ℂ) (hκ : κ.comp iota = P.μ)
    {S : Over Foundations.Scheme.ProjectiveSpace.complexBase} [IsIntegral S.left] [Smooth S.hom]
    (f : S ⟶ M.complexFiber κ) [Mono f] (x : ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints S)

include hM hκ in
theorem Models.FinePELModel.exists_injective_native_ball_periods
    (hs : 0 < s) (hdegree : Module.finrank ℚ E = 2 * s) (hP : P.IsAdmissible) (hN : 0 < N) :
    ∃ (C : PELModuli.CMPoints.IntrinsicFamilyCharts.NativeFamilyCharts (M.complexTestFamily κ f).polarized.abelian x)
      (O : Set (RepresentationTheory.Theta.Geometric.Intrinsic.FamilyFrames.FamilyChartBase C)) (period : RepresentationTheory.Theta.Geometric.Intrinsic.FamilyFrames.FamilyChartBase C → Geometry.ComplexBall.PrescribedSignsB.BallChart),
      IsOpen O ∧ RepresentationTheory.Theta.Geometric.Intrinsic.FamilyFrames.familyChartCenter C ∈ O ∧ DifferentiableOn ℂ period O ∧
      Set.MapsTo period O P.domain ∧ Set.InjOn period O := by
  let A := M.complexTestFamily κ f
  obtain ⟨C, F, H, e₀, O, period, hO, hx, hsub, _, hhol, hp⟩ :=
    PEL.Objects.PELObject.exists_complex_family_ball_periods (κ := κ) (hκ := hκ) (A := A) hs hdegree hP x hN
  refine ⟨C, O, period, hO, hx, hhol, fun z hz => (hp z hz).1, ?_⟩
  intro z hz w hw heq
  have hker := (hp z hz).2.trans
    ((congrArg (fun v : Geometry.ComplexBall.PrescribedSignsB.BallChart => Submodule.span ℂ {Geometry.ComplexBall.PrescribedSignsB.lineVector v}) heq).trans (hp w hw).2.symm)
  have hpoint := M.point_eq_of_native_embeddingKernel_eq hM κ hκ f H hs hdegree hP e₀
    ⟨z, hsub hz⟩ ⟨w, hsub hw⟩ hker
  exact RepresentationTheory.Theta.Geometric.Family.ChartOpenImage.familyChartParameter_injective C (H.compatible.subset_chart (hsub hz))
    (H.compatible.subset_chart (hsub hw)) ((cancel_mono f).mp hpoint)

include hM hκ f x in
theorem Models.FinePELModel.smooth_subspace_dimension_le_two
    (hs : 0 < s) (hdegree : Module.finrank ℚ E = 2 * s) (hP : P.IsAdmissible) (hN : 0 < N) :
    Betti.AffineDimension.Realization.functionFieldDifferentialDimension S.hom ≤ 2 := by
  obtain ⟨C, O, period, hO, hx, hhol, _, hi⟩ := M.exists_injective_native_ball_periods hM κ hκ f x hs hdegree hP hN
  have hdim := RepresentationTheory.Theta.Geometric.Holomorphic.DimensionBound.finrank_le_of_holomorphic_injOn hO ⟨_, hx⟩ hhol hi
  rw [C.dimension] at hdim
  simpa only [Geometry.ComplexBall.PrescribedSignsB.BallChart, Module.finrank_pi, Module.finrank_self, Finset.sum_const,
    Finset.card_univ, Fintype.card_fin, smul_eq_mul, mul_one] using hdim

end

section

/-! The actual dense smooth locus bounds the dimension of every integral
finite-type subspace of the fine PEL model. Smoothness of the moduli scheme
is not assumed in this dimension argument. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

variable {E K : Type} [Field E] [NumberField E] [NumberField.IsCMField E] [IsGalois ℚ E]
    [Field K] {s N : ℕ} {P : Datum.RankThreePELDatum E s} {iota : E →+* K}
    (M : Models.FinePELModel P iota N) (hM : M.IsFine) (κ : K →+* ℂ) (hκ : κ.comp iota = P.μ)
    {S : Over Foundations.Scheme.ProjectiveSpace.complexBase} [IsIntegral S.left] [LocallyOfFiniteType S.hom]
    (f : S ⟶ M.complexFiber κ) [Mono f]

include hM hκ f in
theorem Models.FinePELModel.integral_subspace_dimension_le_two
    (hs : 0 < s) (hdegree : Module.finrank ℚ E = 2 * s) (hP : P.IsAdmissible) (hN : 0 < N) :
    Foundations.Scheme.TranscendenceDimension.schemeTranscendenceDimension S.hom ≤ 2 := by
  let U := S.hom.smoothLocus
  have hU : genericPoint S.left ∈ U := S.hom.genericPoint_mem_smoothLocus_of_perfectField
  have : Nonempty U := ⟨⟨genericPoint S.left, hU⟩⟩
  have : IsIntegral U := isIntegral_of_isOpenImmersion U.ι
  have : Smooth (U.ι ≫ S.hom) := by
    apply Scheme.Hom.smoothLocus_eq_top_iff.mp
    rw [← Scheme.Hom.preimage_smoothLocus_eq]
    apply le_antisymm le_top
    intro y _
    exact y.property
  let T : Over Foundations.Scheme.ProjectiveSpace.complexBase := Over.mk (U.ι ≫ S.hom)
  have : IsIntegral T.left := inferInstanceAs (IsIntegral U)
  have : Smooth T.hom := inferInstanceAs (Smooth (U.ι ≫ S.hom))
  let j : T ⟶ S := Over.homMk U.ι
  have : Mono j := Over.mono_of_mono_left j
  let x : ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints T := Classical.choice (Foundations.Scheme.ComplexPointExistence.nonempty_complexOverPoints T.hom)
  have hd := M.smooth_subspace_dimension_le_two hM κ hκ (j ≫ f) x hs hdegree hP hN
  calc
    Foundations.Scheme.TranscendenceDimension.schemeTranscendenceDimension S.hom = Foundations.Scheme.TranscendenceDimension.schemeTranscendenceDimension T.hom :=
      (Foundations.Scheme.OpenFunctionField.schemeTranscendenceDimension_open S.hom U).symm
    _ = Betti.AffineDimension.Realization.functionFieldDifferentialDimension T.hom :=
      Foundations.Scheme.TranscendenceDimension.schemeTranscendenceDimension_eq_functionFieldDifferentialDimension T.hom
    _ ≤ 2 := hd

end

/-! Every irreducible closed support of the constructed native complex
moduli scheme has dimension at most two. The reduced induced scheme is
used to apply the integral-subspace argument. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace

def FinePELDimension.closedSupportOver (X : Over Foundations.Scheme.ProjectiveSpace.complexBase) (Z : IrreducibleCloseds X.left) : Over Foundations.Scheme.ProjectiveSpace.complexBase :=
  Over.mk (CycleClass.Geometric.SupportFiniteType.supportStructureMap Z X.hom)

instance FinePELDimension.closedSupportOver_integral (X : Over Foundations.Scheme.ProjectiveSpace.complexBase) (Z : IrreducibleCloseds X.left) :
    IsIntegral (FinePELDimension.closedSupportOver X Z).left := inferInstanceAs (IsIntegral (CycleClass.Geometric.GenericPoint.reducedSupportScheme Z))

instance FinePELDimension.closedSupportOver_locallyFiniteType (X : Over Foundations.Scheme.ProjectiveSpace.complexBase) [LocallyOfFiniteType X.hom]
    (Z : IrreducibleCloseds X.left) : LocallyOfFiniteType (FinePELDimension.closedSupportOver X Z).hom :=
  inferInstanceAs (LocallyOfFiniteType (CycleClass.Geometric.SupportFiniteType.supportStructureMap Z X.hom))

def FinePELDimension.closedSupportInclusion (X : Over Foundations.Scheme.ProjectiveSpace.complexBase) (Z : IrreducibleCloseds X.left) :
    FinePELDimension.closedSupportOver X Z ⟶ X := Over.homMk (CycleClass.Geometric.GenericPoint.reducedSupportι Z)

instance FinePELDimension.closedSupportInclusion_mono (X : Over Foundations.Scheme.ProjectiveSpace.complexBase) (Z : IrreducibleCloseds X.left) :
    Mono (FinePELDimension.closedSupportInclusion X Z) := by
  have : Mono (FinePELDimension.closedSupportInclusion X Z).left := inferInstanceAs (Mono (CycleClass.Geometric.GenericPoint.reducedSupportι Z))
  exact Over.mono_of_mono_left _

theorem FinePELDimension.closedSupportOver_dimension (X : Over Foundations.Scheme.ProjectiveSpace.complexBase) (Z : IrreducibleCloseds X.left) :
    Foundations.Scheme.TranscendenceDimension.schemeTranscendenceDimension (FinePELDimension.closedSupportOver X Z).hom =
      Foundations.Scheme.SupportDimension.supportTranscendenceDimension Z X.hom := rfl

variable {E K : Type} [Field E] [NumberField E] [NumberField.IsCMField E] [IsGalois ℚ E]
    [Field K] {s N : ℕ} {P : Datum.RankThreePELDatum E s} {iota : E →+* K}
    (M : Models.FinePELModel P iota N) (hM : M.IsFine) (κ : K →+* ℂ) (hκ : κ.comp iota = P.μ)
    [LocallyOfFiniteType M.space.hom]

omit [IsGalois ℚ E] in
theorem Models.FinePELModel.complexFiber_locallyFiniteType : LocallyOfFiniteType (M.complexFiber κ).hom :=
  inferInstanceAs (LocallyOfFiniteType
    (Limits.pullback.snd M.space.hom (Spec.map (CommRingCat.ofHom κ))))

attribute [local irreducible] Models.FinePELModel.complexFiber FinePELDimension.closedSupportOver FinePELDimension.closedSupportInclusion

include hM hκ in
theorem Models.FinePELModel.support_dimension_le_two
    (hs : 0 < s) (hdegree : Module.finrank ℚ E = 2 * s) (hP : P.IsAdmissible) (hN : 0 < N)
    (Z : IrreducibleCloseds (M.complexFiber κ).left) :
    Foundations.Scheme.SupportDimension.supportTranscendenceDimension Z (M.complexFiber κ).hom ≤ 2 := by
  have : LocallyOfFiniteType (M.complexFiber κ).hom := M.complexFiber_locallyFiniteType κ
  have h := M.integral_subspace_dimension_le_two hM κ hκ
    (FinePELDimension.closedSupportInclusion (M.complexFiber κ) Z) hs hdegree hP hN
  rw [FinePELDimension.closedSupportOver_dimension] at h
  exact h

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily
