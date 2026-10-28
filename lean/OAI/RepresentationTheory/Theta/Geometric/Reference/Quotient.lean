import OAI.RepresentationTheory.Theta.Geometric.Reference.QuotientLocal
import OAI.RepresentationTheory.Theta.Geometric.Reference.Component
import OAI.RepresentationTheory.Theta.Geometric.ComponentFormFaithfulness

/-! # Quotient -/

namespace OAI.RepresentationTheory.Theta.Geometric

noncomputable section

section

/-! The original projective reference surface maps onto the entire
arithmetic quotient and is homeomorphic to it via its exact moduli orbits. -/

set_option backward.isDefEq.respectTransparency false
open _root_.CategoryTheory _root_.AlgebraicGeometry Set
open scoped Classical _root_.Manifold

variable {E K : Type} [Field E] [NumberField E] [NumberField.IsCMField E] [IsGalois ℚ E]
    [Field K] [NumberField K] {s q : ℕ} [Fact q.Prime]
    {Index Ga MpR MpF MpA : Type} [Fintype Index] [DecidableEq Index]
    [Group Ga] [TopologicalSpace Ga] [Group MpR] [Group MpF] [Group MpA]
    (D : Data.ActiveHeckeThetaData E K s q Index Ga MpR MpF MpA)
    (hg : D.pel.HasIntegralModelGeometry) (X : AlgebraicGeometry.Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety)
    (f : X.toOver ⟶ D.pel.complexSpace) [Mono f]
    (href : ∀ x : X.analyticSpace, ∃ a : D.domain, x ≫ f = D.referenceModuliMap hg a)
    (hc : D.HasFiniteCoordinates) (hgood : D.pel.IsGoodCompletelySplitPrime)
    (hdegree : Module.finrank ℚ E = 2 * s) (hs : 0 < s) (hdim : X.complexDimension = 2)

local instance Data.ActiveHeckeThetaData.referenceQuotientProjectiveIntegral : IsIntegral X.toOver.left := X.property
local instance Data.ActiveHeckeThetaData.referenceQuotientProjectiveSmooth : Smooth X.toOver.hom := X.presentation.smooth

include hc hgood hdegree hs hdim

theorem Data.ActiveHeckeThetaData.referenceQuotientCoordinates_surjective :
    Function.Surjective (D.referenceQuotientCoordinates hg f href) := by
  let : T2Space D.ArithmeticBallQuotient := D.arithmeticBallQuotient_t2Space hg hc hgood hdegree
  let : ConnectedSpace D.ArithmeticBallQuotient := D.arithmeticBallQuotient_connected hg hc hgood hdegree
  have hloc := D.referenceQuotientCoordinates_localHomeomorph hg f href hc hgood hdegree hs hdim
  have hclosed : IsClosed (range (D.referenceQuotientCoordinates hg f href)) :=
    (isCompact_range hloc.continuous).isClosed
  have hopen : IsOpen (range (D.referenceQuotientCoordinates hg f href)) := hloc.isOpenMap.isOpen_range
  have hne : (range (D.referenceQuotientCoordinates hg f href)).Nonempty :=
    ⟨_, mem_range_self (Classical.choice X.analyticSpace_nonempty)⟩
  exact range_eq_univ.mp (IsClopen.eq_univ ⟨hclosed, hopen⟩ hne)

def Data.ActiveHeckeThetaData.referenceQuotientHomeomorph : X.analyticSpace ≃ₜ D.ArithmeticBallQuotient :=
  let hloc := D.referenceQuotientCoordinates_localHomeomorph hg f href hc hgood hdegree hs hdim
  (Equiv.ofBijective (D.referenceQuotientCoordinates hg f href)
    ⟨D.referenceQuotientCoordinates_injective hg f href hc hgood hdegree,
      D.referenceQuotientCoordinates_surjective hg X f href hc hgood hdegree hs hdim⟩).toHomeomorphOfContinuousOpen
    hloc.continuous hloc.isOpenMap

theorem Data.ActiveHeckeThetaData.referenceQuotientHomeomorph_apply (x : X.analyticSpace) :
    D.referenceQuotientHomeomorph hg X f href hc hgood hdegree hs hdim x =
      D.referenceQuotientCoordinates hg f href x := rfl

theorem Data.ActiveHeckeThetaData.referenceQuotientHomeomorph_inverse_moduli (a : D.domain) :
    ((D.referenceQuotientHomeomorph hg X f href hc hgood hdegree hs hdim).symm
      (D.arithmeticBallProjection a)) ≫ f = D.referenceModuliMap hg a := by
  have h := D.referenceQuotientCoordinates_moduli hg f href hc hgood hdegree
    ((D.referenceQuotientHomeomorph hg X f href hc hgood hdegree hs hdim).symm (D.arithmeticBallProjection a))
  change D.arithmeticModuliMap hg hc hgood hdegree
    ((D.referenceQuotientHomeomorph hg X f href hc hgood hdegree hs hdim)
      ((D.referenceQuotientHomeomorph hg X f href hc hgood hdegree hs hdim).symm (D.arithmeticBallProjection a))) = _ at h
  rw [Homeomorph.apply_symm_apply] at h
  exact h.symm

end

section

/-! The global arithmetic-quotient identification has a holomorphic
inverse with bijective complex differential at every point. -/

set_option backward.isDefEq.respectTransparency false
open _root_.CategoryTheory _root_.AlgebraicGeometry Set Filter
open scoped Classical _root_.Manifold _root_.Topology

variable {E K : Type} [Field E] [NumberField E] [NumberField.IsCMField E] [IsGalois ℚ E]
    [Field K] [NumberField K] {s q : ℕ} [Fact q.Prime]
    {Index Ga MpR MpF MpA : Type} [Fintype Index] [DecidableEq Index]
    [Group Ga] [TopologicalSpace Ga] [Group MpR] [Group MpF] [Group MpA]
    (D : Data.ActiveHeckeThetaData E K s q Index Ga MpR MpF MpA)
    (hg : D.pel.HasIntegralModelGeometry) (X : AlgebraicGeometry.Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety)
    (f : X.toOver ⟶ D.pel.complexSpace) [Mono f]
    (href : ∀ x : X.analyticSpace, ∃ a : D.domain, x ≫ f = D.referenceModuliMap hg a)
    (hc : D.HasFiniteCoordinates) (hgood : D.pel.IsGoodCompletelySplitPrime)
    (hdegree : Module.finrank ℚ E = 2 * s) (hs : 0 < s) (hdim : X.complexDimension = 2)

local instance Data.ActiveHeckeThetaData.referenceInverseProjectiveIntegral : IsIntegral X.toOver.left := X.property
local instance Data.ActiveHeckeThetaData.referenceInverseProjectiveSmooth : Smooth X.toOver.hom := X.presentation.smooth

theorem Data.ActiveHeckeThetaData.referenceQuotientHomeomorph_inverse_derivative (y : D.ArithmeticBallQuotient) :
    letI := D.arithmeticBallAtlas hg hc hgood hdegree
    MDifferentiableAt (𝓘(ℂ, LinearTheta.BallCoordinates)) (𝓘(ℂ, X.analyticModel))
      (D.referenceQuotientHomeomorph hg X f href hc hgood hdegree hs hdim).symm y ∧
      Function.Bijective (mfderiv (𝓘(ℂ, LinearTheta.BallCoordinates)) (𝓘(ℂ, X.analyticModel))
        (D.referenceQuotientHomeomorph hg X f href hc hgood hdegree hs hdim).symm y) := by
  let := D.arithmeticBallAtlas hg hc hgood hdegree
  let H := D.referenceQuotientHomeomorph hg X f href hc hgood hdegree hs hdim
  let x := H.symm y
  obtain ⟨e, hx, hed, he⟩ := D.referenceQuotientCoordinates_local_charts hg f href hc hgood hdegree hs hdim x
  change e.MDifferentiable (𝓘(ℂ, X.analyticModel)) (𝓘(ℂ, LinearTheta.BallCoordinates)) at hed
  have hex : e x = y := (he hx).symm.trans (H.apply_symm_apply y)
  have hye : y ∈ e.target := hex ▸ e.map_source hx
  have hevent : (H.symm : D.ArithmeticBallQuotient → X.analyticSpace) =ᶠ[𝓝 y] e.symm := by
    filter_upwards [e.open_target.mem_nhds hye] with z hz
    apply H.injective
    rw [H.apply_symm_apply]
    exact ((he (e.map_target hz)).trans (e.right_inv hz)).symm
  refine ⟨hevent.mdifferentiableAt_iff.mpr (hed.mdifferentiableAt_symm hye), ?_⟩
  rw [hevent.mfderiv_eq]
  exact hed.symm.mfderiv_bijective hye

end

section

/-! The original reference ball covers the actual projective moduli
surface holomorphically, with the exact original finite arithmetic orbits. -/

set_option backward.isDefEq.respectTransparency false
open _root_.CategoryTheory _root_.AlgebraicGeometry Set
open scoped Classical _root_.Manifold

variable {E K : Type} [Field E] [NumberField E] [NumberField.IsCMField E] [IsGalois ℚ E]
    [Field K] [NumberField K] {s q : ℕ} [Fact q.Prime]
    {Index Ga MpR MpF MpA : Type} [Fintype Index] [DecidableEq Index]
    [Group Ga] [TopologicalSpace Ga] [Group MpR] [Group MpF] [Group MpA]
    (D : Data.ActiveHeckeThetaData E K s q Index Ga MpR MpF MpA)
    (hg : D.pel.HasIntegralModelGeometry) (X : AlgebraicGeometry.Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety)
    (f : X.toOver ⟶ D.pel.complexSpace) [Mono f]
    (href : ∀ x : X.analyticSpace, ∃ a : D.domain, x ≫ f = D.referenceModuliMap hg a)
    (hc : D.HasFiniteCoordinates) (hgood : D.pel.IsGoodCompletelySplitPrime)
    (hdegree : Module.finrank ℚ E = 2 * s) (hs : 0 < s) (hdim : X.complexDimension = 2)

def Data.ActiveHeckeThetaData.nativeReferenceCover : D.domain → X.analyticSpace :=
  (D.referenceQuotientHomeomorph hg X f href hc hgood hdegree hs hdim).symm ∘ D.arithmeticBallProjection

theorem Data.ActiveHeckeThetaData.nativeReferenceCover_moduli (a : D.domain) :
    D.nativeReferenceCover hg X f href hc hgood hdegree hs hdim a ≫ f = D.referenceModuliMap hg a :=
  D.referenceQuotientHomeomorph_inverse_moduli hg X f href hc hgood hdegree hs hdim a

theorem Data.ActiveHeckeThetaData.nativeReferenceCover_uniformization :
    D.IsPeriodUniformization X (D.nativeReferenceCover hg X f href hc hgood hdegree hs hdim) := by
  let := D.arithmeticBallAtlas hg hc hgood hdegree
  let H := D.referenceQuotientHomeomorph hg X f href hc hgood hdegree hs hdim
  have hH (z : D.ArithmeticBallQuotient) :=
    D.referenceQuotientHomeomorph_inverse_derivative hg X f href hc hgood hdegree hs hdim z
  have hP (a : D.domain) := D.arithmeticBallProjection_derivative hg hc hgood hdegree a
  refine ⟨H.symm.surjective.comp D.arithmeticBallProjection_surjective,
    (D.arithmeticBallProjection_covering hg hc hgood hdegree).homeomorph_comp H.symm,
    (fun a => (hH (D.arithmeticBallProjection a)).1.comp a (hP a).1), ?_, ?_⟩
  · intro a
    change Function.Bijective (mfderiv (𝓘(ℂ, LinearTheta.BallCoordinates)) (𝓘(ℂ, X.analyticModel))
      ((H.symm : D.ArithmeticBallQuotient → X.analyticSpace) ∘ D.arithmeticBallProjection) a)
    rw [mfderiv_comp a (hH (D.arithmeticBallProjection a)).1 (hP a).1]
    exact (hH (D.arithmeticBallProjection a)).2.comp (hP a).2
  · intro a b
    change H.symm (D.arithmeticBallProjection a) = H.symm (D.arithmeticBallProjection b) ↔ _
    exact H.symm.injective.eq_iff.trans
      ((D.arithmeticModuliMap_injective hg hc hgood hdegree).eq_iff.symm.trans
        (D.referenceModuliMap_orbits hg hc hgood hdegree a b))

end

/-! The original GeometricTheta hypotheses construct an actual original projective
surface component and its full reference-ball period uniformization. -/

set_option backward.isDefEq.respectTransparency false
open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped Classical _root_.Manifold

variable {E K : Type} [Field E] [NumberField E] [NumberField.IsCMField E] [IsGalois ℚ E]
    [Field K] [NumberField K] {s q : ℕ} [Fact q.Prime]
    {Index Ga MpR MpF MpA : Type} [Fintype Index] [DecidableEq Index]
    [Group Ga] [TopologicalSpace Ga] [Group MpR] [Group MpF] [Group MpA]
    (D : Data.ActiveHeckeThetaData E K s q Index Ga MpR MpF MpA)

theorem Data.ActiveHeckeThetaData.exists_original_period_uniformization (hg : D.pel.HasIntegralModelGeometry)
    (hc : D.HasFiniteCoordinates) (hgood : D.pel.IsGoodCompletelySplitPrime)
    (hs : 0 < s) (hdegree : Module.finrank ℚ E = 2 * s) :
    ∃ (j : Fin D.pel.componentCount) (X : AlgebraicGeometry.Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety)
      (component : X.toOver ≅ D.componentComplex j) (cover : D.domain → X.analyticSpace),
      X.complexDimension = 2 ∧ D.IsPeriodUniformization X cover ∧
      ∀ a : D.domain, D.totalPeriodMap j X component cover a = D.referenceModuliMap hg a := by
  obtain ⟨j, hj, href⟩ := D.exists_full_reference_surface_component hg hs hdegree
  let X := D.componentVariety hg j
  let f : X.toOver ⟶ D.pel.complexSpace := D.componentComplexInclusion j
  let : IsOpenImmersion f.left := D.componentComplexInclusion_open hg j
  let : Mono f := Over.mono_of_mono_left f
  let c := D.nativeReferenceCover hg X f href hc hgood hdegree hs hj
  refine ⟨j, X, D.componentVarietyIso hg j, c, hj,
    D.nativeReferenceCover_uniformization hg X f href hc hgood hdegree hs hj, ?_⟩
  intro a
  have h := D.nativeReferenceCover_moduli hg X f href hc hgood hdegree hs hj a
  change c a ≫ (D.componentVarietyIso hg j).hom ≫ D.componentComplexInclusion j = D.referenceModuliMap hg a
  have hi : (D.componentVarietyIso hg j).hom ≫ D.componentComplexInclusion j = f :=
    Category.id_comp f
  exact (congrArg (fun k : X.toOver ⟶ D.pel.complexSpace => c a ≫ k) hi).trans h

end

end OAI.RepresentationTheory.Theta.Geometric
