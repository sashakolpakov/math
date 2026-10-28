import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Reference.PointTopology
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.QuasiProjectiveComponents
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Principal.BallCovering
import Mathlib.Analysis.Complex.Basic
import Mathlib.Geometry.Manifold.MFDeriv.Atlas
import Mathlib.Topology.Connected.Clopen

/-! # Projective Component -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily

noncomputable section

/-! The original reference quotient supplies the actual principal
projective component and its holomorphic ball covering. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace
open scoped _root_.Manifold _root_.Topology

/-- A map locally given by the inverse of a holomorphic chart has a
bijective complex derivative in the original manifold structures. -/
theorem Principal.ProjectiveComponent.localInverseChart_derivative
    {V W T : Type} [NormedAddCommGroup V] [NormedSpace ℂ V]
    [NormedAddCommGroup W] [NormedSpace ℂ W]
    [TopologicalSpace T] [ChartedSpace W T] [IsManifold (𝓘(ℂ, W)) 1 T]
    (D : Opens V) (q : D → T) (z : D)
    (e : OpenPartialHomeomorph T V)
    (he : q z ∈ e.source) (hez : e (q z) = z.val)
    (hhol : e.MDifferentiable (𝓘(ℂ, W)) (𝓘(ℂ, V)))
    (hrec : ∀ w : D, w.val ∈ e.target → q w = e.symm w.val) :
    MDifferentiableAt (𝓘(ℂ, V)) (𝓘(ℂ, W)) q z ∧
      Function.Bijective (mfderiv (𝓘(ℂ, V)) (𝓘(ℂ, W)) q z) := by
  have hz : z.val ∈ e.target := by
    rw [← hez]
    exact e.map_source he
  have hc := mdifferentiable_of_mem_atlas (I := 𝓘(ℂ, V)) (chart_mem_atlas V z)
  have hi : MDifferentiableAt (𝓘(ℂ, V)) (𝓘(ℂ, V)) (fun w : D => w.val) z :=
    hc.mdifferentiableAt (mem_chart_source V z)
  have hbi : Function.Bijective (mfderiv (𝓘(ℂ, V)) (𝓘(ℂ, V)) (fun w : D => w.val) z) :=
    hc.mfderiv_bijective (mem_chart_source V z)
  have hinv := hhol.mdifferentiableAt_symm hz
  have hEq : q =ᶠ[𝓝 z] (fun w : D => e.symm w.val) := by
    filter_upwards [(e.open_target.preimage continuous_subtype_val).mem_nhds hz] with w hw
    exact hrec w hw
  refine ⟨(hinv.comp z hi).congr_of_eventuallyEq hEq, ?_⟩
  have hd : (mfderiv (𝓘(ℂ, V)) (𝓘(ℂ, W)) q z : V →L[ℂ] W) =
      mfderiv (𝓘(ℂ, V)) (𝓘(ℂ, W)) (e.symm ∘ (fun w : D => w.val)) z := hEq.mfderiv_eq
  rw [hd, mfderiv_comp z hinv hi]
  exact (hhol.symm.mfderiv_bijective hz).comp hbi

/-- A nonempty connected clopen set is precisely the connected component
of any of its points. -/
theorem Principal.ProjectiveComponent.clopen_connected_eq_component_fiber
    {X : Type} [TopologicalSpace X] (S : Set X) (hc : IsClopen S)
    (hS : IsConnected S) (x : X) (hx : x ∈ S) :
    S = {y | ConnectedComponents.mk y = ConnectedComponents.mk x} := by
  have heq : S = connectedComponent x :=
    Set.Subset.antisymm (hS.isPreconnected.subset_connectedComponent hx)
      (hc.connectedComponent_subset hx)
  ext y
  rw [heq]
  exact ConnectedComponents.coe_eq_coe'.symm

theorem Principal.ProjectiveComponent.exists_homeomorph_of_equal_embedding_ranges
    {A B T : Type} [TopologicalSpace A] [TopologicalSpace B] [TopologicalSpace T]
    (u : A → T) (v : B → T) (hu : Topology.IsEmbedding u) (hv : Topology.IsEmbedding v)
    (hrange : Set.range u = Set.range v) :
    ∃ e : A ≃ₜ B, ∀ a, v (e a) = u a := by
  let O : A ≃ₜ Set.range u := hu.toHomeomorph
  let J : B ≃ₜ Set.range u := hv.toHomeomorph.trans (Homeomorph.setCongr hrange.symm)
  let e : A ≃ₜ B := O.trans J.symm
  refine ⟨e, ?_⟩
  intro a
  calc
    v (e a) = (J (J.symm (O a))).val := rfl
    _ = (O a).val := congrArg Subtype.val (J.apply_symm_apply _)
    _ = u a := rfl

attribute [local implicit_reducible] Models.FinePELModel.complexFiber

variable {E K : Type} [Field E] [NumberField E] [NumberField.IsCMField E]
    [IsGalois ℚ E] [Field K]
    {s N : ℕ} [NeZero N] {P : Datum.RankThreePELDatum E s} {iota : E →+* K}
    (M : Models.FinePELModel P iota N) (hM : M.IsFine) (κ : K →+* ℂ)
    (hP : P.IsAdmissible) (hκ : κ.comp iota = P.μ)

/-- Any lift of the literal reference map through a monomorphic smooth
surface has the native holomorphic derivative dictated by its period chart. -/
theorem Models.FinePELModel.reference_lift_derivative
    {S : Over Foundations.Scheme.ProjectiveSpace.complexBase} [IsIntegral S.left] [Smooth S.hom]
    (f : S ⟶ M.complexFiber κ) [Mono f]
    (hdim : Betti.AffineDimension.Realization.functionFieldDifferentialDimension S.hom = 2)
    (q : P.Domain → ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints S)
    (hq : ∀ z, q z ≫ f = M.referencePoint hM κ hP hκ z)
    (hs : 0 < s) (hdegree : Module.finrank ℚ E = 2 * s) (z : P.Domain) :
    MDifferentiableAt (𝓘(ℂ, OAI.Geometry.ComplexBall.PrescribedSignsB.BallChart))
        (𝓘(ℂ, Fin (Betti.AffineDimension.Realization.functionFieldDifferentialDimension S.hom) → ℂ)) q z ∧
      Function.Bijective (mfderiv (𝓘(ℂ, OAI.Geometry.ComplexBall.PrescribedSignsB.BallChart))
        (𝓘(ℂ, Fin (Betti.AffineDimension.Realization.functionFieldDifferentialDimension S.hom) → ℂ)) q z) := by
  obtain ⟨e, he, hez, hhol, _, hrec⟩ :=
    M.exists_native_reference_moduli_chart hM κ hP hκ f hs hdegree hdim (q z) z (hq z)
  apply Principal.ProjectiveComponent.localInverseChart_derivative P.domainOpen q z e he hez hhol
  intro w hw
  obtain ⟨hp, hpoint⟩ := hrec (e.symm w.val) (e.map_target hw)
  have heq : (⟨e (e.symm w.val), hp⟩ : P.domain) = w := Subtype.ext (e.right_inv hw)
  rw [heq] at hpoint
  exact (cancel_mono f).mp ((hq w).trans hpoint.symm)

variable [NumberField K] [LocallyOfFiniteType M.space.hom] [QuasiCompact M.space.hom]

/-- An actual open projective realization of the reference image has the
prescribed principal SU uniformization in its native analytic atlas. -/
theorem Models.FinePELModel.principal_uniformization_of_reference_image
    (hN : 3 ≤ N) (hs : 0 < s) (hdegree : Module.finrank ℚ E = 2 * s)
    (X : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety) (f : X.toOver ⟶ M.complexFiber κ)
    [IsOpenImmersion f.left] (hdim : X.complexDimension = 2)
    (hrange : Set.range (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map f) = Set.range (M.referencePoint hM κ hP hκ)) :
    P.IsUniformizedBy X (Groups.principalSpecialUnitary P.b P.lattice N) := by
  have : IsIntegral X.toOver.left := X.property
  have : Smooth X.toOver.hom := X.presentation.smooth
  have : Mono f := Over.mono_of_mono_left f
  obtain ⟨e, he⟩ := Principal.ProjectiveComponent.exists_homeomorph_of_equal_embedding_ranges
    (M.referenceOrbitMap hM κ hP hκ) (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map f)
    (M.referenceOrbitMap_isOpenEmbedding hM κ hP hκ hN hs hdegree).isEmbedding
    (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.isOpenEmbedding_map_of_isOpenImmersion f).isEmbedding
    ((M.referenceOrbitMap_range hM κ hP hκ).trans hrange.symm)
  let q : P.Domain → X.analyticSpace := e ∘ P.principalOrbitProjection N
  have hq (z : P.Domain) : q z ≫ f = M.referencePoint hM κ hP hκ z :=
    he (P.principalOrbitProjection N z)
  have hsurj : Function.Surjective q := e.surjective.comp (P.principalOrbitProjection_surjective N)
  have hcover : IsCoveringMap q :=
    (P.principalOrbitProjection_covering hP N hN).homeomorph_comp e
  have hderiv (z : P.Domain) :=
    M.reference_lift_derivative hM κ hP hκ f hdim q hq hs hdegree z
  refine ⟨q, ⟨hsurj, hcover, fun z => (hderiv z).1, fun z => (hderiv z).2⟩, ?_⟩
  intro z w
  change e (P.principalOrbitProjection N z) = e (P.principalOrbitProjection N w) ↔ _
  exact e.injective.eq_iff.trans (P.principalOrbitProjection_fibers N z w)

include hM hP hκ in
/-- The original reference locus is an actual open-and-closed projective
surface component, with precisely its original principal SU ball quotient. -/
theorem Models.FinePELModel.exists_principal_projective_component
    (Q : HilbertConstruction.Projective.ProjectivePresentations.QuasiProjectivePresentation (M.complexFiber κ))
    (hN : 3 ≤ N) (hs : 0 < s) (hdegree : Module.finrank ℚ E = 2 * s) :
    ∃ (C : M.ComplexComponent κ) (X : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety),
      M.IsProjectiveComponent κ C X ∧
        P.IsUniformizedBy X (Groups.principalSpecialUnitary P.b P.lattice N) := by
  have : LocallyOfFiniteType (M.complexFiber κ).hom := M.complexFiber_locallyFiniteType κ
  let Y := M.complexFiber κ
  let V := Set.range (M.referencePoint hM κ hP hκ)
  obtain ⟨hcompact, hopen, hconnected, hsmooth⟩ :=
    M.referenceImage_compact_open_connected_smooth hM κ hP hκ hN hs hdegree
  obtain ⟨R, hRo, hRc, ⟨Pj⟩, hrange⟩ :=
    QuasiProjectiveComponents.exists_projective_open_piece_of_compact_connected_analytic_open Q V hopen hcompact hconnected
      (fun _ hx => hsmooth hx)
  have : IsOpenImmersion R.inclusion := hRo
  have : IsClosedImmersion R.inclusion := hRc
  let X : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety := ⟨{
    carrier := R.carrier
    structureMap := R.inclusion ≫ Y.hom
    projective := Pj
    smooth := R.smooth }, R.integral⟩
  let f : X.toOver ⟶ Y := Over.homMk R.inclusion rfl
  have : IsOpenImmersion f.left := hRo
  have : IsClosedImmersion f.left := hRc
  have hfRange : Set.range (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map f) = V := hrange
  let a := P.referenceOrigin hP
  let x := M.referencePoint hM κ hP hκ a
  have hx : x ∈ V := ⟨a, rfl⟩
  have hxR : ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.underlying x ∈ R.support := by
    have hmem : x ∈ Set.range (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map f) := hfRange.symm ▸ hx
    rw [ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.range_map_of_isOpenImmersion f] at hmem
    exact hmem
  obtain ⟨S, hSo, hSdim, t, ht⟩ :=
    M.exists_reference_open_surface hM κ hP hκ hN hs hdegree a
  have : IsOpenImmersion S.inclusion := hSo
  have hxS : ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.underlying x ∈ S.support := by
    change ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.underlying (M.referencePoint hM κ hP hκ a) ∈ S.support
    rw [← ht]
    exact ⟨ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.underlying t, rfl⟩
  have : Etale ((𝟙 Y : Y ⟶ Y).left) := inferInstanceAs (Etale (𝟙 Y.left))
  have hdim : X.complexDimension = 2 :=
    (Reference.PointTopology.openPiece_dimension_eq_of_etale_span (𝟙 Y) (𝟙 Y) R S
      (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.underlying x) hxR hxS).trans hSdim
  have hclopen : IsClopen V := by
    refine ⟨?_, hopen⟩
    rw [← hfRange]
    exact (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.isClosedEmbedding_map_of_isClosedImmersion f).isClosed_range
  have hcomponent := Principal.ProjectiveComponent.clopen_connected_eq_component_fiber V hclopen hconnected x hx
  let C : M.ComplexComponent κ := ConnectedComponents.mk x
  refine ⟨C, X, ⟨hdim, f, hRo, hRc, hfRange.trans hcomponent⟩, ?_⟩
  exact M.principal_uniformization_of_reference_image hM κ hP hκ hN hs hdegree X f hdim hfRange

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily
