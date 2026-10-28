import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Real.BallLocalRecovery
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Real.BallPELHeckeQuotients
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Real.BallPELOrigin
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Reference.PointTopology

/-! # Ball Smoothness -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Real.BallSmoothness.FinePELModel

noncomputable section

/-! Every full-ball family attached to an original PEL object is locally
the inverse of a native period chart on the actual fine moduli scheme.
A smooth surface patch is obtained from its marked kernels, and actual
finite étale Hecke correspondences carry that patch through the ball. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
open scoped Classical BigOperators _root_.Manifold

attribute [local implicit_reducible] Models.FinePELModel.complexFiber
attribute [local irreducible] Intrinsic.BallCoordinateData.NativeBallCoordinateData.fiberAt
  Intrinsic.BallCoordinateData.NativeBallCoordinateData.pointTransport PEL.RealPeriodChanges.IntrinsicPELRealChanges.changeMap
  ChangedPELModel.RealChangedPEL.action ChangedPELModel.RealChangedPEL.fullLevel

variable {E K : Type} [Field E] [NumberField E] [NumberField.IsCMField E]
    [Field K] {s N : ℕ} {P : Datum.RankThreePELDatum E s} {iota : E →+* K}
    (M : Models.FinePELModel P iota N) (hM : M.IsFine) (κ : K →+* ℂ)

local instance [LocallyOfFiniteType M.space.hom] :
    LocallyOfFinitePresentation (M.complexFiber κ).hom :=
  inferInstanceAs (LocallyOfFinitePresentation
    (pullback.snd M.space.hom (Spec.map (CommRingCat.ofHom κ))))

theorem _root_.OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Models.FinePELModel.objectPoint_classifyingMap
    (B : PEL.Objects.PELObject P iota N (Over.mk (Spec.map (CommRingCat.ofHom κ)))) :
    AbelianScheme.IsogenyQuotient.FinePELTarget.Construction.finePELClassifyingMap M hM B = M.complexPointBaseEquiv κ (M.objectPoint hM κ B) := by
  apply (AbelianScheme.IsogenyQuotient.FinePELTarget.Construction.finePELClassifyingMap_unique M hM B _ ?_).symm
  exact (Models.PELPullbackIso.nonempty_iff_classOf _).mpr (M.objectPoint_class hM κ B).symm

theorem _root_.OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Models.FinePELModel.objectPoint_universal (x : M.ComplexPoints κ) :
    M.objectPoint hM κ (M.universal.pullback (M.complexPointBaseEquiv κ x)) = x :=
  (M.complexPointClassEquiv κ hM).symm_apply_apply x

section Hecke

variable [NumberField K] [LocallyOfFiniteType M.space.hom]
    (hN : 3 ≤ N) {n : ℕ} (hn : 0 < n) (hcop : Nat.Coprime n N)
    (hmod : Nat.ModEq N n 1)
    (hdegree : Nat.Coprime n ((∏ i, P.polarizationType i) ^ 2))
    {B C : PEL.Objects.PELObject P iota N (Over.mk (Spec.map (CommRingCat.ofHom κ)))}
    (f : Paired.PELQuotients.PairedPELQuotient B C n)

include hN hn hcop hmod hdegree f

theorem _root_.OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Models.FinePELModel.objectPoint_pairedQuotient_mem_smoothLocus_iff :
    AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.underlying (M.objectPoint hM κ B) ∈
        (M.complexFiber κ).hom.smoothLocus ↔
      AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.underlying (M.objectPoint hM κ C) ∈
        (M.complexFiber κ).hom.smoothLocus := by
  have : IsLocallyNoetherian M.space.left :=
    LocallyOfFiniteType.isLocallyNoetherian M.space.hom
  simpa only [M.objectPoint_classifyingMap hM κ, Equiv.symm_apply_apply] using
    HeckeSmoothLocus.geometric_pair_complexPoints_mem_smoothLocus_iff M hM κ hN hn hcop hmod hdegree f

theorem _root_.OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Models.FinePELModel.objectPoint_pairedQuotient_openPiece_dimension
    (R S : CycleClass.Geometric.IntegralSmoothStratification.IntegralSmoothGeometricPiece (M.complexFiber κ).hom)
    [IsOpenImmersion R.inclusion] [IsOpenImmersion S.inclusion]
    (hBR : AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.underlying (M.objectPoint hM κ B) ∈ R.support)
    (hCS : AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.underlying (M.objectPoint hM κ C) ∈ S.support) :
    R.complexDimension = S.complexDimension := by
  have : IsLocallyNoetherian M.space.left := LocallyOfFiniteType.isLocallyNoetherian M.space.hom
  obtain ⟨H, _, het, u, _, hsource, htarget⟩ :=
    Geometric.PairedHeckeRealization.geometric_pair_realized_by_finite_etale_hecke M hM hN hn hcop hmod hdegree f
  have : Etale (AbelianScheme.IsogenyQuotient.TotalParameters.Construction.totalParameterSource M.space H.parameter).left := H.etale
  have : Etale (H.targetProjection M hM).left := het
  let b := Spec.map (CommRingCat.ofHom κ)
  let U := (Over.pullback b).obj (AbelianScheme.IsogenyQuotient.TotalParameters.Construction.totalParameter M.space H.parameter)
  let p : U ⟶ M.complexFiber κ := (Over.pullback b).map (AbelianScheme.IsogenyQuotient.TotalParameters.Construction.totalParameterSource M.space H.parameter)
  let q : U ⟶ M.complexFiber κ := (Over.pullback b).map (H.targetProjection M hM)
  have : Etale p.left := MorphismProperty.of_isPullback
    (OverPullbackCartesianMap.overPullback_map_isPullback b (AbelianScheme.IsogenyQuotient.TotalParameters.Construction.totalParameterSource M.space H.parameter)).flip inferInstance
  have : Etale q.left := MorphismProperty.of_isPullback
    (OverPullbackCartesianMap.overPullback_map_isPullback b (H.targetProjection M hM)).flip inferInstance
  let v : AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints U := EtaleSmooth.EtaleSmoothLocus.baseChangePoint b u
  have hvp : v ≫ p = M.objectPoint hM κ B := by
    dsimp only [v, p]
    rw [← EtaleSmooth.EtaleSmoothLocus.baseChangePoint_comp, hsource]
    change (M.complexPointBaseEquiv κ).symm _ = _
    rw [M.objectPoint_classifyingMap hM κ, Equiv.symm_apply_apply]
  have hvq : v ≫ q = M.objectPoint hM κ C := by
    dsimp only [v, q]
    rw [← EtaleSmooth.EtaleSmoothLocus.baseChangePoint_comp, htarget]
    change (M.complexPointBaseEquiv κ).symm _ = _
    rw [M.objectPoint_classifyingMap hM κ, Equiv.symm_apply_apply]
  apply Reference.PointTopology.openPiece_dimension_eq_of_etale_span p q R S (AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.underlying v)
  · change AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.underlying (v ≫ p) ∈ R.support
    rwa [hvp]
  · change AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.underlying (v ≫ q) ∈ S.support
    rwa [hvq]

end Hecke

variable [NeZero N] [IsGalois ℚ E]
    {A : PEL.Objects.PELObject P iota N (Over.mk (Spec.map (CommRingCat.ofHom κ)))}
    {hs : 0 < s} {hdegree : Module.finrank ℚ E = 2 * s}
    (D : Intrinsic.BallCoordinateData.NativeBallCoordinateData A hs hdegree) (hP : P.IsAdmissible)
    (hκ : κ.comp iota = P.μ)

include hκ

theorem _root_.OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Models.FinePELModel.realBallPoint_origin :
    M.realBallPoint hM κ D hP D.point = M.objectPoint hM κ A := by
  change (M.complexPointClassEquiv κ hM).symm _ = (M.complexPointClassEquiv κ hM).symm _
  apply congrArg (M.complexPointClassEquiv κ hM).symm
  exact (PEL.Objects.PELObject.classOf_eq_iff _ _).mpr ⟨(BallPELOrigin.RealBallPELHecke.originIso A hs hdegree D hP hκ).symm⟩

theorem _root_.OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Models.FinePELModel.objectPoint_mem_realBallImage :
    M.objectPoint hM κ A ∈ Set.range (M.realBallPoint hM κ D hP) :=
  ⟨D.point, M.realBallPoint_origin hM κ D hP hκ⟩

variable [LocallyOfFiniteType M.space.hom] [QuasiCompact M.space.hom]

theorem _root_.OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Models.FinePELModel.exists_realBall_surface_stratum :
    ∃ R : CycleClass.Geometric.IntegralSmoothStratification.IntegralSmoothGeometricPiece (M.complexFiber κ).hom,
      R.complexDimension = 2 ∧ ∃ (a : P.domain) (x : R.analyticSpace),
        x ≫ Intrinsic.SmoothStrata.smoothPieceInclusion (M.complexFiber κ) R = M.realBallPoint hM κ D hP a := by
  exact M.exists_marked_family_surface_stratum hM κ hP hκ hs hdegree (NeZero.pos N)
    P.domain P.domain_isOpen ⟨D.point.val, D.point.property⟩
    (fun z => (D.fiberAt hP z).object) (fun z => (D.fiberAt hP z).model.model.abelian)
    (fun z => (D.fiberAt hP z).nativeIso) (fun _ => inferInstance)
    (PeriodEmbeddingChanges.fixedFirstComplexInclusion E (P.embeddings P.distinguished) D.normalizer)
    (fun z => (D.fiberAt hP z).marking.toLinearMap) (D.fiberAt_kernel hP)

theorem _root_.OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Models.FinePELModel.exists_realBall_surface_ball_patch :
    ∃ O : Set Geometry.ComplexBall.PrescribedSignsB.BallChart, IsOpen O ∧ O.Nonempty ∧ O ⊆ P.domain ∧
      ∀ z : P.domain, z.val ∈ O →
        ∃ R : CycleClass.Geometric.IntegralSmoothStratification.IntegralSmoothGeometricPiece (M.complexFiber κ).hom,
          IsOpenImmersion R.inclusion ∧ R.complexDimension = 2 ∧
          ∃ x : R.analyticSpace,
            x ≫ Intrinsic.SmoothStrata.smoothPieceInclusion (M.complexFiber κ) R = M.realBallPoint hM κ D hP z := by
  have : LocallyOfFiniteType (M.complexFiber κ).hom := M.complexFiber_locallyFiniteType κ
  obtain ⟨S, hS, a, x, hx⟩ := M.exists_realBall_surface_stratum hM κ D hP hκ
  let f := Intrinsic.SmoothStrata.smoothPieceInclusion (M.complexFiber κ) S
  have hdim : Betti.AffineDimension.Realization.functionFieldDifferentialDimension S.toOver.hom = 2 :=
    (Intrinsic.SmoothStrata.smoothPiece_dimension (M.complexFiber κ) S).trans hS
  obtain ⟨e, he, _, _, htarget, hmod⟩ :=
    M.exists_native_realBall_moduli_chart hM κ D hP f a x hx hκ hdim
  refine ⟨e.target, e.open_target, ⟨e x, e.map_source he⟩, htarget, ?_⟩
  intro z hz
  let y := e.symm z.val
  have hy : y ∈ e.source := e.map_target hz
  obtain ⟨hp, hpoint⟩ := hmod y hy
  have hz' : (⟨e y, hp⟩ : P.domain) = z := Subtype.ext (e.right_inv hz)
  rw [hz'] at hpoint
  have hb : Function.Bijective (f.left.stalkMap (AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.underlying y)).hom := by
    rw [show AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.underlying y = y.left (IsLocalRing.closedPoint ℂ) from
      congrArg y.left (Subsingleton.elim AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.basePoint (IsLocalRing.closedPoint ℂ))]
    exact (M.complexPoint_surface_stalk_data hP hM κ hκ f y hdim).1
  obtain ⟨R, hopen, hmem, hd⟩ := Reference.PointTopology.exists_open_piece_of_bijective_stalk f y hb
  have : IsOpenImmersion R.inclusion := hopen
  have : IsOpenImmersion (Intrinsic.SmoothStrata.smoothPieceInclusion (M.complexFiber κ) R).left := hopen
  have hrange : M.realBallPoint hM κ D hP z ∈
      Set.range (AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map (Intrinsic.SmoothStrata.smoothPieceInclusion (M.complexFiber κ) R)) := by
    rw [AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.range_map_of_isOpenImmersion]
    rwa [hpoint] at hmem
  exact ⟨R, hopen, hd.trans hdim, hrange⟩

variable [NumberField K]

theorem _root_.OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Models.FinePELModel.realBall_pairedQuotient_in_ball_patch
    (C : ℕ) (hC : 0 < C) (z : P.domain)
    (O : Set Geometry.ComplexBall.PrescribedSignsB.BallChart) (hO : IsOpen O) (hOn : O.Nonempty) (hdom : O ⊆ P.domain) :
    ∃ (w : P.domain) (n : ℕ), w.val ∈ O ∧ 0 < n ∧ Nat.Coprime n N ∧
      Nat.Coprime n C ∧ Nat.ModEq N n 1 ∧
      Nonempty (Paired.PELQuotients.PairedPELQuotient (D.fiberAt hP z).object (D.fiberAt hP w).object n) := by
  obtain ⟨v, hv⟩ := hOn
  let w₀ : P.domain := ⟨v, hdom hv⟩
  let H := Intrinsic.HermitianMarking.IntrinsicHermitianMarking.markedHermitianMatrix A.polarized A.action s hs rfl hdegree A.rosati P.normalizedImaginaryScalar
  let Λ := Intrinsic.PELMarking.IntrinsicPELMarking.markedLattice A.polarized.abelian (Polarized.Projectivity.polarizedNativeProjectivePresentation A.polarized)
    A.action s hs rfl hdegree
  obtain ⟨hξ, hc, _⟩ := Datum.RankThreePELDatum.normalizedImaginaryScalar_spec hP
  have hHerm : ∀ i j, H i j = NumberField.IsCMField.complexConj E (H j i) :=
    Intrinsic.HermitianMarking.IntrinsicHermitianMarking.markedHermitianMatrix_symmetry A.polarized A.action s hs rfl hdegree A.rosati
      P.normalizedImaginaryScalar hc
  have hdet : H.det ≠ 0 := Intrinsic.HermitianNondegenerate.IntrinsicHermitianMarking.markedHermitianMatrix_det_ne_zero A.polarized A.action
    s hs rfl hdegree A.rosati P.normalizedImaginaryScalar hξ
  have hΛ : NumberTheory.ArithmeticGroups.Data.CongruenceLevel.FullStableLattice Λ := Intrinsic.PELMarking.IntrinsicPELMarking.markedLattice_full_stable A.polarized.abelian
    (Polarized.Projectivity.polarizedNativeProjectivePresentation A.polarized) A.action s hs rfl hdegree
  obtain ⟨g, d, m, m', hg, _, hhit, hd, hcopN, hcopC, hmod, hm, hm', _, _, hcongr, _⟩ :=
    PrimeBallLatticeIsogenies.exists_original_ball_paired_lattice_maps P hP H hHerm hdet Λ hΛ D.normalizer D.hermitian
      N C (NeZero.pos N) hC z w₀ O hO hv
  let w : P.domain := ⟨P.lineActionVia D.normalizer g z.val, hdom hhit⟩
  refine ⟨w, d ^ 2, hhit, pow_pos hd 2, hcopN, hcopC, hmod, ?_⟩
  exact BallPELHeckeQuotients.RealBallPELHecke.exists_paired_quotient A hs hdegree D hP hκ z w g hg rfl
    d hd hmod m m' hm hm' hcongr

/-- The neighborhood is open in the original scheme, including all of
its local scheme structure. -/
theorem _root_.OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Models.FinePELModel.exists_realBall_open_surface (hN : 3 ≤ N) (z : P.domain) :
    ∃ R : CycleClass.Geometric.IntegralSmoothStratification.IntegralSmoothGeometricPiece (M.complexFiber κ).hom,
      IsOpenImmersion R.inclusion ∧ R.complexDimension = 2 ∧
      ∃ x : R.analyticSpace,
        x ≫ Intrinsic.SmoothStrata.smoothPieceInclusion (M.complexFiber κ) R = M.realBallPoint hM κ D hP z := by
  let X := M.complexFiber κ
  have : LocallyOfFiniteType X.hom := M.complexFiber_locallyFiniteType κ
  have : IsLocallyNoetherian X.left := LocallyOfFiniteType.isLocallyNoetherian X.hom
  have : CompactSpace X.left := inferInstanceAs
    (CompactSpace (pullback M.space.hom (Spec.map (CommRingCat.ofHom κ)) : Scheme))
  have : IsNoetherian X.left := ⟨⟩
  obtain ⟨O, hO, hOn, hdom, hsurface⟩ := M.exists_realBall_surface_ball_patch hM κ D hP hκ
  have hC : 0 < (∏ i, P.polarizationType i) ^ 2 := by
    have hdata := hP
    rcases hdata with ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, hδ, _⟩
    exact pow_pos (Finset.prod_pos (fun i _ => hδ i)) 2
  obtain ⟨w, n, hw, hn, hcopN, hcopδ, hmod, ⟨f⟩⟩ :=
    Models.FinePELModel.realBall_pairedQuotient_in_ball_patch κ D hP hκ ((∏ i, P.polarizationType i) ^ 2)
      hC z O hO hOn hdom
  obtain ⟨S, hS, hdimS, y, hy⟩ := hsurface w hw
  have : IsOpenImmersion S.inclusion := hS
  have hsmw : AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.underlying (M.realBallPoint hM κ D hP w) ∈ X.hom.smoothLocus := by
    have h := M.complexPoint_mem_smoothLocus_of_surface hP hM κ hκ
      (Intrinsic.SmoothStrata.smoothPieceInclusion X S) y hdimS
    rw [hy] at h
    simpa only [AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.underlying,
      Subsingleton.elim AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.basePoint (IsLocalRing.closedPoint ℂ)] using h
  have hsmz : AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.underlying (M.realBallPoint hM κ D hP z) ∈ X.hom.smoothLocus :=
    (M.objectPoint_pairedQuotient_mem_smoothLocus_iff hM κ hN hn hcopN hmod hcopδ f).mpr hsmw
  obtain ⟨R, hR, hzR⟩ := Reference.PointTopology.exists_integral_smooth_open_piece_at X _ hsmz
  have : IsOpenImmersion R.inclusion := hR
  have hwS : AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.underlying (M.realBallPoint hM κ D hP w) ∈ S.support := by
    rw [← hy]
    exact ⟨AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.underlying y, rfl⟩
  have hdimR : R.complexDimension = 2 :=
    (M.objectPoint_pairedQuotient_openPiece_dimension hM κ hN hn hcopN hmod hcopδ
      f R S hzR hwS).trans hdimS
  have : IsOpenImmersion (Intrinsic.SmoothStrata.smoothPieceInclusion X R).left := hR
  have hrange : M.realBallPoint hM κ D hP z ∈
      Set.range (AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map (Intrinsic.SmoothStrata.smoothPieceInclusion X R)) := by
    rw [AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.range_map_of_isOpenImmersion]
    exact hzR
  exact ⟨R, hR, hdimR, hrange⟩

theorem _root_.OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Models.FinePELModel.realBallPoint_mem_smoothLocus (hN : 3 ≤ N) (z : P.domain) :
    AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.underlying (M.realBallPoint hM κ D hP z) ∈
      (M.complexFiber κ).hom.smoothLocus := by
  obtain ⟨R, _, hd, x, hx⟩ := M.exists_realBall_open_surface hM κ D hP hκ hN z
  have h := M.complexPoint_mem_smoothLocus_of_surface hP hM κ hκ
    (Intrinsic.SmoothStrata.smoothPieceInclusion (M.complexFiber κ) R) x hd
  rw [hx] at h
  simpa only [AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.underlying,
    Subsingleton.elim AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.basePoint (IsLocalRing.closedPoint ℂ)] using h

theorem _root_.OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Models.FinePELModel.exists_native_realBall_open_chart (hN : 3 ≤ N) (z : P.domain) :
    ∃ R : CycleClass.Geometric.IntegralSmoothStratification.IntegralSmoothGeometricPiece (M.complexFiber κ).hom,
      IsOpenImmersion R.inclusion ∧ R.complexDimension = 2 ∧
      ∃ e : OpenPartialHomeomorph R.analyticSpace Geometry.ComplexBall.PrescribedSignsB.BallChart,
        z.val ∈ e.target ∧
        e.MDifferentiable (𝓘(ℂ, Fin (Betti.AffineDimension.Realization.functionFieldDifferentialDimension R.toOver.hom) → ℂ))
          (𝓘(ℂ, Geometry.ComplexBall.PrescribedSignsB.BallChart)) ∧ e.target ⊆ P.domain ∧
        ∀ y ∈ e.source, ∃ hp : e y ∈ P.domain,
          y ≫ Intrinsic.SmoothStrata.smoothPieceInclusion (M.complexFiber κ) R = M.realBallPoint hM κ D hP ⟨e y, hp⟩ := by
  obtain ⟨R, hopen, hdim, x, hx⟩ := M.exists_realBall_open_surface hM κ D hP hκ hN z
  obtain ⟨e, he, hez, hhol, htarget, hmod⟩ := M.exists_native_realBall_moduli_chart
    hM κ D hP (Intrinsic.SmoothStrata.smoothPieceInclusion (M.complexFiber κ) R) z x hx hκ hdim
  refine ⟨R, hopen, hdim, e, ?_, hhol, htarget, hmod⟩
  rw [← hez]
  exact e.map_source he

theorem _root_.OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Models.FinePELModel.realBallPoint_isLocalHomeomorph (hN : 3 ≤ N) :
    IsLocalHomeomorph (M.realBallPoint hM κ D hP) := by
  apply Reference.PointTopology.isLocalHomeomorph_of_open_period_charts P.domain_isOpen
  intro z
  obtain ⟨R, hopen, _, e, hz, _, _, hmod⟩ :=
    M.exists_native_realBall_open_chart hM κ D hP hκ hN z
  exact ⟨R, hopen, e, hz, hmod⟩

theorem _root_.OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Models.FinePELModel.realBallPoint_continuous (hN : 3 ≤ N) :
    Continuous (M.realBallPoint hM κ D hP) :=
  (M.realBallPoint_isLocalHomeomorph hM κ D hP hκ hN).continuous

theorem _root_.OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Models.FinePELModel.realBallPoint_isOpenMap (hN : 3 ≤ N) :
    IsOpenMap (M.realBallPoint hM κ D hP) :=
  (M.realBallPoint_isLocalHomeomorph hM κ D hP hκ hN).isOpenMap

theorem _root_.OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Models.FinePELModel.realBallImage_open_connected_smooth (hN : 3 ≤ N) :
    IsOpen (Set.range (M.realBallPoint hM κ D hP)) ∧
      IsConnected (Set.range (M.realBallPoint hM κ D hP)) ∧
      Set.range (M.realBallPoint hM κ D hP) ⊆
        AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.underlying ⁻¹' (M.complexFiber κ).hom.smoothLocus := by
  have : ConnectedSpace P.domain := P.domain_connected hP
  refine ⟨(M.realBallPoint_isOpenMap hM κ D hP hκ hN).isOpen_range,
    isConnected_range (M.realBallPoint_continuous hM κ D hP hκ hN), ?_⟩
  rintro _ ⟨z, rfl⟩
  exact M.realBallPoint_mem_smoothLocus hM κ D hP hκ hN z

include hP hM in
theorem _root_.OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Models.FinePELModel.complexPoint_exists_open_surface (hN : 3 ≤ N)
    (hpos : 0 < s) (hdeg : Module.finrank ℚ E = 2 * s) (x : M.ComplexPoints κ) :
    ∃ R : CycleClass.Geometric.IntegralSmoothStratification.IntegralSmoothGeometricPiece (M.complexFiber κ).hom,
      IsOpenImmersion R.inclusion ∧ R.complexDimension = 2 ∧
      ∃ y : R.analyticSpace, y ≫ Intrinsic.SmoothStrata.smoothPieceInclusion (M.complexFiber κ) R = x := by
  let B := M.universal.pullback (M.complexPointBaseEquiv κ x)
  let D₀ := Intrinsic.BallCoordinateData.nativeBallCoordinateData B hpos hdeg hP hκ
  obtain ⟨R, hopen, hdim, y, hy⟩ := M.exists_realBall_open_surface hM κ D₀ hP hκ hN D₀.point
  refine ⟨R, hopen, hdim, y, ?_⟩
  rw [M.realBallPoint_origin hM κ D₀ hP hκ] at hy
  exact hy.trans (M.objectPoint_universal hM κ x)

include hP hM in
theorem _root_.OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Models.FinePELModel.complexPoint_mem_smoothLocus (hN : 3 ≤ N)
    (hpos : 0 < s) (hdeg : Module.finrank ℚ E = 2 * s) (x : M.ComplexPoints κ) :
    AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.underlying x ∈ (M.complexFiber κ).hom.smoothLocus := by
  obtain ⟨R, _, hd, y, hy⟩ := M.complexPoint_exists_open_surface hM κ hP hκ hN hpos hdeg x
  have h := M.complexPoint_mem_smoothLocus_of_surface hP hM κ hκ
    (Intrinsic.SmoothStrata.smoothPieceInclusion (M.complexFiber κ) R) y hd
  rw [hy] at h
  simpa only [AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.underlying,
    Subsingleton.elim AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.basePoint (IsLocalRing.closedPoint ℂ)] using h

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Real.BallSmoothness.FinePELModel
