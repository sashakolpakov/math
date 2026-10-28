import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Reference.HeckeSmoothness
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Reference.OrbitFibers
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Principal.QuotientCompact
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.EtaleSmooth
import OAI.ArithmeticGeometry.OrdinaryLocus.Openness.SmoothRelativeDimension
import OAI.AlgebraicGeometry.Foundations.Scheme.SmoothProjectiveDecomposition
import OAI.AlgebraicGeometry.ComplexPoints.Analytic.CycleStratumRealization
import OAI.AlgebraicGeometry.Betti.SmoothDimension
import Mathlib.Topology.IsLocalHomeomorph
import Mathlib.Topology.OpenPartialHomeomorph.Constructions

/-! # Point Topology -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Reference.PointTopology

noncomputable section

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry _root_.TopologicalSpace
open scoped _root_.Manifold BigOperators

attribute [local implicit_reducible] Models.FinePELModel.complexFiber

/-- A smooth point of a noetherian complex scheme belongs to an actual
integral smooth open piece of that same scheme. -/
theorem exists_integral_smooth_open_piece_at
    (X : Over Foundations.Scheme.ProjectiveSpace.complexBase) [NoetherianSpace X.left] [LocallyOfFiniteType X.hom]
    (x : X.left) (hx : x ∈ X.hom.smoothLocus) :
    ∃ R : CycleClass.Geometric.IntegralSmoothStratification.IntegralSmoothGeometricPiece X.hom,
      IsOpenImmersion R.inclusion ∧ x ∈ R.support := by
  let U := X.hom.smoothLocus
  have : Smooth (U.ι ≫ X.hom) := EtaleSmooth.EtaleSmoothLocus.smooth_on_smoothLocus X.hom
  have : NoetherianSpace U.toScheme := U.ι.isOpenEmbedding.isInducing.noetherianSpace
  let y : U.toScheme := ⟨x, hx⟩
  let C := irreducibleComponent y
  have hC : C ∈ irreducibleComponents U.toScheme := irreducibleComponent_mem_irreducibleComponents y
  let V : U.toScheme.Opens := ⟨C, Foundations.Scheme.LocalDomainComponents.isOpen_irreducibleComponent_of_stalkDomains
    (Foundations.Scheme.SmoothProjectiveDecomposition.smoothScheme_stalk_isDomain (U.ι ≫ X.hom))
    NoetherianSpace.finite_irreducibleComponents hC⟩
  have : IrreducibleSpace V.toScheme := isIrreducible_iff_irreducibleSpace.mp hC.1
  have : IsReduced U.toScheme := Foundations.Scheme.SmoothProjectiveDecomposition.smoothScheme_isReduced (U.ι ≫ X.hom)
  have : IsIntegral V.toScheme := isIntegral_of_irreducibleSpace_of_isReduced _
  let R : CycleClass.Geometric.IntegralSmoothStratification.IntegralSmoothGeometricPiece X.hom := {
    carrier := V.toScheme
    inclusion := V.ι ≫ U.ι
    immersion := inferInstance
    smooth := by
      rw [Category.assoc]
      infer_instance
    integral := inferInstance }
  refine ⟨R, inferInstanceAs (IsOpenImmersion (V.ι ≫ U.ι)), ?_⟩
  exact ⟨⟨y, mem_irreducibleComponent⟩, rfl⟩

/-- The dimensions of two actual smooth open pieces agree when their
points are related by an étale span. -/
theorem openPiece_dimension_eq_of_etale_span
    {X U : Over Foundations.Scheme.ProjectiveSpace.complexBase} (p q : U ⟶ X) [Etale p.left] [Etale q.left]
    (R S : CycleClass.Geometric.IntegralSmoothStratification.IntegralSmoothGeometricPiece X.hom)
    [IsOpenImmersion R.inclusion] [IsOpenImmersion S.inclusion]
    (u : U.left) (hp : p.left u ∈ R.support) (hq : q.left u ∈ S.support) :
    R.complexDimension = S.complexDimension := by
  obtain ⟨r, hr⟩ := hp
  obtain ⟨s, hs⟩ := hq
  let V := pullback p.left R.inclusion
  let a : V ⟶ U.left := pullback.fst p.left R.inclusion
  let b : V ⟶ R.carrier := pullback.snd p.left R.inclusion
  let W := pullback (a ≫ q.left) S.inclusion
  let c : W ⟶ V := pullback.fst (a ≫ q.left) S.inclusion
  let d : W ⟶ S.carrier := pullback.snd (a ≫ q.left) S.inclusion
  obtain ⟨v, hv, _⟩ := Scheme.Pullback.exists_preimage_pullback
    (f := p.left) (g := R.inclusion) u r hr.symm
  have hvs : (a ≫ q.left) v = S.inclusion s := by
    change q.left (a v) = S.inclusion s
    rw [hv]
    exact hs.symm
  obtain ⟨w, _, _⟩ := Scheme.Pullback.exists_preimage_pullback
    (f := a ≫ q.left) (g := S.inclusion) v s hvs
  have : Nonempty W := ⟨w⟩
  have : SmoothOfRelativeDimension R.complexDimension (R.inclusion ≫ X.hom) :=
    Betti.SmoothDimension.Realization.smoothOfFunctionFieldDimension _
  have : SmoothOfRelativeDimension S.complexDimension (S.inclusion ≫ X.hom) :=
    Betti.SmoothDimension.Realization.smoothOfFunctionFieldDimension _
  let f : W ⟶ Foundations.Scheme.ProjectiveSpace.complexBase := c ≫ b ≫ R.inclusion ≫ X.hom
  have hf : f = d ≫ S.inclusion ≫ X.hom := by
    dsimp only [f, b, d]
    rw [← pullback.condition_assoc, p.w, ← q.w]
    change c ≫ a ≫ q.left ≫ X.hom = _
    rw [← Category.assoc a q.left X.hom]
    dsimp only [c]
    rw [pullback.condition_assoc]
  have : SmoothOfRelativeDimension R.complexDimension f := by
    dsimp only [f]
    simpa only [Nat.zero_add] using
      (inferInstance : SmoothOfRelativeDimension (0 + (0 + R.complexDimension))
        (c ≫ b ≫ R.inclusion ≫ X.hom))
  have : SmoothOfRelativeDimension S.complexDimension f := by
    rw [hf]
    simpa only [Nat.zero_add] using
      (inferInstance : SmoothOfRelativeDimension (0 + S.complexDimension)
        (d ≫ S.inclusion ≫ X.hom))
  have : Smooth f := SmoothOfRelativeDimension.smooth R.complexDimension f
  have : JacobsonSpace W := LocallyOfFiniteType.jacobsonSpace f
  obtain ⟨z, _, hz⟩ := nonempty_inter_closedPoints
    (X := W) Set.univ_nonempty isOpen_univ.isLocallyClosed
  have hR := ArithmeticGeometry.OrdinaryLocus.Openness.SmoothRelativeDimension.Construction.ringKrullDim_stalk_of_smoothOfRelativeDimension R.complexDimension f z hz
  have hS := ArithmeticGeometry.OrdinaryLocus.Openness.SmoothRelativeDimension.Construction.ringKrullDim_stalk_of_smoothOfRelativeDimension S.complexDimension f z hz
  exact_mod_cast hR.symm.trans hS

/-- Exact recovery in native charts of open subschemes makes the original
set-theoretic map a local homeomorphism. -/
theorem isLocalHomeomorph_of_open_period_charts
    {V : Type} [TopologicalSpace V] {D : Set V} (hD : IsOpen D)
    {X : Over Foundations.Scheme.ProjectiveSpace.complexBase} (f : D → ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X)
    (h : ∀ z : D, ∃ R : CycleClass.Geometric.IntegralSmoothStratification.IntegralSmoothGeometricPiece X.hom,
      IsOpenImmersion R.inclusion ∧
        ∃ e : OpenPartialHomeomorph R.analyticSpace V,
          z.val ∈ e.target ∧ ∀ y ∈ e.source, ∃ hy : e y ∈ D,
            ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map (Over.homMk R.inclusion rfl : R.toOver ⟶ X) y =
              f ⟨e y, hy⟩) :
    IsLocalHomeomorph f := by
  apply IsLocalHomeomorph.mk
  intro z
  obtain ⟨R, hopen, e, hz, hrec⟩ := h z
  have : IsOpenImmersion R.inclusion := hopen
  let j : R.toOver ⟶ X := Over.homMk R.inclusion rfl
  have : IsOpenImmersion j.left := hopen
  let J := (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.isOpenEmbedding_map_of_isOpenImmersion j).toOpenPartialHomeomorph
    (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map j)
  let D' : Opens V := ⟨D, hD⟩
  let e' : OpenPartialHomeomorph D R.analyticSpace :=
    e.symm.subtypeRestr (s := D') ⟨z⟩
  let E := e'.trans J
  refine ⟨E, ⟨?_, ?_⟩, ?_⟩
  · simpa only [e', OpenPartialHomeomorph.symm_target,
      OpenPartialHomeomorph.subtypeRestr_source, OpenPartialHomeomorph.symm_source,
      Set.mem_preimage] using hz
  · trivial
  · intro w hw
    have hwT : w.val ∈ e.target := by
      simpa only [e', OpenPartialHomeomorph.symm_target,
        OpenPartialHomeomorph.subtypeRestr_source, OpenPartialHomeomorph.symm_source,
        Set.mem_preimage] using hw.1
    obtain ⟨hy, hpoint⟩ := hrec (e.symm w.val) (e.map_target hwT)
    have heq : (⟨e (e.symm w.val), hy⟩ : D) = w := Subtype.ext (e.right_inv hwT)
    rw [heq] at hpoint
    exact hpoint.symm

/-- A bijective immersion stalk supplies an actual open integral piece
with the original smooth source dimension. -/
theorem exists_open_piece_of_bijective_stalk
    {S X : Over Foundations.Scheme.ProjectiveSpace.complexBase} [IsIntegral S.left] [Smooth S.hom]
    [LocallyOfFiniteType X.hom] (f : S ⟶ X) [IsImmersion f.left]
    (x : ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints S)
    (hb : Function.Bijective (f.left.stalkMap (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.underlying x)).hom) :
    ∃ R : CycleClass.Geometric.IntegralSmoothStratification.IntegralSmoothGeometricPiece X.hom,
      IsOpenImmersion R.inclusion ∧
      ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.underlying (x ≫ f) ∈ R.support ∧
      R.complexDimension = Betti.AffineDimension.Realization.functionFieldDifferentialDimension S.hom := by
  have : IsLocallyNoetherian X.left := LocallyOfFiniteType.isLocallyNoetherian X.hom
  obtain ⟨U, hx, g, hg, hgf, _⟩ :=
    PELStratumLocalRegularity.exists_open_section_of_stalkMap_bijective f.left (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.underlying x) hb
  have : IsOpenImmersion g := hg
  have : Nonempty U.toScheme := ⟨⟨_, hx⟩⟩
  have : IsIntegral U.toScheme := isIntegral_of_isOpenImmersion g
  have hstr : U.ι ≫ X.hom = g ≫ S.hom := by
    rw [← f.w, ← Category.assoc, hgf]
  have hsm : Smooth (U.ι ≫ X.hom) := by
    rw [hstr]
    infer_instance
  let R : CycleClass.Geometric.IntegralSmoothStratification.IntegralSmoothGeometricPiece X.hom := {
    carrier := U.toScheme
    inclusion := U.ι
    immersion := inferInstance
    smooth := hsm
    integral := inferInstance }
  refine ⟨R, inferInstanceAs (IsOpenImmersion U.ι), ⟨⟨_, hx⟩, rfl⟩, ?_⟩
  change Betti.AffineDimension.Realization.functionFieldDifferentialDimension (U.ι ≫ X.hom) = _
  rw [hstr, ← Foundations.Scheme.TranscendenceDimension.schemeTranscendenceDimension_eq_functionFieldDifferentialDimension (g ≫ S.hom),
    ← Foundations.Scheme.TranscendenceDimension.schemeTranscendenceDimension_eq_functionFieldDifferentialDimension S.hom]
  exact Foundations.Scheme.OpenFunctionField.schemeTranscendenceDimension_openImmersion g S.hom

namespace FinePELModel

variable {E K : Type} [Field E] [NumberField E] [NumberField.IsCMField E]
    [IsGalois ℚ E] [Field K] [NumberField K]
    {s N : ℕ} [NeZero N] {P : Datum.RankThreePELDatum E s} {iota : E →+* K}
    (M : Models.FinePELModel P iota N) (hM : M.IsFine) (κ : K →+* ℂ)
    (hP : P.IsAdmissible) (hκ : κ.comp iota = P.μ)
    [LocallyOfFiniteType M.space.hom]

local instance : LocallyOfFinitePresentation (M.complexFiber κ).hom :=
  inferInstanceAs (LocallyOfFinitePresentation
    (Limits.pullback.snd M.space.hom (Spec.map (CommRingCat.ofHom κ))))

omit [IsGalois ℚ E] in
theorem _root_.OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Models.FinePELModel.reference_pairedQuotient_openPiece_dimension
    (hN : 3 ≤ N) {n : ℕ} (hn : 0 < n) (hcop : Nat.Coprime n N)
    (hmod : Nat.ModEq N n 1)
    (hdegree : Nat.Coprime n ((∏ i, P.polarizationType i) ^ 2))
    (z w : P.domain)
    (f : Paired.PELQuotients.PairedPELQuotient (P.referencePELObject hP z iota κ hκ N)
      (P.referencePELObject hP w iota κ hκ N) n)
    (R S : CycleClass.Geometric.IntegralSmoothStratification.IntegralSmoothGeometricPiece (M.complexFiber κ).hom)
    [IsOpenImmersion R.inclusion] [IsOpenImmersion S.inclusion]
    (hzR : ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.underlying (M.referencePoint hM κ hP hκ z) ∈ R.support)
    (hwS : ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.underlying (M.referencePoint hM κ hP hκ w) ∈ S.support) :
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
  let v : ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints U := EtaleSmooth.EtaleSmoothLocus.baseChangePoint b u
  have hz : AbelianScheme.IsogenyQuotient.FinePELTarget.Construction.finePELClassifyingMap M hM (P.referencePELObject hP z iota κ hκ N) =
      M.complexPointBaseEquiv κ (M.referencePoint hM κ hP hκ z) :=
    (AbelianScheme.IsogenyQuotient.FinePELTarget.Construction.finePELClassifyingMap_unique M hM _ _ (M.referencePoint_recovery hM κ hP hκ z)).symm
  have hw : AbelianScheme.IsogenyQuotient.FinePELTarget.Construction.finePELClassifyingMap M hM (P.referencePELObject hP w iota κ hκ N) =
      M.complexPointBaseEquiv κ (M.referencePoint hM κ hP hκ w) :=
    (AbelianScheme.IsogenyQuotient.FinePELTarget.Construction.finePELClassifyingMap_unique M hM _ _ (M.referencePoint_recovery hM κ hP hκ w)).symm
  have hvp : v ≫ p = M.referencePoint hM κ hP hκ z := by
    dsimp only [v, p]
    rw [← EtaleSmooth.EtaleSmoothLocus.baseChangePoint_comp, hsource]
    change (M.complexPointBaseEquiv κ).symm _ = _
    rw [hz, Equiv.symm_apply_apply]
  have hvq : v ≫ q = M.referencePoint hM κ hP hκ w := by
    dsimp only [v, q]
    rw [← EtaleSmooth.EtaleSmoothLocus.baseChangePoint_comp, htarget]
    change (M.complexPointBaseEquiv κ).symm _ = _
    rw [hw, Equiv.symm_apply_apply]
  apply openPiece_dimension_eq_of_etale_span p q R S (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.underlying v)
  · change ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.underlying (v ≫ p) ∈ R.support
    rwa [hvp]
  · change ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.underlying (v ≫ q) ∈ S.support
    rwa [hvq]

omit [NumberField K] in
theorem _root_.OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Models.FinePELModel.exists_reference_surface_ball_patch [QuasiCompact M.space.hom]
    (hs : 0 < s) (hdegree : Module.finrank ℚ E = 2 * s) :
    ∃ O : Set Geometry.ComplexBall.PrescribedSignsB.BallChart, IsOpen O ∧ O.Nonempty ∧ O ⊆ P.domain ∧
      ∀ z : P.domain, z.val ∈ O →
        ∃ R : CycleClass.Geometric.IntegralSmoothStratification.IntegralSmoothGeometricPiece (M.complexFiber κ).hom,
          IsOpenImmersion R.inclusion ∧ R.complexDimension = 2 ∧
          ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.underlying (M.referencePoint hM κ hP hκ z) ∈ R.support := by
  have : LocallyOfFiniteType (M.complexFiber κ).hom := M.complexFiber_locallyFiniteType κ
  obtain ⟨S, hS, a, x, hx⟩ :=
    M.exists_reference_smooth_surface_stratum hM κ hP hκ hs hdegree
  let f := Intrinsic.SmoothStrata.smoothPieceInclusion (M.complexFiber κ) S
  have hdim : Betti.AffineDimension.Realization.functionFieldDifferentialDimension S.toOver.hom = 2 :=
    (Intrinsic.SmoothStrata.smoothPiece_dimension (M.complexFiber κ) S).trans hS
  obtain ⟨e, he, _, _, htarget, hmod⟩ :=
    M.exists_native_reference_moduli_chart hM κ hP hκ f hs hdegree hdim x a hx
  refine ⟨e.target, e.open_target, ⟨e x, e.map_source he⟩, htarget, ?_⟩
  intro z hz
  let y := e.symm z.val
  have hy : y ∈ e.source := e.map_target hz
  obtain ⟨hp, hpoint⟩ := hmod y hy
  have hz' : (⟨e y, hp⟩ : P.domain) = z := Subtype.ext (e.right_inv hz)
  rw [hz'] at hpoint
  have hb : Function.Bijective (f.left.stalkMap (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.underlying y)).hom := by
    rw [show ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.underlying y = y.left (IsLocalRing.closedPoint ℂ) from
      congrArg y.left (Subsingleton.elim ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.basePoint (IsLocalRing.closedPoint ℂ))]
    exact (M.complexPoint_surface_stalk_data hP hM κ hκ f y hdim).1
  obtain ⟨R, hopen, hmem, hd⟩ := exists_open_piece_of_bijective_stalk f y hb
  refine ⟨R, hopen, hd.trans hdim, ?_⟩
  rwa [hpoint] at hmem

/-- Every original reference point has a genuine open surface neighborhood
in the unreduced fine PEL scheme. -/
theorem _root_.OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Models.FinePELModel.exists_reference_open_surface [QuasiCompact M.space.hom]
    (hN : 3 ≤ N) (hs : 0 < s) (hdegree : Module.finrank ℚ E = 2 * s)
    (z : P.domain) :
    ∃ R : CycleClass.Geometric.IntegralSmoothStratification.IntegralSmoothGeometricPiece (M.complexFiber κ).hom,
      IsOpenImmersion R.inclusion ∧ R.complexDimension = 2 ∧
      ∃ x : R.analyticSpace,
        x ≫ Intrinsic.SmoothStrata.smoothPieceInclusion (M.complexFiber κ) R = M.referencePoint hM κ hP hκ z := by
  classical
  let X := M.complexFiber κ
  have : LocallyOfFiniteType X.hom := M.complexFiber_locallyFiniteType κ
  have : IsLocallyNoetherian X.left := LocallyOfFiniteType.isLocallyNoetherian X.hom
  have : CompactSpace X.left := inferInstanceAs
    (CompactSpace (pullback M.space.hom (Spec.map (CommRingCat.ofHom κ)) : Scheme))
  have : IsNoetherian X.left := ⟨⟩
  obtain ⟨R, hR, hzR⟩ := exists_integral_smooth_open_piece_at X
    (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.underlying (M.referencePoint hM κ hP hκ z))
    (M.referencePoint_mem_smoothLocus hM κ hP hκ hN hs hdegree z)
  have : IsOpenImmersion R.inclusion := hR
  obtain ⟨O, hO, ⟨v, hv⟩, hdom, hsurface⟩ :=
    M.exists_reference_surface_ball_patch hM κ hP hκ hs hdegree
  let w₀ : P.domain := ⟨v, hdom hv⟩
  have hdata := hP
  rcases hdata with ⟨_, hb, hbne, _, _, _, _, _, _, hlat, _, _, _, hδ, _⟩
  let H : Matrix (Fin 3) (Fin 3) E := Matrix.diagonal ![1, 1, P.b]
  have hHerm : ∀ i j, H i j = NumberField.IsCMField.complexConj E (H j i) := by
    intro i j
    by_cases hij : i = j
    · subst j
      fin_cases i <;> simp [H, hb]
    · simp [H, Matrix.diagonal, hij, Ne.symm hij]
  have hdet : H.det ≠ 0 := by
    simpa [H, Matrix.det_diagonal, Fin.prod_univ_succ] using hbne
  let e : (Fin 3 → ℂ) ≃ₗ[ℂ] (Fin 3 → ℂ) := LinearEquiv.refl ℂ _
  have he : ∀ x y, Datum.RankThreePELDatum.complexMatrixHermitian P.μ H (e x) (e y) =
      Datum.RankThreePELDatum.complexMatrixHermitian P.μ (Matrix.diagonal ![1, 1, P.b]) x y := by
    intro x y
    rfl
  have hC : 0 < (∏ i, P.polarizationType i) ^ 2 :=
    pow_pos (Finset.prod_pos (fun i _ => hδ i)) 2
  obtain ⟨g, D, m, m', hg, _, hhit, hD, hcopN, hcopδ, hmod, hm, hm', _, _, hcongr, _⟩ :=
    PrimeBallLatticeIsogenies.exists_original_ball_paired_lattice_maps P hP H hHerm hdet P.lattice hlat e he
      N ((∏ i, P.polarizationType i) ^ 2) (NeZero.pos N) hC z w₀ O hO hv
  have hg' : g ∈ Groups.unitarySubgroup (NumberTheory.ArithmeticGroups.Data.CongruenceLevel.hermitian P.b) := by
    intro x y
    simpa only [H, Principal.BallAction.matrixHermitian_diagonal] using hg x y
  change P.lineAction g z.val ∈ O at hhit
  let w : P.domain := ⟨P.lineAction g z.val, hdom hhit⟩
  obtain ⟨S, hS, hdimS, hwS⟩ := hsurface w hhit
  have : IsOpenImmersion S.inclusion := hS
  obtain ⟨f⟩ := P.reference_paired_quotient_of_scaled_isometry hP z w iota κ hκ N
    g hg' rfl D hD hmod m m' hm hm' hcongr
  have hdimR : R.complexDimension = 2 :=
    (M.reference_pairedQuotient_openPiece_dimension hM κ hP hκ hN
      (pow_pos hD 2) hcopN hmod hcopδ z w f R S hzR hwS).trans hdimS
  have : IsOpenImmersion (Intrinsic.SmoothStrata.smoothPieceInclusion X R).left := hR
  have hrange : M.referencePoint hM κ hP hκ z ∈
      Set.range (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map (Intrinsic.SmoothStrata.smoothPieceInclusion X R)) := by
    rw [ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.range_map_of_isOpenImmersion]
    exact hzR
  exact ⟨R, hR, hdimR, hrange⟩

/-- The literal reference map is locally the inverse of a native holomorphic
period chart on an actual open subscheme of the fine model. -/
theorem _root_.OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Models.FinePELModel.exists_native_reference_open_chart [QuasiCompact M.space.hom]
    (hN : 3 ≤ N) (hs : 0 < s) (hdegree : Module.finrank ℚ E = 2 * s)
    (z : P.domain) :
    ∃ R : CycleClass.Geometric.IntegralSmoothStratification.IntegralSmoothGeometricPiece (M.complexFiber κ).hom,
      IsOpenImmersion R.inclusion ∧ R.complexDimension = 2 ∧
      ∃ e : OpenPartialHomeomorph R.analyticSpace Geometry.ComplexBall.PrescribedSignsB.BallChart,
        z.val ∈ e.target ∧
        e.MDifferentiable (𝓘(ℂ, Fin (Betti.AffineDimension.Realization.functionFieldDifferentialDimension R.toOver.hom) → ℂ))
          (𝓘(ℂ, Geometry.ComplexBall.PrescribedSignsB.BallChart)) ∧ e.target ⊆ P.domain ∧
        ∀ y ∈ e.source, ∃ hp : e y ∈ P.domain,
          y ≫ Intrinsic.SmoothStrata.smoothPieceInclusion (M.complexFiber κ) R = M.referencePoint hM κ hP hκ ⟨e y, hp⟩ := by
  obtain ⟨R, hopen, hdim, x, hx⟩ :=
    M.exists_reference_open_surface hM κ hP hκ hN hs hdegree z
  obtain ⟨e, he, hez, hhol, htarget, hmod⟩ := M.exists_native_reference_moduli_chart
    hM κ hP hκ (Intrinsic.SmoothStrata.smoothPieceInclusion (M.complexFiber κ) R) hs hdegree hdim x z hx
  refine ⟨R, hopen, hdim, e, ?_, hhol, htarget, hmod⟩
  rw [← hez]
  exact e.map_source he

theorem _root_.OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Models.FinePELModel.referencePoint_isLocalHomeomorph [QuasiCompact M.space.hom]
    (hN : 3 ≤ N) (hs : 0 < s) (hdegree : Module.finrank ℚ E = 2 * s) :
    IsLocalHomeomorph (M.referencePoint hM κ hP hκ) := by
  apply isLocalHomeomorph_of_open_period_charts P.domain_isOpen
  intro z
  obtain ⟨R, hopen, _, e, hz, _, _, hmod⟩ :=
    M.exists_native_reference_open_chart hM κ hP hκ hN hs hdegree z
  exact ⟨R, hopen, e, hz, hmod⟩

theorem _root_.OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Models.FinePELModel.referencePoint_continuous [QuasiCompact M.space.hom]
    (hN : 3 ≤ N) (hs : 0 < s) (hdegree : Module.finrank ℚ E = 2 * s) :
    Continuous (M.referencePoint hM κ hP hκ) :=
  (M.referencePoint_isLocalHomeomorph hM κ hP hκ hN hs hdegree).continuous

theorem _root_.OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Models.FinePELModel.referencePoint_isOpenMap [QuasiCompact M.space.hom]
    (hN : 3 ≤ N) (hs : 0 < s) (hdegree : Module.finrank ℚ E = 2 * s) :
    IsOpenMap (M.referencePoint hM κ hP hκ) :=
  (M.referencePoint_isLocalHomeomorph hM κ hP hκ hN hs hdegree).isOpenMap

theorem _root_.OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Models.FinePELModel.referenceOrbitMap_continuous [QuasiCompact M.space.hom]
    (hN : 3 ≤ N) (hs : 0 < s) (hdegree : Module.finrank ℚ E = 2 * s) :
    Continuous (M.referenceOrbitMap hM κ hP hκ) :=
  (M.referencePoint_continuous hM κ hP hκ hN hs hdegree).quotient_lift _

theorem _root_.OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Models.FinePELModel.referenceOrbitMap_isOpenEmbedding [QuasiCompact M.space.hom]
    (hN : 3 ≤ N) (hs : 0 < s) (hdegree : Module.finrank ℚ E = 2 * s) :
    Topology.IsOpenEmbedding (M.referenceOrbitMap hM κ hP hκ) := by
  apply Topology.IsOpenEmbedding.of_continuous_injective_isOpenMap
    (M.referenceOrbitMap_continuous hM κ hP hκ hN hs hdegree)
    (M.referenceOrbitMap_injective hM κ hP hκ hN)
  exact (P.principalOrbitProjection_isOpenQuotientMap N).isOpenMap_iff.mpr
    (M.referencePoint_isOpenMap hM κ hP hκ hN hs hdegree)

omit [IsGalois ℚ E] [NumberField K] [LocallyOfFiniteType M.space.hom] in
theorem _root_.OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Models.FinePELModel.referenceOrbitMap_range :
    Set.range (M.referenceOrbitMap hM κ hP hκ) = Set.range (M.referencePoint hM κ hP hκ) := by
  ext y
  constructor
  · rintro ⟨q, rfl⟩
    induction q using Quotient.inductionOn with
    | h z => exact ⟨z, rfl⟩
  · rintro ⟨z, rfl⟩
    exact ⟨P.principalOrbitProjection N z, rfl⟩

/-- The original reference locus is a compact connected analytic open
contained in the smooth locus of the unreduced fine model. -/
theorem _root_.OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Models.FinePELModel.referenceImage_compact_open_connected_smooth [QuasiCompact M.space.hom]
    (hN : 3 ≤ N) (hs : 0 < s) (hdegree : Module.finrank ℚ E = 2 * s) :
    IsCompact (Set.range (M.referencePoint hM κ hP hκ)) ∧
      IsOpen (Set.range (M.referencePoint hM κ hP hκ)) ∧
      IsConnected (Set.range (M.referencePoint hM κ hP hκ)) ∧
      Set.range (M.referencePoint hM κ hP hκ) ⊆
        ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.underlying ⁻¹' (M.complexFiber κ).hom.smoothLocus := by
  have : CompactSpace (Quotient (P.principalOrbitSetoid N)) :=
    P.principalOrbitQuotient_compact hP N (NeZero.ne N)
  have : ConnectedSpace P.domain := P.domain_connected hP
  refine ⟨?_, (M.referencePoint_isOpenMap hM κ hP hκ hN hs hdegree).isOpen_range,
    isConnected_range (M.referencePoint_continuous hM κ hP hκ hN hs hdegree), ?_⟩
  · rw [← M.referenceOrbitMap_range hM κ hP hκ]
    exact isCompact_range (M.referenceOrbitMap_continuous hM κ hP hκ hN hs hdegree)
  · rintro _ ⟨z, rfl⟩
    exact M.referencePoint_mem_smoothLocus hM κ hP hκ hN hs hdegree z

end FinePELModel

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Reference.PointTopology
