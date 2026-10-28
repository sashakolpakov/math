import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Family.MarkedKernelImages
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Intrinsic.ComplexUniversal
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.FinePELDimension
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Intrinsic.SmoothStrata
import OAI.RepresentationTheory.Theta.Geometric.Holomorphic.ImageMeasure
import Mathlib.MeasureTheory.Measure.Lebesgue.Complex

/-! # Surface Stratum -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily

noncomputable section

/-! An actual collection of PEL objects whose native marked Hodge lines
range over an open ball meets a smooth surface stratum of the fine moduli
scheme. The marking and rational Hermitian form may differ from the
reference datum. No continuity of the object assignment is required. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.MeasureTheory _root_.MeasureTheory.Measure
open scoped Classical

open OAI.RepresentationTheory.Theta.Geometric.Holomorphic.ImageMeasure

attribute [local irreducible] Models.FinePELModel.complexTestFamily

variable {E K : Type} [Field E] [NumberField E] [NumberField.IsCMField E]
    [Field K] {s N : ℕ} {P : Datum.RankThreePELDatum E s} {iota : E →+* K}
    (M : Models.FinePELModel P iota N) (hM : M.IsFine) (κ : K →+* ℂ)

def Models.FinePELModel.objectPoint (B : PEL.Objects.PELObject P iota N (Over.mk (Spec.map (CommRingCat.ofHom κ)))) :
    M.ComplexPoints κ := (M.complexPointClassEquiv κ hM).symm B.classOf

theorem Models.FinePELModel.objectPoint_class
    (B : PEL.Objects.PELObject P iota N (Over.mk (Spec.map (CommRingCat.ofHom κ)))) :
    (M.universal.pullback (M.complexPointBaseEquiv κ (M.objectPoint hM κ B))).classOf = B.classOf :=
  (M.complexPointClassEquiv κ hM).apply_symm_apply _

theorem Models.FinePELModel.complexTestFamily_object_iso
    {S : Over Foundations.Scheme.ProjectiveSpace.complexBase} (f : S ⟶ M.complexFiber κ)
    (B : PEL.Objects.PELObject P iota N (Over.mk (Spec.map (CommRingCat.ofHom κ))))
    (y : AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints S) (hy : y ≫ f = M.objectPoint hM κ B) :
    Nonempty (PEL.Objects.PELIso B ((M.complexTestFamily κ f).pullback (Intrinsic.ComplexUniversal.complexPointRestriction κ y))) := by
  apply (PEL.Objects.PELObject.classOf_eq_iff _ _).mp
  calc
    B.classOf =
        (M.universal.pullback (M.complexPointBaseEquiv κ (M.objectPoint hM κ B))).classOf :=
      (M.objectPoint_class hM κ B).symm
    _ = (M.universal.pullback (M.complexPointBaseEquiv κ (y ≫ f))).classOf :=
      congrArg (fun p => (M.universal.pullback (M.complexPointBaseEquiv κ p)).classOf) hy.symm
    _ = ((M.complexTestFamily κ f).pullback (Intrinsic.ComplexUniversal.complexPointRestriction κ y)).classOf :=
      (M.complexTestFamily_point_class κ f y).symm

theorem Models.FinePELModel.exists_native_object_testFiber_iso
    {S : Over Foundations.Scheme.ProjectiveSpace.complexBase} (f : S ⟶ M.complexFiber κ)
    (B : PEL.Objects.PELObject P iota N (Over.mk (Spec.map (CommRingCat.ofHom κ))))
    (C : ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety) (eC : C.toOver ≅ B.polarized.abelian.scheme) [IsMonHom eC.hom]
    (y : AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints S) (hy : y ≫ f = M.objectPoint hM κ B) :
    ∃ e : C.toOver ≅ (RepresentationTheory.Theta.Geometric.PolarizedCanonicalForm.polarizedFamilyPresentation (M.complexTestFamily κ f).polarized y).variety.toOver,
      IsMonHom e.hom := by
  obtain ⟨eB⟩ := M.complexTestFamily_object_iso hM κ f B y hy
  let Q := RepresentationTheory.Theta.Geometric.PolarizedCanonicalForm.polarizedFamilyPresentation (M.complexTestFamily κ f).polarized y
  let : GrpObj C.toOver := C.group
  let : GrpObj B.polarized.abelian.scheme := B.polarized.abelian.group
  let : GrpObj ((M.complexTestFamily κ f).pullback
      (Intrinsic.ComplexUniversal.complexPointRestriction κ y)).polarized.abelian.scheme :=
    ((M.complexTestFamily κ f).pullback (Intrinsic.ComplexUniversal.complexPointRestriction κ y)).polarized.abelian.group
  let : GrpObj Q.variety.toOver := Q.variety.group
  let : IsMonHom eB.polarized.abelian.hom := eB.polarized.abelianGroup
  let : IsMonHom Q.comparison.hom := Q.comparison_group
  let e := eC ≪≫ eB.polarized.abelian ≪≫ Q.comparison
  refine ⟨e, ?_⟩
  change IsMonHom (eC.hom ≫ eB.polarized.abelian.hom ≫ Q.comparison.hom)
  exact @instIsMonHomComp (Over Foundations.Scheme.ProjectiveSpace.complexBase) _ _ _ _ _
    C.group.toMonObj B.polarized.abelian.group.toMonObj Q.variety.group.toMonObj
    eC.hom (eB.polarized.abelian.hom ≫ Q.comparison.hom) inferInstance
    (@instIsMonHomComp (Over Foundations.Scheme.ProjectiveSpace.complexBase) _ _ _ _ _
      B.polarized.abelian.group.toMonObj
      ((M.complexTestFamily κ f).polarized.abelian.pullback y.left).group.toMonObj
      Q.variety.group.toMonObj eB.polarized.abelian.hom Q.comparison.hom
      eB.polarized.abelianGroup Q.comparison_group)

theorem Models.FinePELModel.exists_countable_object_family_images
    {S : Over Foundations.Scheme.ProjectiveSpace.complexBase} [IsIntegral S.left] [Smooth S.hom]
    [SecondCountableTopology (AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints S)] (f : S ⟶ M.complexFiber κ)
    {D : Set Geometry.ComplexBall.PrescribedSignsB.BallChart}
    (B : D → PEL.Objects.PELObject P iota N (Over.mk (Spec.map (CommRingCat.ofHom κ))))
    (C : D → ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety) (eC : ∀ a, (C a).toOver ≅ (B a).polarized.abelian.scheme)
    (heC : ∀ a, IsMonHom (eC a).hom)
    (j : Geometry.ComplexBall.PrescribedSignsB.Vec →ₗ[ℂ] ComplexMultiplication.WeightOne.CM.Complexification (NumberTheory.ArithmeticGroups.Data.CongruenceLevel.VE E))
    (m : ∀ a, NumberTheory.ArithmeticGroups.Data.CongruenceLevel.VE E →ₗ[ℚ] Intrinsic.RationalPeriods.IntrinsicRationalPeriods.rationalPeriods (C a))
    (hk : ∀ a v, (m a).baseChange ℂ (j v) ∈ (Intrinsic.PeriodProjection.IntrinsicRationalPeriods.complexPeriodProjection (C a)).ker ↔
      v ∈ Submodule.span ℂ {Geometry.ComplexBall.PrescribedSignsB.lineVector a.val}) (hN : 0 < N) :
    let V := Fin (Betti.AffineDimension.Realization.functionFieldDifferentialDimension S.hom) → ℂ
    ∃ I : Type, Countable I ∧ ∃ (O : I → Set V) (period : I → V → Geometry.ComplexBall.PrescribedSignsB.BallChart),
      (∀ i, IsOpen (O i) ∧ DifferentiableOn ℂ (period i) (O i)) ∧
      ∀ a : D, (∃ y : AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints S, y ≫ f = M.objectPoint hM κ (B a)) →
        ∃ i, a.val ∈ period i '' O i := by
  let A := M.complexTestFamily κ f
  obtain ⟨I, hI, O, period, hO, hcover⟩ :=
    Family.MarkedKernelImages.exists_countable_native_marked_kernel_images A.polarized A.action j hN
  refine ⟨I, hI, O, period, hO, ?_⟩
  intro a ha
  obtain ⟨y, hy⟩ := ha
  let : IsMonHom (eC a).hom := heC a
  obtain ⟨e, he⟩ := M.exists_native_object_testFiber_iso hM κ f (B a) (C a) (eC a) y hy
  exact hcover a.val (C a) (m a) (hk a) ⟨y, e, he⟩

theorem Models.FinePELModel.exists_marked_family_surface_stratum [IsGalois ℚ E]
    [LocallyOfFiniteType M.space.hom] [QuasiCompact M.space.hom]
    (hP : P.IsAdmissible) (hκ : κ.comp iota = P.μ)
    (hs : 0 < s) (hdegree : Module.finrank ℚ E = 2 * s) (hN : 0 < N)
    (D : Set Geometry.ComplexBall.PrescribedSignsB.BallChart) (hD : IsOpen D) (hDn : D.Nonempty)
    (B : D → PEL.Objects.PELObject P iota N (Over.mk (Spec.map (CommRingCat.ofHom κ))))
    (C : D → ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety) (eC : ∀ a, (C a).toOver ≅ (B a).polarized.abelian.scheme)
    (heC : ∀ a, IsMonHom (eC a).hom)
    (j : Geometry.ComplexBall.PrescribedSignsB.Vec →ₗ[ℂ] ComplexMultiplication.WeightOne.CM.Complexification (NumberTheory.ArithmeticGroups.Data.CongruenceLevel.VE E))
    (m : ∀ a, NumberTheory.ArithmeticGroups.Data.CongruenceLevel.VE E →ₗ[ℚ] Intrinsic.RationalPeriods.IntrinsicRationalPeriods.rationalPeriods (C a))
    (hk : ∀ a v, (m a).baseChange ℂ (j v) ∈ (Intrinsic.PeriodProjection.IntrinsicRationalPeriods.complexPeriodProjection (C a)).ker ↔
      v ∈ Submodule.span ℂ {Geometry.ComplexBall.PrescribedSignsB.lineVector a.val}) :
    ∃ R : CycleClass.Geometric.IntegralSmoothStratification.IntegralSmoothGeometricPiece (M.complexFiber κ).hom,
      R.complexDimension = 2 ∧ ∃ (a : D) (x : R.analyticSpace),
        x ≫ Intrinsic.SmoothStrata.smoothPieceInclusion (M.complexFiber κ) R = M.objectPoint hM κ (B a) := by
  have : LocallyOfFiniteType (M.complexFiber κ).hom := M.complexFiber_locallyFiniteType κ
  have : QuasiCompact (M.complexFiber κ).hom :=
    inferInstanceAs (QuasiCompact (Limits.pullback.snd M.space.hom (Spec.map (CommRingCat.ofHom κ))))
  have : SecondCountableTopology (M.ComplexPoints κ) := AlgebraicGeometry.ComplexPoints.Analytic.FiniteTypeSchemeTopology.schemePoints_secondCountable (M.complexFiber κ)
  let Q := CycleClass.Geometric.IntegralSmoothStratification.integralSmoothGeometricStratification_of_finiteType (M.complexFiber κ).hom
  let R (k : Fin Q.pieces.length) := Q.pieces.get k
  let f (k : Fin Q.pieces.length) := Intrinsic.SmoothStrata.smoothPieceInclusion (M.complexFiber κ) (R k)
  have (k : Fin Q.pieces.length) : SecondCountableTopology (R k).analyticSpace :=
    Intrinsic.SmoothStrata.smoothPiece_secondCountable (M.complexFiber κ) (R k)
  have hex (k : Fin Q.pieces.length) :=
    M.exists_countable_object_family_images hM κ (f k) B C eC heC j m hk hN
  choose I hI O period hO hcover using hex
  have (k : Fin Q.pieces.length) : Countable (I k) := hI k
  let hit (k : Fin Q.pieces.length) := ∃ (a : D) (x : (R k).analyticSpace),
    x ≫ f k = M.objectPoint hM κ (B a)
  have hlarge : ∃ k : Fin Q.pieces.length, 2 ≤ (R k).complexDimension ∧ hit k := by
    by_contra hn
    have hsmall (k : Fin Q.pieces.length) (hk : hit k) : (R k).complexDimension < 2 :=
      lt_of_not_ge (fun hd => hn ⟨k, hd, hk⟩)
    let J := {i : (Σ k : Fin Q.pieces.length, I k) // hit i.1}
    let μ : Measure Geometry.ComplexBall.PrescribedSignsB.BallChart := volume
    have hzero (i : J) : μ (period i.val.1 i.val.2 '' O i.val.1 i.val.2) = 0 := by
      apply RepresentationTheory.Theta.Geometric.Holomorphic.ImageMeasure.measure_image_eq_zero_of_complex_finrank_lt μ (hO i.val.1 i.val.2).1 (hO i.val.1 i.val.2).2
      have hd : Betti.AffineDimension.Realization.functionFieldDifferentialDimension (R i.val.1).toOver.hom < 2 := by
        rw [Intrinsic.SmoothStrata.smoothPiece_dimension (M.complexFiber κ) (R i.val.1)]
        exact hsmall i.val.1 i.property
      simpa only [Geometry.ComplexBall.PrescribedSignsB.BallChart, Module.finrank_pi, Fintype.card_fin] using hd
    have hnull : μ D = 0 := by
      apply measure_mono_null (t := ⋃ i : J, period i.val.1 i.val.2 '' O i.val.1 i.val.2) ?_
        (measure_iUnion_null hzero)
      intro a ha
      obtain ⟨k, x, hx⟩ := Intrinsic.SmoothStrata.smoothStratification_complexPoint_cover (M.complexFiber κ) Q
        (M.objectPoint hM κ (B ⟨a, ha⟩))
      obtain ⟨i, hi⟩ := hcover k ⟨a, ha⟩ ⟨x, hx⟩
      exact Set.mem_iUnion.mpr ⟨⟨⟨k, i⟩, ⟨⟨a, ha⟩, x, hx⟩⟩, hi⟩
    exact (ne_of_gt (hD.measure_pos (μ := μ) hDn)) hnull
  obtain ⟨k, hkdim, a, x, hx⟩ := hlarge
  have hu := M.smooth_subspace_dimension_le_two hM κ hκ (f k) x hs hdegree hP hN
  rw [Intrinsic.SmoothStrata.smoothPiece_dimension (M.complexFiber κ) (R k)] at hu
  exact ⟨R k, Nat.le_antisymm hu hkdim, a, x, hx⟩

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily
