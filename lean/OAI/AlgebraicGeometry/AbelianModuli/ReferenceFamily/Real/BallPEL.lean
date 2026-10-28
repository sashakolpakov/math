import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Real.ChangedPELModel
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Intrinsic.BallCoordinateData
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Marked.Scheme

/-! # Ball PEL -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Real.BallPEL

noncomputable section

/-! For every original complex PEL object, its actual rational
Hermitian space and integral lattice give a PEL object over every point
of the negative-line ball. One fixed embedding inclusion recovers each
ball coordinate from the new object's genuine native period kernel. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.AbelianUniformizationEq.Constructions.AbelianUniformization
open scoped Classical _root_.CategoryTheory.MonObj

open OAI.AlgebraicGeometry.Picard.ThetaConstruction.DefinitionsIntegral

local instance (B : ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety) : IsIntegral B.toOver.left := B.variety.property
local instance (B : ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety) : Smooth B.toOver.hom := B.variety.presentation.smooth

attribute [local irreducible] PEL.RealPeriodChanges.IntrinsicPELRealChanges.changeMap
  ChangedPELModel.RealChangedPEL.action ChangedPELModel.RealChangedPEL.fullLevel

attribute [local implicit_reducible] Picard.ThetaConstruction.PeriodModel.Geometric.AlgebraicPeriodModel.abelianScheme
  Abelian.IntrinsicAdapter.AbelianIntrinsicAdapter.native Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation.toOver

variable {E K : Type} [Field E] [NumberField E] [Algebra ℚ E]
    [NumberField.IsCMField E] [Field K]
    {s N : ℕ} {P : Datum.RankThreePELDatum E s} {iota : E →+* K} {κ : K →+* ℂ}
    (A : PEL.Objects.PELObject P iota N (Over.mk (Spec.map (CommRingCat.ofHom κ))))
    (hs : 0 < s) (hdegree : Module.finrank ℚ E = 2 * s)

local notation "PA" => OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Polarized.Projectivity.polarizedNativeProjectivePresentation A.polarized
local notation "A₀" => OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Abelian.IntrinsicAdapter.AbelianIntrinsicAdapter.native A.polarized.abelian PA
local notation "bA" => OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Marked.Scheme.originalNativeIntegralMarking A.polarized.abelian PA
local notation "LA" => OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Intrinsic.ChernPairing.polarizationLineBundle A.polarized
local notation "hLA" => OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Intrinsic.ChernPairing.polarizationLineBundle_ample A.polarized

namespace NativeBallCoordinateData

variable {A hs hdegree} (D : Intrinsic.BallCoordinateData.NativeBallCoordinateData A hs hdegree) (hP : P.IsAdmissible)

structure _root_.OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Intrinsic.BallCoordinateData.NativeBallCoordinateData.Fiber (r : Geometry.ComplexBall.PrescribedSignsB.Vec ≃ₗ[ℂ] Geometry.ComplexBall.PrescribedSignsB.Vec) where
  model : ChangedModel.RealChangedAlgebraicModel A₀ bA (D.realChange hP r) LA hLA
  dual : Picard.ThetaConstruction.IntegralDualModel.Geometric.IntegralDualAlgebraicModel model.torus
  isogeny : Picard.ThetaConstruction.IntegralDualIsogenyKernel.Geometric.IntegralDualLatticeIsogeny model.model dual
  primitive : Picard.ThetaConstruction.PrimitiveDual.Geometric.PrimitiveDualConstruction isogeny

def _root_.OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Intrinsic.BallCoordinateData.NativeBallCoordinateData.fiber (r : Geometry.ComplexBall.PrescribedSignsB.Vec ≃ₗ[ℂ] Geometry.ComplexBall.PrescribedSignsB.Vec)
    (hr : ∀ x y, ReferenceFamily.Complex.HermitianMatrixForm.complexHermitianMatrixForm (Matrix.diagonal ![1, 1, P.μ P.b]) (r x) (r y) =
      ReferenceFamily.Complex.HermitianMatrixForm.complexHermitianMatrixForm (Matrix.diagonal ![1, 1, P.μ P.b]) x y) : D.Fiber hP r := by
  apply Classical.choice
  let R := ChangedModel.realChangedAlgebraicModel A₀ bA (D.realChange hP r) LA hLA (D.realChange_riemann hP r hr)
  obtain ⟨B, p, ⟨C⟩⟩ := Picard.ThetaConstruction.PrimitiveDual.Geometric.exists_primitive_dual_on_actual_model R.model
    (Intrinsic.ChernIntegralPeriods.nativeIntegralChernMatrix_alternating A₀ LA bA)
  exact ⟨⟨R, B, p, C⟩⟩

namespace Fiber

variable {D hP} {r : Geometry.ComplexBall.PrescribedSignsB.Vec ≃ₗ[ℂ] Geometry.ComplexBall.PrescribedSignsB.Vec} (F : D.Fiber hP r)

def _root_.OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Intrinsic.BallCoordinateData.NativeBallCoordinateData.Fiber.object [NeZero N] : PEL.Objects.PELObject P iota N (Over.mk (Spec.map (CommRingCat.ofHom κ))) :=
  ChangedPELModel.RealChangedPEL.object A bA (D.realChange hP r) F.model (D.realChange_commutes hP r) F.primitive hP

def _root_.OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Intrinsic.BallCoordinateData.NativeBallCoordinateData.Fiber.marking : NumberTheory.ArithmeticGroups.Data.CongruenceLevel.VE E ≃ₗ[ℚ] Intrinsic.RationalPeriods.IntrinsicRationalPeriods.rationalPeriods F.model.model.abelian :=
  (PEL.RealPeriodChanges.IntrinsicPELRealChanges.rationalMarking A.polarized A.action s hs rfl hdegree).symm.trans
    F.model.rationalMarking

def _root_.OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Intrinsic.BallCoordinateData.NativeBallCoordinateData.Fiber.fieldMarking [NeZero N] :=
  ChangedPELModel.RealChangedPEL.objectFieldMarking A bA (D.realChange hP r) F.model
    (D.realChange_commutes hP r) F.primitive hP hs hdegree

theorem _root_.OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Intrinsic.BallCoordinateData.NativeBallCoordinateData.Fiber.fieldMarking_apply [NeZero N] (v : NumberTheory.ArithmeticGroups.Data.CongruenceLevel.VE E) :
    F.fieldMarking.toEquiv v = F.marking v := rfl

theorem _root_.OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Intrinsic.BallCoordinateData.NativeBallCoordinateData.Fiber.marking_integral (v : NumberTheory.ArithmeticGroups.Data.CongruenceLevel.VE E) :
    (F.marking v).val ∈ HodgeConjecture.DegreeTwo.AbelianUniformizationEq.Constructions.AbelianUniformization.periodLattice F.model.model.abelian ↔
      ((PEL.RealPeriodChanges.IntrinsicPELRealChanges.rationalMarking A.polarized A.action s hs rfl hdegree).symm v).val ∈
        HodgeConjecture.DegreeTwo.AbelianUniformizationEq.Constructions.AbelianUniformization.periodLattice A₀ := F.model.rationalMarking_integral _

theorem _root_.OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Intrinsic.BallCoordinateData.NativeBallCoordinateData.Fiber.marking_polarization [NeZero N]
    (hr : ∀ x y, ReferenceFamily.Complex.HermitianMatrixForm.complexHermitianMatrixForm (Matrix.diagonal ![1, 1, P.μ P.b]) (r x) (r y) =
      ReferenceFamily.Complex.HermitianMatrixForm.complexHermitianMatrixForm (Matrix.diagonal ![1, 1, P.μ P.b]) x y) (v w : NumberTheory.ArithmeticGroups.Data.CongruenceLevel.VE E) :
    Intrinsic.ChernPairing.nativePolarizationForm F.object.polarized (F.marking v) (F.marking w) =
      Intrinsic.ChernPairing.nativePolarizationForm A.polarized
        ((PEL.RealPeriodChanges.IntrinsicPELRealChanges.rationalMarking A.polarized A.action s hs rfl hdegree).symm v)
        ((PEL.RealPeriodChanges.IntrinsicPELRealChanges.rationalMarking A.polarized A.action s hs rfl hdegree).symm w) :=
  ChangedPELModel.RealChangedPEL.object_rationalMarking_polarization A bA (D.realChange hP r) F.model
    (D.realChange_commutes hP r) F.primitive hP (D.realChange_riemann hP r hr) _ _

theorem _root_.OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Intrinsic.BallCoordinateData.NativeBallCoordinateData.Fiber.marking_original_period (v : Intrinsic.RationalPeriods.IntrinsicRationalPeriods.rationalPeriods A₀) :
    F.marking (PEL.RealPeriodChanges.IntrinsicPELRealChanges.rationalMarking A.polarized A.action s hs rfl hdegree v) =
      F.model.rationalMarking v := by
  change F.model.rationalMarking ((PEL.RealPeriodChanges.IntrinsicPELRealChanges.rationalMarking A.polarized A.action
    s hs rfl hdegree).symm ((PEL.RealPeriodChanges.IntrinsicPELRealChanges.rationalMarking A.polarized A.action
      s hs rfl hdegree) v)) = _
  rw [LinearEquiv.symm_apply_apply]

theorem _root_.OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Intrinsic.BallCoordinateData.NativeBallCoordinateData.Fiber.marking_level [NeZero N] (l : HodgeConjecture.DegreeTwo.AbelianUniformizationEq.Constructions.AbelianUniformization.periodLattice A₀) :
    (F.object.polarized.level.hom.app (.op (ConstantSectionsOn.ConstantSections.baseTest Foundations.Scheme.ProjectiveSpace.complexBase))
      (LocallyConstant.const Foundations.Scheme.ProjectiveSpace.complexBase (ChangedPELModel.RealChangedPEL.originalLevelLabel A l))).val =
        HodgeConjecture.DegreeTwo.ExponentialM.Constructions.Exponential.expMap (C := ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints F.model.model.abelian.toOver)
          ((N : ℝ)⁻¹ • (F.marking (PEL.RealPeriodChanges.IntrinsicPELRealChanges.rationalMarking A.polarized A.action
            s hs rfl hdegree (LatticePeriodEvaluation.LatticeCharacters.latticeInclusion (HodgeConjecture.DegreeTwo.AbelianUniformizationEq.Constructions.AbelianUniformization.periodLattice A₀) l))).val) := by
  exact ChangedPELModel.RealChangedPEL.object_level_of_period A bA (D.realChange hP r) F.model
    (D.realChange_commutes hP r) F.primitive hP l _
    (F.marking_original_period (LatticePeriodEvaluation.LatticeCharacters.latticeInclusion (HodgeConjecture.DegreeTwo.AbelianUniformizationEq.Constructions.AbelianUniformization.periodLattice A₀) l))

def _root_.OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Intrinsic.BallCoordinateData.NativeBallCoordinateData.Fiber.nativeIso [NeZero N] : F.model.model.abelian.toOver ≅ F.object.polarized.abelian.scheme := Iso.refl _

instance _root_.OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Intrinsic.BallCoordinateData.NativeBallCoordinateData.Fiber.nativeIso_isMonHom [NeZero N] : IsMonHom F.nativeIso.hom :=
  inferInstanceAs (IsMonHom (𝟙 F.model.model.abelian.toOver))

theorem _root_.OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Intrinsic.BallCoordinateData.NativeBallCoordinateData.Fiber.marking_projection (v : ComplexMultiplication.WeightOne.CM.Complexification (NumberTheory.ArithmeticGroups.Data.CongruenceLevel.VE E)) :
    Intrinsic.PeriodProjection.IntrinsicRationalPeriods.complexPeriodProjection F.model.model.abelian (F.marking.toLinearMap.baseChange ℂ v) =
      F.model.tangentEquiv (PeriodHodgeTransport.realChangedComplexPeriodMap A₀ (D.realChange hP r)
        ((PEL.RealPeriodChanges.IntrinsicPELRealChanges.rationalMarking A.polarized A.action s hs rfl hdegree).symm.toLinearMap.baseChange ℂ v)) := by
  change Intrinsic.PeriodProjection.IntrinsicRationalPeriods.complexPeriodProjection F.model.model.abelian
    ((F.model.rationalMarking.toLinearMap.comp
      (PEL.RealPeriodChanges.IntrinsicPELRealChanges.rationalMarking A.polarized A.action s hs rfl hdegree).symm.toLinearMap).baseChange ℂ v) = _
  rw [LinearMap.baseChange_comp, LinearMap.comp_apply]
  exact F.model.rationalMarking_projection _

theorem _root_.OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Intrinsic.BallCoordinateData.NativeBallCoordinateData.Fiber.first_kernel (z : P.Domain)
    (hr : (Submodule.span ℂ {Geometry.ComplexBall.PrescribedSignsB.lineVector D.point.val}).map r.toLinearMap =
      Submodule.span ℂ {Geometry.ComplexBall.PrescribedSignsB.lineVector z.val}) (v : Geometry.ComplexBall.PrescribedSignsB.Vec) :
    F.marking.toLinearMap.baseChange ℂ (PeriodEmbeddingChanges.fixedFirstComplexInclusion E
      (P.embeddings P.distinguished) D.normalizer v) ∈ (Intrinsic.PeriodProjection.IntrinsicRationalPeriods.complexPeriodProjection F.model.model.abelian).ker ↔
      v ∈ Submodule.span ℂ {Geometry.ComplexBall.PrescribedSignsB.lineVector z.val} := by
  change Intrinsic.PeriodProjection.IntrinsicRationalPeriods.complexPeriodProjection F.model.model.abelian
    (F.marking.toLinearMap.baseChange ℂ (PeriodEmbeddingChanges.fixedFirstComplexInclusion E
      (P.embeddings P.distinguished) D.normalizer v)) = 0 ↔ _
  rw [F.marking_projection]
  exact (map_eq_zero_iff F.model.tangentEquiv F.model.tangentEquiv.injective).trans
    (PEL.RealPeriodChanges.IntrinsicPELRealChanges.changed_normalized_kernel A.polarized A.action s hs rfl hdegree
      P.embeddings hP.1 (D.components r) P.distinguished D.normalizer r
      (D.components_distinguished r) D.point.val z.val D.hodgeLine hr v)

end Fiber

def _root_.OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Intrinsic.BallCoordinateData.NativeBallCoordinateData.pointTransport (z : P.Domain) :
    {r : Geometry.ComplexBall.PrescribedSignsB.Vec ≃ₗ[ℂ] Geometry.ComplexBall.PrescribedSignsB.Vec //
      (∀ x y, ReferenceFamily.Complex.HermitianMatrixForm.complexHermitianMatrixForm (Matrix.diagonal ![1, 1, P.μ P.b]) (r x) (r y) =
        ReferenceFamily.Complex.HermitianMatrixForm.complexHermitianMatrixForm (Matrix.diagonal ![1, 1, P.μ P.b]) x y) ∧
      (Submodule.span ℂ {Geometry.ComplexBall.PrescribedSignsB.lineVector D.point.val}).map r.toLinearMap =
        Submodule.span ℂ {Geometry.ComplexBall.PrescribedSignsB.lineVector z.val}} := by
  apply Classical.choice
  have him : (P.μ P.b).im = 0 := by
    have h := (ComplexMultiplication.CM.TraceForm.cmFieldConjugation_embedding E (P.embeddings P.distinguished) P.b).symm.trans
      (congrArg P.μ hP.2.1)
    have hi := congrArg Complex.im h
    simp only [Complex.star_def, Complex.conj_im] at hi
    change -(P.μ P.b).im = (P.μ P.b).im at hi
    linarith
  obtain ⟨r, hr, hline⟩ := Intrinsic.BallReflectionLifts.exists_diagonalIsometry_line_transport (P.μ P.b) him hP.2.2.2.1
    D.point.val z.val ((Datum.RankThreePELDatum.mem_domain_iff_diagonal D.point.val).mp D.point.property)
    ((Datum.RankThreePELDatum.mem_domain_iff_diagonal z.val).mp z.property)
  exact ⟨⟨r, hr, hline⟩⟩

def _root_.OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Intrinsic.BallCoordinateData.NativeBallCoordinateData.fiberAt (z : P.Domain) : D.Fiber hP (D.pointTransport hP z).val :=
  D.fiber hP (D.pointTransport hP z).val (D.pointTransport hP z).property.1

theorem _root_.OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Intrinsic.BallCoordinateData.NativeBallCoordinateData.fiberAt_kernel (z : P.Domain) (v : Geometry.ComplexBall.PrescribedSignsB.Vec) :
    (D.fiberAt hP z).marking.toLinearMap.baseChange ℂ
      (PeriodEmbeddingChanges.fixedFirstComplexInclusion E (P.embeddings P.distinguished) D.normalizer v) ∈
        (Intrinsic.PeriodProjection.IntrinsicRationalPeriods.complexPeriodProjection (D.fiberAt hP z).model.model.abelian).ker ↔
      v ∈ Submodule.span ℂ {Geometry.ComplexBall.PrescribedSignsB.lineVector z.val} :=
  (D.fiberAt hP z).first_kernel z (D.pointTransport hP z).property.2 v

end NativeBallCoordinateData

include A hs hdegree in
theorem exists_fullBall_native_PEL_family [IsGalois ℚ E] [NeZero N]
    (hP : P.IsAdmissible) (hκ : κ.comp iota = P.μ) :
    ∃ (j : Geometry.ComplexBall.PrescribedSignsB.Vec →ₗ[ℂ] ComplexMultiplication.WeightOne.CM.Complexification (NumberTheory.ArithmeticGroups.Data.CongruenceLevel.VE E))
      (B : P.Domain → PEL.Objects.PELObject P iota N (Over.mk (Spec.map (CommRingCat.ofHom κ))))
      (C : P.Domain → ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety) (eC : ∀ z, (C z).toOver ≅ (B z).polarized.abelian.scheme),
      (∀ z, IsMonHom (eC z).hom) ∧
      ∃ m : ∀ z, NumberTheory.ArithmeticGroups.Data.CongruenceLevel.VE E ≃ₗ[ℚ] Intrinsic.RationalPeriods.IntrinsicRationalPeriods.rationalPeriods (C z),
        ∀ z v, (m z).toLinearMap.baseChange ℂ (j v) ∈ (Intrinsic.PeriodProjection.IntrinsicRationalPeriods.complexPeriodProjection (C z)).ker ↔
          v ∈ Submodule.span ℂ {Geometry.ComplexBall.PrescribedSignsB.lineVector z.val} := by
  let D := Intrinsic.BallCoordinateData.nativeBallCoordinateData A hs hdegree hP hκ
  refine ⟨PeriodEmbeddingChanges.fixedFirstComplexInclusion E (P.embeddings P.distinguished) D.normalizer,
    fun z => (D.fiberAt hP z).object, fun z => (D.fiberAt hP z).model.model.abelian,
    fun z => (D.fiberAt hP z).nativeIso, fun _ => inferInstance,
    fun z => (D.fiberAt hP z).marking, ?_⟩
  exact D.fiberAt_kernel hP

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Real.BallPEL
