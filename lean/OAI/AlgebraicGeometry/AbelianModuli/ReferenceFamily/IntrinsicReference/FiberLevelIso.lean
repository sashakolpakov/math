import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.IntrinsicReference.Fiber
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.IntrinsicReference.TransportedLevel
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Polarized.ComparisonMarkedLevel

/-! # Fiber Level Iso -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily

noncomputable section

section

/-! The algebraized native reference comparison preserves every ordered
level section on every test and hence gives an actual level isomorphism. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj

attribute [local implicit_reducible] Complex.BallPeriods.restrictComplexBase
  RepresentationTheory.Theta.Geometric.PolarizedCanonicalForm.polarizedFamilyPresentation RepresentationTheory.Theta.Geometric.PolarizedCanonicalForm.polarizedNativePresentation
attribute [local irreducible] Models.FinePELModel.complexTestFamily Models.FinePELModel.nativeReferenceFiberPolarizedComparison

variable {E K : Type} [Field E] [NumberField E] [NumberField.IsCMField E] [IsGalois ℚ E]
    [Field K] {s N : ℕ} [NeZero N] {P : Datum.RankThreePELDatum E s} {iota : E →+* K}
    (M : Models.FinePELModel P iota N) (hM : M.IsFine) (κ : K →+* ℂ)
    (hP : P.IsAdmissible) (hκ : κ.comp iota = P.μ)
    {S : Over Foundations.Scheme.ProjectiveSpace.complexBase} (f : S ⟶ M.complexFiber κ) (a : P.domain)
    {x : ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints S}
    {C : PELModuli.CMPoints.IntrinsicFamilyCharts.NativeFamilyCharts (M.complexTestFamily κ f).polarized.abelian x}
    {F : RepresentationTheory.Theta.Geometric.Intrinsic.FamilyFrames.NativeFamilyPeriodFrame C}
    (H : Intrinsic.HolomorphicTransport.NativeFamilyHolomorphicTransport (M.complexTestFamily κ f).polarized
      (M.complexTestFamily κ f).action F)
    (z₀ : H.compatible.neighborhood)
    (hz₀ : RepresentationTheory.Theta.Geometric.Intrinsic.FamilyFrames.familyChartParameter C z₀ ≫ f = M.referencePoint hM κ hP hκ a)
    (b : P.domain) (z : H.compatible.neighborhood)
    (hs : 0 < s) (hdegree : Module.finrank ℚ E = 2 * s)
    (hk : (H.referenceMarkedMatrix P hP
      (M.transportedNativeReferenceLabel hM κ hP hκ f a H z₀ hz₀) z).ker =
        Submodule.span ℂ {Geometry.ComplexBall.PrescribedSignsB.lineVector b.val})

theorem Models.FinePELModel.nativeReferenceFiberPolarizedComparison_level (T : Over Foundations.Scheme.ProjectiveSpace.complexBase)
    (c : LocallyConstant T.left (Multiplicative (Fin (2 * (3 * s)) → ZMod N))) :
    ((((M.complexTestFamily κ (M.referencePoint hM κ hP hκ b)).polarized.level.pullback (𝟙 Foundations.Scheme.ProjectiveSpace.complexBase)).hom.app
      (.op T)) c).val ≫
        (M.nativeReferenceFiberPolarizedComparison hM κ hP hκ f a H z₀ hz₀ b z hs hdegree hk).algebraicIso.hom =
      ((((M.complexTestFamily κ f).polarized.level.pullback (RepresentationTheory.Theta.Geometric.Intrinsic.FamilyFrames.familyChartParameter C z).left).hom.app (.op T)) c).val := by
  let D := M.nativeReferenceFiberPolarizedComparison hM κ hP hκ f a H z₀ hz₀ b z hs hdegree hk
  refine Polarized.ComparisonMarkedLevel.polarizedComparison_level_of_rational_labels D
    (fun v : P.lattice => Multiplicative.ofAdd (P.fixedLevelLabel hP N v)) ?_
    (fun v => M.nativeReferenceTestRationalMarking hM κ hP hκ (M.referencePoint hM κ hP hκ b) b
      (𝟙 (Over.mk (𝟙 Foundations.Scheme.ProjectiveSpace.complexBase))) (Category.id_comp _) v.val)
    (fun v => M.transportedNativeReferenceFieldMarking hM κ hP hκ f a H z₀ hz₀ z v.val)
    (N : ℝ)⁻¹ ?_ ?_ ?_ T c
  · intro t
    obtain ⟨v, hv⟩ := P.fixedLevelLabel_surjective hP N t.toAdd
    exact ⟨v, congrArg Multiplicative.ofAdd hv⟩
  · intro v
    exact (Polarized.ComparisonMarkedLevel.polarizedNativeLevelPoint_pullback
      (M.complexTestFamily κ (M.referencePoint hM κ hP hκ b)).polarized (𝟙 (Over.mk (𝟙 Foundations.Scheme.ProjectiveSpace.complexBase)))
      (Multiplicative.ofAdd (P.fixedLevelLabel hP N v))).trans
        (M.nativeReferenceTestRationalMarking_level hM κ hP hκ (M.referencePoint hM κ hP hκ b) b
          (𝟙 (Over.mk (𝟙 Foundations.Scheme.ProjectiveSpace.complexBase))) (Category.id_comp _) v)
  · intro v
    rw [Polarized.ComparisonMarkedLevel.polarizedNativeLevelPoint_pullback]
    exact M.transportedNativeReferenceFieldMarking_level hM κ hP hκ f a H z₀ hz₀ z v
  · intro v
    dsimp only [D]
    rw [M.nativeReferenceFiberPolarizedComparison_periods]
    exact M.nativeReferenceFiberComparison_marking hM κ hP hκ f a H z₀ hz₀ b z v.val

def Models.FinePELModel.nativeReferenceFiberLevelIso : HilbertConstruction.Moduli.Isomorphisms.LevelPreservingIso
    ((M.complexTestFamily κ (M.referencePoint hM κ hP hκ b)).polarized.pullback (𝟙 Foundations.Scheme.ProjectiveSpace.complexBase))
    ((M.complexTestFamily κ f).polarized.pullback (RepresentationTheory.Theta.Geometric.Intrinsic.FamilyFrames.familyChartParameter C z).left) :=
  (M.nativeReferenceFiberPolarizedComparison hM κ hP hκ f a H z₀ hz₀ b z hs hdegree hk).toLevelIso
    (M.nativeReferenceFiberPolarizedComparison_level hM κ hP hκ f a H z₀ hz₀ b z hs hdegree hk)

theorem Models.FinePELModel.nativeReferenceFiberLevelIso_action (c : NumberField.RingOfIntegers E) :
    ((M.complexTestFamily κ (M.referencePoint hM κ hP hκ b)).action.pullback (𝟙 Foundations.Scheme.ProjectiveSpace.complexBase)).map c ≫
      (M.nativeReferenceFiberLevelIso hM κ hP hκ f a H z₀ hz₀ b z hs hdegree hk).abelian.hom =
      (M.nativeReferenceFiberLevelIso hM κ hP hκ f a H z₀ hz₀ b z hs hdegree hk).abelian.hom ≫
        ((M.complexTestFamily κ f).action.pullback (RepresentationTheory.Theta.Geometric.Intrinsic.FamilyFrames.familyChartParameter C z).left).map c :=
  M.nativeReferenceFiberPolarizedComparison_action hM κ hP hκ f a H z₀ hz₀ b z hs hdegree hk c

end

/-! The complete reference-to-test PEL isomorphism identifies the actual
fine moduli point of each nearby original reference period. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

attribute [local implicit_reducible] Complex.BallPeriods.restrictComplexBase
attribute [local irreducible] Models.FinePELModel.complexTestFamily Models.FinePELModel.nativeReferenceFiberLevelIso

variable {E K : Type} [Field E] [NumberField E] [NumberField.IsCMField E] [IsGalois ℚ E]
    [Field K] {s N : ℕ} [NeZero N] {P : Datum.RankThreePELDatum E s} {iota : E →+* K}
    (M : Models.FinePELModel P iota N) (hM : M.IsFine) (κ : K →+* ℂ)
    (hP : P.IsAdmissible) (hκ : κ.comp iota = P.μ)
    {S : Over Foundations.Scheme.ProjectiveSpace.complexBase} (f : S ⟶ M.complexFiber κ) (a : P.domain)
    {x : ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints S}
    {C : PELModuli.CMPoints.IntrinsicFamilyCharts.NativeFamilyCharts (M.complexTestFamily κ f).polarized.abelian x}
    {F : RepresentationTheory.Theta.Geometric.Intrinsic.FamilyFrames.NativeFamilyPeriodFrame C}
    (H : Intrinsic.HolomorphicTransport.NativeFamilyHolomorphicTransport (M.complexTestFamily κ f).polarized
      (M.complexTestFamily κ f).action F)
    (z₀ : H.compatible.neighborhood)
    (hz₀ : RepresentationTheory.Theta.Geometric.Intrinsic.FamilyFrames.familyChartParameter C z₀ ≫ f = M.referencePoint hM κ hP hκ a)
    (b : P.domain) (z : H.compatible.neighborhood)
    (hs : 0 < s) (hdegree : Module.finrank ℚ E = 2 * s)
    (hk : (H.referenceMarkedMatrix P hP
      (M.transportedNativeReferenceLabel hM κ hP hκ f a H z₀ hz₀) z).ker =
        Submodule.span ℂ {Geometry.ComplexBall.PrescribedSignsB.lineVector b.val})

def Models.FinePELModel.nativeReferenceFiberPELIso :
    PEL.Objects.PELIso ((M.complexTestFamily κ (M.referencePoint hM κ hP hκ b)).pullback
      (Intrinsic.ComplexUniversal.complexPointRestriction κ (𝟙 (Over.mk (𝟙 Foundations.Scheme.ProjectiveSpace.complexBase)))))
      ((M.complexTestFamily κ f).pullback (Intrinsic.ComplexUniversal.complexPointRestriction κ (RepresentationTheory.Theta.Geometric.Intrinsic.FamilyFrames.familyChartParameter C z))) where
  polarized := M.nativeReferenceFiberLevelIso hM κ hP hκ f a H z₀ hz₀ b z hs hdegree hk
  action := M.nativeReferenceFiberLevelIso_action hM κ hP hκ f a H z₀ hz₀ b z hs hdegree hk

include hs hdegree hk in
theorem Models.FinePELModel.nativeReferenceFiber_moduli_point :
    RepresentationTheory.Theta.Geometric.Intrinsic.FamilyFrames.familyChartParameter C z ≫ f = M.referencePoint hM κ hP hκ b := by
  apply (M.complexPointClassEquiv κ hM).injective
  change (M.universal.pullback (M.complexPointBaseEquiv κ (RepresentationTheory.Theta.Geometric.Intrinsic.FamilyFrames.familyChartParameter C z ≫ f))).classOf =
    (M.universal.pullback (M.complexPointBaseEquiv κ (M.referencePoint hM κ hP hκ b))).classOf
  rw [← M.complexTestFamily_point_class κ f (RepresentationTheory.Theta.Geometric.Intrinsic.FamilyFrames.familyChartParameter C z)]
  have he : ((M.complexTestFamily κ f).pullback (Intrinsic.ComplexUniversal.complexPointRestriction κ (RepresentationTheory.Theta.Geometric.Intrinsic.FamilyFrames.familyChartParameter C z))).classOf =
      ((M.complexTestFamily κ (M.referencePoint hM κ hP hκ b)).pullback
        (Intrinsic.ComplexUniversal.complexPointRestriction κ (𝟙 (Over.mk (𝟙 Foundations.Scheme.ProjectiveSpace.complexBase))))).classOf :=
    Quotient.sound ⟨(M.nativeReferenceFiberPELIso hM κ hP hκ f a H z₀ hz₀ b z hs hdegree hk).symm⟩
  apply he.trans
  simpa only [Category.id_comp] using M.complexTestFamily_point_class κ
    (M.referencePoint hM κ hP hκ b) (𝟙 (Over.mk (𝟙 Foundations.Scheme.ProjectiveSpace.complexBase)))

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily
