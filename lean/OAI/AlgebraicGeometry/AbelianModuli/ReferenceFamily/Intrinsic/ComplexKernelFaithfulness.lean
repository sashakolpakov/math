import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Intrinsic.ComplexUniversal
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Family.KernelPELIso

/-! # Complex Kernel Faithfulness -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily

noncomputable section

/-! Equal distinguished native period kernels determine the point of
the actual fine PEL model, without a geometric hypothesis on that model. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

attribute [local irreducible] Models.FinePELModel.complexTestFamily

variable {E K : Type} [Field E] [NumberField E] [NumberField.IsCMField E] [IsGalois ℚ E]
    [Field K] {s N : ℕ} {P : Datum.RankThreePELDatum E s} {iota : E →+* K}
    (M : Models.FinePELModel P iota N) (hM : M.IsFine) (κ : K →+* ℂ) (hκ : κ.comp iota = P.μ)
    {S : Over Foundations.Scheme.ProjectiveSpace.complexBase} (f : S ⟶ M.complexFiber κ) {x : ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints S}
    {C : PELModuli.CMPoints.IntrinsicFamilyCharts.NativeFamilyCharts (M.complexTestFamily κ f).polarized.abelian x}
    {F : RepresentationTheory.Theta.Geometric.Intrinsic.FamilyFrames.NativeFamilyPeriodFrame C}
    (H : Intrinsic.HolomorphicTransport.NativeFamilyHolomorphicTransport (M.complexTestFamily κ f).polarized (M.complexTestFamily κ f).action F)

include hM hκ in
theorem Models.FinePELModel.point_eq_of_native_embeddingKernel_eq
    (hs : 0 < s) (hdegree : Module.finrank ℚ E = 2 * s) (hP : P.IsAdmissible)
    (e₀ : Geometry.ComplexBall.PrescribedSignsB.Vec ≃ₗ[ℂ] Geometry.ComplexBall.PrescribedSignsB.Vec) (z w : H.compatible.neighborhood)
    (heq : (H.embeddingMatrix s hs rfl hdegree (P.embeddings P.distinguished) e₀ z).ker =
      (H.embeddingMatrix s hs rfl hdegree (P.embeddings P.distinguished) e₀ w).ker) :
    RepresentationTheory.Theta.Geometric.Intrinsic.FamilyFrames.familyChartParameter C z ≫ f = RepresentationTheory.Theta.Geometric.Intrinsic.FamilyFrames.familyChartParameter C w ≫ f := by
  let A := M.complexTestFamily κ f
  have hcompact (i : Fin s) (hi : i ≠ P.distinguished) :
      ∃ r, (r = 0 ∨ r = 3) ∧
        LieRanks.HasLieRank (A.polarized.abelian.pullback (RepresentationTheory.Theta.Geometric.Intrinsic.FamilyFrames.familyChartParameter C z).left)
          (A.action.pullback (RepresentationTheory.Theta.Geometric.Intrinsic.FamilyFrames.familyChartParameter C z).left)
          ((P.embeddings i).toRingHom.comp (algebraMap (NumberField.RingOfIntegers E) E)) r ∧
        LieRanks.HasLieRank (A.polarized.abelian.pullback (RepresentationTheory.Theta.Geometric.Intrinsic.FamilyFrames.familyChartParameter C w).left)
          (A.action.pullback (RepresentationTheory.Theta.Geometric.Intrinsic.FamilyFrames.familyChartParameter C w).left)
          ((P.embeddings i).toRingHom.comp (algebraMap (NumberField.RingOfIntegers E) E)) r := by
    refine ⟨P.firstLieRank i, ?_, ?_, ?_⟩
    · unfold Datum.RankThreePELDatum.firstLieRank
      rw [ite_eq_right hi]
      split <;> simp
    · exact A.complexFiber_embedding_rank κ hκ (RepresentationTheory.Theta.Geometric.Intrinsic.FamilyFrames.familyChartParameter C z).left
        (Complex.BallPeriods.restrictComplexBase_point κ (RepresentationTheory.Theta.Geometric.Intrinsic.FamilyFrames.familyChartParameter C z)) hP i
    · exact A.complexFiber_embedding_rank κ hκ (RepresentationTheory.Theta.Geometric.Intrinsic.FamilyFrames.familyChartParameter C w).left
        (Complex.BallPeriods.restrictComplexBase_point κ (RepresentationTheory.Theta.Geometric.Intrinsic.FamilyFrames.familyChartParameter C w)) hP i
  have hξ := (Datum.RankThreePELDatum.normalizedImaginaryScalar_spec hP).1
  let e := H.levelIsoOfEmbeddingKernel s hs rfl hdegree A.rosati P.normalizedImaginaryScalar hξ
    P.embeddings P.distinguished hP.1.2 e₀ z w heq hcompact
  let p : PEL.Objects.PELIso (A.pullback (Intrinsic.ComplexUniversal.complexPointRestriction κ (RepresentationTheory.Theta.Geometric.Intrinsic.FamilyFrames.familyChartParameter C z)))
      (A.pullback (Intrinsic.ComplexUniversal.complexPointRestriction κ (RepresentationTheory.Theta.Geometric.Intrinsic.FamilyFrames.familyChartParameter C w))) := {
    polarized := e
    action := H.levelIsoOfEmbeddingKernel_action s hs rfl hdegree A.rosati P.normalizedImaginaryScalar hξ
      P.embeddings P.distinguished hP.1.2 e₀ z w heq hcompact }
  exact M.point_eq_of_complexTestFamily_iso κ f hM (RepresentationTheory.Theta.Geometric.Intrinsic.FamilyFrames.familyChartParameter C z) (RepresentationTheory.Theta.Geometric.Intrinsic.FamilyFrames.familyChartParameter C w) p

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily
