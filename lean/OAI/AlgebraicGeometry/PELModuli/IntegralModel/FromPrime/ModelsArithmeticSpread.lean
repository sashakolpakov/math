import OAI.AlgebraicGeometry.PELModuli.IntegralModel.SmoothProjectiveFineSpread
import OAI.AlgebraicGeometry.PELModuli.IntegralModel.Arithmetic.PELComplexComparison
import OAI.AlgebraicGeometry.PELModuli.IntegralModel.FromPrime.ArithmeticReducedFineExistence
import OAI.AlgebraicGeometry.PELModuli.IntegralModel.FromPrime.ModelsReducedFineProjectivity

/-! # Models Arithmetic Spread -/

namespace OAI.AlgebraicGeometry.PELModuli.IntegralModel.FromPrime.ModelsArithmeticSpread

noncomputable section

/-! IntegralModel construction from actual arithmetic prime-level PEL models.
The original family, prescribed level, and full conclusion are retained. -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

namespace FromPrimeModels

theorem exists_smooth_projective_arithmetic_pel_spread
    (h43 : ReferenceFamily.ModuliInput)
    (hPresentations : Presentations.Hilbert.EndomorphismEquationsInput.{0})
    {E : Type} [Field E] [NumberField E] [Algebra ℚ E]
    [NumberField.IsCMField E] [IsGalois ℚ E]
    (s : ℕ) (hs : 0 < s) (hdegree : Module.finrank ℚ E = 2 * s)
    (P : AbelianModuli.ReferenceFamily.Datum.RankThreePELDatum E s) (hP : P.IsAdmissible)
    {K : Type} [Field K] [NumberField K] (iota : E →+* K) (κ : K →+* ℂ)
    (hemb : κ.comp iota = P.μ) (N : ℕ) (hN : 3 ≤ N)
    (M : AbelianModuli.ReferenceFamily.Models.FinePELModel P iota N) (hM : M.IsFine) [Arithmetic.PrimeModels.ArithmeticPrimePELModels P] :
    ∃ B : Base.ArithmeticBaseExtension K κ, IsUnit (N : B.R) ∧
      ∃ T : PEL.Has.IntegralPELSpread P iota κ N M.space M.universal B,
        T.IsReducedPELModuli P ∧ Smooth T.toOver.hom ∧ IsProper T.toOver.hom ∧
          Components.RelativelyProjective T.toOver := by
  obtain ⟨B, _, Q, hr, hn, hft, hqc, U, hU⟩ :=
    ArithmeticReducedFineExistence.FromPrimeModels.exists_arithmetic_reduced_fine_pel_model h43 hPresentations
      s hs hdegree P hP iota κ hemb N hN M hM
  have : IsReduced Q.left := hr
  have : IsNoetherian Q.left := hn
  have : LocallyOfFiniteType Q.hom := hft
  have : QuasiCompact Q.hom := hqc
  let T := Arithmetic.GenericFamilyComparison.integralPELSpreadOfFineModel B U M hU hM
  let e := T.complexReferenceIso
  obtain ⟨hsm, _⟩ := ModelsReducedFine.FromPrimeModels.reduced_finePEL_smooth_proper h43 hPresentations
    s hs hdegree P hP iota κ hemb N hN M hM
  have : Smooth (Reduction.reduction M.space).hom := hsm
  have : Smooth (Reduced.ReducedComplexPEL.reducedComplexPEL M κ).hom :=
    inferInstanceAs (Smooth (pullback.snd (Reduction.reduction M.space).hom (Spec.map (CommRingCat.ofHom κ))))
  have : IsIso e.hom.left := ((Over.forget Foundations.Scheme.ProjectiveSpace.complexBase).mapIso e).isIso_hom
  have : Smooth ((Over.pullback (Spec.map (CommRingCat.ofHom (B.embedding.comp B.toField)))).obj Q).hom := by
    change Smooth ((Over.pullback (Spec.map (CommRingCat.ofHom (B.embedding.comp B.toField)))).obj T.toOver).hom
    rw [← e.hom.w]
    infer_instance
  obtain ⟨PM⟩ := ModelsReducedFineProjectivity.FromPrimeModels.reduced_finePEL_complex_projective h43 hPresentations
    s hs hdegree P hP iota κ hemb N hN M hM
  let PQ : Foundations.Scheme.SmoothProjective.ProjectivePresentation
      ((Over.pullback (Spec.map (CommRingCat.ofHom (B.embedding.comp B.toField)))).obj Q).left
      ((Over.pullback (Spec.map (CommRingCat.ofHom (B.embedding.comp B.toField)))).obj Q).hom := {
    ambientDimension := PM.ambientDimension
    embedding := e.hom.left ≫ PM.embedding
    closedImmersion := inferInstanceAs (IsClosedImmersion (e.hom.left ≫ PM.embedding))
    over_base := by rw [Category.assoc, PM.over_base]; exact e.hom.w }
  exact SmoothProjectiveFineSpread.smooth_projective_arithmetic_fine_pel_spread B Q
    ⟨inferInstance, inferInstance, inferInstance⟩ U hU PQ (by omega) M hM

end FromPrimeModels

end

end OAI.AlgebraicGeometry.PELModuli.IntegralModel.FromPrime.ModelsArithmeticSpread
