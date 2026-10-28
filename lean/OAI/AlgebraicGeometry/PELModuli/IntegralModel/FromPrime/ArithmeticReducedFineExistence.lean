import OAI.AlgebraicGeometry.PELModuli.IntegralModel.FromPrime.ArithmeticAbelianPairExistence
import OAI.AlgebraicGeometry.PELModuli.IntegralModel.Arithmetic.ReducedFine

/-! # Arithmetic Reduced Fine Existence -/

namespace OAI.AlgebraicGeometry.PELModuli.IntegralModel.FromPrime.ArithmeticReducedFineExistence

noncomputable section

/-! IntegralModel construction from actual arithmetic prime-level PEL models.
The original family, prescribed level, and full conclusion are retained. -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

namespace FromPrimeModels

theorem exists_arithmetic_reduced_fine_pel_model
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
      ∃ Q : Over B.base, IsReduced Q.left ∧ IsNoetherian Q.left ∧
        LocallyOfFiniteType Q.hom ∧ QuasiCompact Q.hom ∧
        ∃ U : PEL.Has.IntegralPELObject P B.R (B.integralEmbedding iota) N Q,
          ∀ (T : Over B.base) [IsReduced T.left]
            (A : PEL.Has.IntegralPELObject P B.R (B.integralEmbedding iota) N T),
            ∃! f : T ⟶ Q, Nonempty (PEL.Iso.PolarizedActionIso (U.pullback f).data A.data) := by
  obtain ⟨B, hNB, p, hp, _, _, _, hpB, V, hr, hn, _, _, _,
      U, hU, hrigid, _, Q, π, _, _, hftQ, hqcQ, hf, ht, hsπ, hk, _,
      D, _, φ, hφ, ⟨A⟩⟩ :=
    ArithmeticAbelianPairExistence.FromPrimeModels.exists_arithmetic_pel_quotient_with_abelian_pair h43 hPresentations
      s hs hdegree P hP iota κ hemb N hN M hM
  have : Fact p.Prime := ⟨hp⟩
  have : IsReduced V.left := hr
  have : IsNoetherian V.left := hn
  have : LocallyOfFiniteType Q.hom := hftQ
  have : QuasiCompact Q.hom := hqcQ
  have : IsFinite π.left := hf
  have : Etale π.left := ht
  have : Surjective π.left := hsπ
  let b := Spec.map (CommRingCat.ofHom φ)
  let Q' := (Over.pullback b).obj Q
  have : IsNoetherian Q'.left := Arithmetic.ReducedFamily.arithmetic_scalar_parameter_isNoetherian B D φ
  have : LocallyOfFiniteType Q'.hom := inferInstanceAs (LocallyOfFiniteType (pullback.snd Q.hom b))
  have : QuasiCompact Q'.hom := inferInstanceAs (QuasiCompact (pullback.snd Q.hom b))
  have hn' : IsNoetherian (Reduction.reduction Q').left := PrescribedAbelian.PairReducedObject.reduction_isNoetherian Q'
  have hft' : LocallyOfFiniteType (Reduction.reduction Q').hom :=
    inferInstanceAs (LocallyOfFiniteType ((Reduction.reductionι Q').left ≫ Q'.hom))
  have hqc' : QuasiCompact (Reduction.reduction Q').hom :=
    inferInstanceAs (QuasiCompact ((Reduction.reductionι Q').left ≫ Q'.hom))
  have hND : IsUnit (N : (B.compose D).R) := by
    change IsUnit (N : D.R)
    simpa only [map_natCast] using hNB.map φ
  exact ⟨B.compose D, hND, Reduction.reduction Q', Reduction.reduction_reduced Q', hn', hft', hqc',
    Arithmetic.ReducedFamily.arithmetic_reduced_pel_family B D φ hφ A hrigid,
    Arithmetic.ReducedFine.arithmetic_reduced_pel_family_classifies B D φ hφ A hrigid hp hpB⟩

end FromPrimeModels

end

end OAI.AlgebraicGeometry.PELModuli.IntegralModel.FromPrime.ArithmeticReducedFineExistence
