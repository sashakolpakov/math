import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.UniversalFunction.ParameterMultiset
import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.UniversalFunction.CanonicalCorrespondence
import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Reference.HeckeTargets

/-! # Correspondence -/

namespace OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.UniversalFunction.Correspondence.Construction

noncomputable section

/-! For a fine PEL model whose universal family has universal global functions the canonical finite etale
correspondence has exactly the independent raw integral Hecke multisets. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj BigOperators

variable {E K L : Type} [Field E] [NumberField E] [NumberField.IsCMField E] [IsGalois ℚ E]
  [Field K] [NumberField K] [CharZero K] [Field L] [NumberField L]
  {d N q : ℕ} [Fact q.Prime] {P : AbelianModuli.ReferenceFamily.Datum.RankThreePELDatum E d} {iota : E →+* K}
  (Z : AbelianModuli.ReferenceFamily.Models.FinePELModel P iota N) (hZ : Z.IsFine)
  (hA : GlobalFunctions.Construction.HasUniversalGlobalFunctions Z.universal.polarized.abelian.scheme)
  {κ : L →+* ℂ} (j : PELModuli.CMPoints.Arithmetic.QadicChoice L κ q) (arithmeticEmbedding : E →+* L)
  (hsplit : j.HasSplitCoordinates arithmeticEmbedding)
  (hd : 0 < d) (hdegree : Module.finrank ℚ E = 2 * d)
  (h : ℕ) (labels : ChoiceKernel.Construction.KernelIndex d ≃ Gal(E/ℚ))
  (hlabels : ∀ i, labels (Sum.swap i) = PELModuli.CMPoints.Arithmetic.rationalConjugation E * labels i)
  (a : Fin d → Fin 3 → ℕ) (ha : ∀ v i, a v i ≤ h) (hdominant : ∀ v, Antitone (a v))
  (hcop : Nat.Coprime q N) (hpol : Nat.Coprime q (∏ i, P.polarizationType i))
  (h_FiniteDescent : IsogenyComplement.Construction.FiniteDescentInput.{0})

include hA in
set_option backward.isDefEq.respectTransparency false in
theorem universalFunction_raw_hecke_correspondence :
    ∃ Q : Over Z.space.left, IsFinite Q.hom ∧ Etale Q.hom ∧
      ∃ f : IntrinsicFineTargetData.Construction.NativeFinePELTarget (Z.universal.pullback (TotalParameters.Construction.totalParameterSource Z.space Q)) (q ^ h) Z,
      ∀ (c : Foundations.Scheme.ProjectiveSpace.complexBase ⟶ Spec (.of K)) (x : Over.mk c ⟶ Z.space),
        ∃ hfin : Finite (CorrespondenceFibers.Construction.SourceFiber (TotalParameters.Construction.totalParameterSource Z.space Q) x),
          @CorrespondenceFibers.Construction.correspondenceFiberMultiset _ _ _ _ _ (TotalParameters.Construction.totalParameterSource Z.space Q) f.target x hfin =
            Reference.HeckeTargets.Construction.originalRawHeckeMultiset Z hZ j arithmeticEmbedding hsplit hd hdegree h labels hlabels
              a ha hdominant hcop hpol h_FiniteDescent x := by
  let M := fun v => ElementaryModules.Construction.RankThreeElementaryModule.{0} q (a v)
  let : ∀ v, Module (ZMod (q ^ h)) (M v) :=
    fun v => ElementaryModules.Construction.rankThreeElementaryModule_structure q h (a v) (ha v)
  have hp : Nat.Coprime (q ^ h) ((∏ i, P.polarizationType i) ^ 2) := (hpol.pow_right 2).pow_left h
  obtain ⟨Q, hQf, hQe, repr, R, f, hker⟩ :=
    CanonicalCorrespondence.Construction.universalFunction_canonical_fine_correspondence Z.universal hA q hcop h hp j arithmeticEmbedding hsplit
      labels hlabels M h_FiniteDescent Z hZ
  refine ⟨Q, hQf, hQe, f, ?_⟩
  intro c x
  let hfin := Relative.FiberEquiv.Construction.relativeParameterRawFiber_finite Z.universal x j arithmeticEmbedding hsplit h labels M
    hd hdegree a ha hdominant (fun _ => AddEquiv.ulift) Q repr
  refine ⟨hfin, ?_⟩
  exact ParameterMultiset.Construction.universalFunctionParameterFineTarget_multiset Z.universal hA x j arithmeticEmbedding hsplit h labels M
    hd hdegree a ha hdominant (fun _ => AddEquiv.ulift) Q repr hcop hp hlabels h_FiniteDescent Z hZ R f hker

end

end OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.UniversalFunction.Correspondence.Construction
