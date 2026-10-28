import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.IdentityPEL
import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Reference.HeckeTargets

/-! # Target Realization -/

namespace OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.TargetRealization.Construction

noncomputable section

/-! Each independently defined raw target is realized by an actual
positive PEL quotient of the original source, with its exact raw kernel. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj BigOperators

variable {E K L : Type} [Field E] [NumberField E] [NumberField.IsCMField E] [IsGalois ℚ E]
  [Field K] [NumberField K] [CharZero K] [Field L] [NumberField L]
  {d N q : ℕ} [Fact q.Prime] {P : AbelianModuli.ReferenceFamily.Datum.RankThreePELDatum E d} {iota : E →+* K}
  {c : Foundations.Scheme.ProjectiveSpace.complexBase ⟶ Spec (.of K)} (A : AbelianModuli.ReferenceFamily.PEL.Objects.PELObject P iota N (Over.mk c))
  {κ : L →+* ℂ} (j : PELModuli.CMPoints.Arithmetic.QadicChoice L κ q) (arithmeticEmbedding : E →+* L)
  (hsplit : j.HasSplitCoordinates arithmeticEmbedding)
  (hd : 0 < d) (hdegree : Module.finrank ℚ E = 2 * d)
  (h : ℕ) (labels : ChoiceKernel.Construction.KernelIndex d ≃ Gal(E/ℚ))
  (M : Fin d → Type) [∀ v, AddCommGroup (M v)] [∀ v, Module (ZMod (q ^ h)) (M v)] [∀ v, Finite (M v)]
  (a : Fin d → Fin 3 → ℕ) (ha : ∀ v i, a v i ≤ h) (hdominant : ∀ v, Antitone (a v))
  (eM : ∀ v, M v ≃+ (∀ i, ZMod (q ^ a v i)))
  (hcop : Nat.Coprime q N) (hpol : Nat.Coprime (q ^ h) ((∏ i, P.polarizationType i) ^ 2))
  (hlabels : ∀ i, labels (Sum.swap i) = PELModuli.CMPoints.Arithmetic.rationalConjugation E * labels i)
  (h_FiniteDescent : IsogenyComplement.Construction.FiniteDescentInput.{0}) (Z : AbelianModuli.ReferenceFamily.Models.FinePELModel P iota N) (hZ : Z.IsFine)

theorem originalComplexRawTarget_realized
    (x : Hecke.Construction.rawRightCosetSupport (TateComparison.HeckeKernel.integralLevel d q) (TateComparison.HeckeKernel.representative d q (SplitHeckeChoices.Construction.naturalIntegralLocalType d h a hdominant))) :
    ∃ B : AbelianModuli.ReferenceFamily.PEL.Objects.PELObject P iota N (Over.mk c), ∃ f : Intrinsic.PELBaseChange.Construction.NativePELQuotient A B (q ^ h),
      FinePELTarget.Construction.finePELClassifyingMap Z hZ B =
        Reference.ComplexTarget.Construction.originalComplexRawTarget A j arithmeticEmbedding hsplit hd hdegree h labels M a ha hdominant eM
          hcop hpol hlabels h_FiniteDescent Z hZ x ∧
      ∀ (U : Over Foundations.Scheme.ProjectiveSpace.complexBase) (z : U ⟶ A.polarized.abelian.scheme),
        z ≫ f.isogeny.hom = 1 ↔ z ∈
          (Reference.ComplexTarget.Construction.originalComplexRawKernel A j arithmeticEmbedding hsplit hd hdegree h labels M a ha hdominant eM x).points U
            (Over.homMk U.hom (Category.comp_id U.hom)) := by
  let H := Reference.ComplexTarget.Construction.originalComplexRawKernel_quotient A j arithmeticEmbedding hsplit hd hdegree h labels M a ha hdominant eM
    hcop hpol hlabels h_FiniteDescent x
  exact ⟨_, H.identityQuotient, H.identityQuotient_classifies Z hZ, H.identityQuotient_kernel⟩

end

end OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.TargetRealization.Construction
