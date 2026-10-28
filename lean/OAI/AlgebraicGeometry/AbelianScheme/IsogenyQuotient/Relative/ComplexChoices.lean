import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Reference.ComplexChoices
import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Geometric.ParameterChoiceComparison

/-! # Complex Choices -/

namespace OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Relative.ComplexChoices.Construction

noncomputable section

/-! Relative choices over an original complex moduli point are the raw
split cosets of the actual pulled-back PEL source. No Noetherian source
base is assumed in this classification. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj

variable {E K L : Type} [Field E] [NumberField E] [NumberField.IsCMField E] [IsGalois ℚ E]
  [Field K] [CharZero K] [Field L] [NumberField L]
  {d N q : ℕ} [Fact q.Prime] {P : AbelianModuli.ReferenceFamily.Datum.RankThreePELDatum E d} {iota : E →+* K}
  {T : Over (Spec (.of K))} (A : AbelianModuli.ReferenceFamily.PEL.Objects.PELObject P iota N T)
  {c : Foundations.Scheme.ProjectiveSpace.complexBase ⟶ Spec (.of K)} (x : Over.mk c ⟶ T)
  {κ : L →+* ℂ} (j : PELModuli.CMPoints.Arithmetic.QadicChoice L κ q) (arithmeticEmbedding : E →+* L)
  (hsplit : j.HasSplitCoordinates arithmeticEmbedding)
  (h : ℕ) (labels : ChoiceKernel.Construction.KernelIndex d ≃ Gal(E/ℚ))
  (M : Fin d → Type) [∀ v, AddCommGroup (M v)] [∀ v, Module (ZMod (q ^ h)) (M v)] [∀ v, Finite (M v)]

set_option backward.isDefEq.respectTransparency false in
def relativeComplexBlockChoiceEquiv (v : Fin d) :
    SubgroupFunctor.Construction.SupportedChoice A.polarized.abelian.scheme (q ^ h) (M v)
      (A.action.map (j.projector arithmeticEmbedding hsplit h (labels (.inl v)))) (Over.mk x.left) ≃
    SubgroupFunctor.Construction.SupportedChoice (A.pullback x).polarized.abelian.scheme (q ^ h) (M v)
      ((A.pullback x).action.map (j.projector arithmeticEmbedding hsplit h (labels (.inl v))))
      (Over.mk (𝟙 Foundations.Scheme.ProjectiveSpace.complexBase)) :=
  (Geometric.ChoicesFromTorsion.Construction.geometricSupportedBaseChangeFromTorsionQuotient T.hom A.polarized.abelian
    (A.action.map (j.projector arithmeticEmbedding hsplit h (labels (.inl v))))
    (q ^ h) (pow_pos (Fact.out : q.Prime).pos h) ℂ x.left (M v)).symm

variable (hd : 0 < d) (hdegree : Module.finrank ℚ E = 2 * d)
  (a : Fin d → Fin 3 → ℕ) (ha : ∀ v i, a v i ≤ h) (hdominant : ∀ v, Antitone (a v))
  (eM : ∀ v, M v ≃+ (∀ i, ZMod (q ^ a v i)))

def relativeComplexRawChoices :
    (∀ v, SubgroupFunctor.Construction.SupportedChoice A.polarized.abelian.scheme (q ^ h) (M v)
      (A.action.map (j.projector arithmeticEmbedding hsplit h (labels (.inl v)))) (Over.mk x.left)) ≃
    Hecke.Construction.rawRightCosetSupport (TateComparison.HeckeKernel.integralLevel d q) (TateComparison.HeckeKernel.representative d q (SplitHeckeChoices.Construction.naturalIntegralLocalType d h a hdominant)) :=
  (Equiv.piCongrRight fun v => relativeComplexBlockChoiceEquiv A x j arithmeticEmbedding hsplit h labels M v).trans
    (Reference.ComplexChoices.Construction.originalComplexRawChoices (A.pullback x) j arithmeticEmbedding hsplit hd hdegree h labels M a ha hdominant eM)

set_option backward.isDefEq.respectTransparency false in
theorem relativeComplexRawChoices_actual_parameter
    (U : ∀ v, SubgroupFunctor.Construction.SupportedChoice A.polarized.abelian.scheme (q ^ h) (M v)
      (A.action.map (j.projector arithmeticEmbedding hsplit h (labels (.inl v)))) (Over.mk x.left)) :
    relativeComplexRawChoices A x j arithmeticEmbedding hsplit h labels M hd hdegree a ha hdominant eM U =
      Reference.ComplexChoices.Construction.originalComplexRawChoices (A.pullback x) j arithmeticEmbedding hsplit hd hdegree h labels M a ha hdominant eM
        (fun v => Parameter.SubgroupChoice.Construction.supportedChoiceOverParameter A.polarized.abelian (Over.mk x.left) (q ^ h) (M v)
          (A.action.map (j.projector arithmeticEmbedding hsplit h (labels (.inl v)))) (U v)) := by
  apply congrArg (Reference.ComplexChoices.Construction.originalComplexRawChoices (A.pullback x) j arithmeticEmbedding hsplit hd hdegree h labels M a ha hdominant eM)
  funext v
  exact Geometric.ParameterChoiceComparison.Construction.geometricSupportedBaseChange_inverse T.hom A.polarized.abelian
    (A.action.map (j.projector arithmeticEmbedding hsplit h (labels (.inl v))))
    (q ^ h) (pow_pos (Fact.out : q.Prime).pos h) (M v) ℂ x.left (U v)

end

end OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Relative.ComplexChoices.Construction
