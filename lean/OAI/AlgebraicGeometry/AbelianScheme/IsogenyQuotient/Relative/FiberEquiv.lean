import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Relative.ComplexChoices
import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.CorrespondenceFibers
import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Universal.Choices
import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.ChoiceMultisets

/-! # Fiber Equiv -/

namespace OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Relative.FiberEquiv.Construction

noncomputable section

/-! The actual geometric source fiber is indexed by the raw split
cosets of its original PEL source. Reindexing retains repeated target values. -/

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

variable (hd : 0 < d) (hdegree : Module.finrank ℚ E = 2 * d)
  (a : Fin d → Fin 3 → ℕ) (ha : ∀ v i, a v i ≤ h) (hdominant : ∀ v, Antitone (a v))
  (eM : ∀ v, M v ≃+ (∀ i, ZMod (q ^ a v i)))

variable (Q : Over T.left)
  (repr : (Parameter.Products.Construction.blockTupleFunctor d (fun v => SubgroupFunctor.Construction.supportedSubgroupFunctor A.polarized.abelian.scheme (q ^ h) (M v)
    (A.action.map (j.projector arithmeticEmbedding hsplit h (labels (.inl v)))))).RepresentableBy Q)

def relativeParameterRawFiberEquiv :
    CorrespondenceFibers.Construction.SourceFiber (TotalParameters.Construction.totalParameterSource T Q) x ≃
      Hecke.Construction.rawRightCosetSupport (TateComparison.HeckeKernel.integralLevel d q) (TateComparison.HeckeKernel.representative d q (SplitHeckeChoices.Construction.naturalIntegralLocalType d h a hdominant)) :=
  (TotalParameters.Construction.totalParameterFiberEquiv T Q _ repr (Over.mk c) x).trans
    ((Universal.Choices.Construction.blockTupleCoordinates d (fun v => SubgroupFunctor.Construction.supportedSubgroupFunctor A.polarized.abelian.scheme (q ^ h) (M v)
      (A.action.map (j.projector arithmeticEmbedding hsplit h (labels (.inl v))))) (.op (Over.mk x.left))).trans
        (ComplexChoices.Construction.relativeComplexRawChoices A x j arithmeticEmbedding hsplit h labels M hd hdegree a ha hdominant eM))

include A j arithmeticEmbedding hsplit h labels M hd hdegree a ha hdominant eM repr in
theorem relativeParameterRawFiber_finite : Finite (CorrespondenceFibers.Construction.SourceFiber (TotalParameters.Construction.totalParameterSource T Q) x) :=
  Finite.of_equiv _ (relativeParameterRawFiberEquiv A x j arithmeticEmbedding hsplit h labels M hd hdegree
    a ha hdominant eM Q repr).symm

theorem correspondence_multiset_via_raw_parameter (dst : TotalParameters.Construction.totalParameter T Q ⟶ T) :
    letI : Finite (CorrespondenceFibers.Construction.SourceFiber (TotalParameters.Construction.totalParameterSource T Q) x) :=
      relativeParameterRawFiber_finite A x j arithmeticEmbedding hsplit h labels M hd hdegree a ha hdominant eM Q repr
    CorrespondenceFibers.Construction.correspondenceFiberMultiset (TotalParameters.Construction.totalParameterSource T Q) dst x =
      ChoiceMultisets.Construction.rawSplitTargetMultiset d q (SplitHeckeChoices.Construction.naturalIntegralLocalType d h a hdominant)
        (fun y => ((relativeParameterRawFiberEquiv A x j arithmeticEmbedding hsplit h labels M hd hdegree
          a ha hdominant eM Q repr).symm y).val ≫ dst) := by
  let : Finite (CorrespondenceFibers.Construction.SourceFiber (TotalParameters.Construction.totalParameterSource T Q) x) :=
    relativeParameterRawFiber_finite A x j arithmeticEmbedding hsplit h labels M hd hdegree a ha hdominant eM Q repr
  exact CorrespondenceFibers.Construction.finiteTargetMultiset_reindex
    (relativeParameterRawFiberEquiv A x j arithmeticEmbedding hsplit h labels M hd hdegree a ha hdominant eM Q repr)
    (fun y : CorrespondenceFibers.Construction.SourceFiber (TotalParameters.Construction.totalParameterSource T Q) x => y.val ≫ dst)

end

end OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Relative.FiberEquiv.Construction
