import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Intrinsic.PELTateAdapter
import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.PolarizedTupleChoices

/-! # Complex Choices -/

namespace OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Reference.ComplexChoices.Construction

noncomputable section

/-! Raw split cosets classify the original ReferenceFamily complex subgroup
choices. The integral block bases come from that actual polarized family. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj

variable {E K L : Type} [Field E] [NumberField E]
  [NumberField.IsCMField E] [IsGalois ℚ E] [Field K] [Field L] [NumberField L]
  {d N q : ℕ} [Fact q.Prime] {P : AbelianModuli.ReferenceFamily.Datum.RankThreePELDatum E d} {iota : E →+* K}
  {c : Foundations.Scheme.ProjectiveSpace.complexBase ⟶ Spec (.of K)} (A : AbelianModuli.ReferenceFamily.PEL.Objects.PELObject P iota N (Over.mk c))
  {κ : L →+* ℂ} (j : PELModuli.CMPoints.Arithmetic.QadicChoice L κ q) (arithmeticEmbedding : E →+* L)
  (hsplit : j.HasSplitCoordinates arithmeticEmbedding)
  (hd : 0 < d) (hdegree : Module.finrank ℚ E = 2 * d)
  (h : ℕ) (labels : ChoiceKernel.Construction.KernelIndex d ≃ Gal(E/ℚ))
  (M : Fin d → Type) [∀ v, AddCommGroup (M v)] [∀ v, Module (ZMod (q ^ h)) (M v)] [∀ v, Finite (M v)]
  (a : Fin d → Fin 3 → ℕ) (ha : ∀ v i, a v i ≤ h) (hdominant : ∀ v, Antitone (a v))
  (eM : ∀ v, M v ≃+ (∀ i, ZMod (q ^ a v i)))

theorem originalComplexPEL_isPEL : (Intrinsic.PELTateAdapter.Construction.nativePELTateFamily A).IsPEL P.polarizationType
    (NumberField.IsCMField.ringOfIntegersComplexConj E).toRingHom :=
  TateComparison.PEL.PELFamilyData.ofPolarized_isPEL A.polarized (TateComparison.PELAdapters.actionToEnd A.action) _
    ((TateComparison.PELAdapters.rosati_iff A.polarized A.action).mpr A.rosati)

set_option backward.isDefEq.respectTransparency false in
def originalComplexBlockRawChoices (v : Fin d) :
    SubgroupFunctor.Construction.SupportedChoice A.polarized.abelian.scheme (q ^ h) (M v)
      (A.action.map (j.projector arithmeticEmbedding hsplit h (labels (.inl v))))
      (Over.mk (𝟙 Foundations.Scheme.ProjectiveSpace.complexBase)) ≃
      Hecke.Construction.rawRightCosetSupport (BlockLatticeCosets.Construction.blockIntegralLevel q) (BlockHeckeChoices.Construction.blockDiagonal q (fun i => (a v i : ℤ))) := by
  have e := PolarizedChoices.Construction.polarizedSupportedRawChoices j arithmeticEmbedding hsplit d hd hdegree
    (Intrinsic.PELTateAdapter.Construction.nativePELTateFamily A) (originalComplexPEL_isPEL A) h (labels (.inl v)) (M v)
    (a v) (ha v) (hdominant v) (eM v)
  simpa only [Intrinsic.PELTateAdapter.Construction.nativePELTateFamily, TateComparison.PEL.PELFamilyData.ofPolarized, TateComparison.PELAdapters.actionFromEnd, TateComparison.PELAdapters.actionToEnd_schemeMap] using e

def originalComplexRawChoices :
    (∀ v, SubgroupFunctor.Construction.SupportedChoice A.polarized.abelian.scheme (q ^ h) (M v)
      (A.action.map (j.projector arithmeticEmbedding hsplit h (labels (.inl v))))
      (Over.mk (𝟙 Foundations.Scheme.ProjectiveSpace.complexBase))) ≃
      Hecke.Construction.rawRightCosetSupport (TateComparison.HeckeKernel.integralLevel d q) (TateComparison.HeckeKernel.representative d q (SplitHeckeChoices.Construction.naturalIntegralLocalType d h a hdominant)) :=
  (Equiv.piCongrRight fun v => originalComplexBlockRawChoices A j arithmeticEmbedding hsplit hd hdegree
    h labels M a ha hdominant eM v).trans
      (SplitHeckeChoices.Construction.splitRawBlockSupportEquiv d q (SplitHeckeChoices.Construction.naturalIntegralLocalType d h a hdominant)).symm

theorem originalComplexRawChoices_block
    (U : ∀ v, SubgroupFunctor.Construction.SupportedChoice A.polarized.abelian.scheme (q ^ h) (M v)
      (A.action.map (j.projector arithmeticEmbedding hsplit h (labels (.inl v))))
      (Over.mk (𝟙 Foundations.Scheme.ProjectiveSpace.complexBase))) (v : Fin d) :
    SplitHeckeChoices.Construction.splitRawBlockSupportEquiv d q (SplitHeckeChoices.Construction.naturalIntegralLocalType d h a hdominant)
      (originalComplexRawChoices A j arithmeticEmbedding hsplit hd hdegree h labels M a ha hdominant eM U) v =
      originalComplexBlockRawChoices A j arithmeticEmbedding hsplit hd hdegree h labels M a ha hdominant eM v (U v) := by
  exact congrFun ((SplitHeckeChoices.Construction.splitRawBlockSupportEquiv d q (SplitHeckeChoices.Construction.naturalIntegralLocalType d h a hdominant)).apply_symm_apply _) v

end

end OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Reference.ComplexChoices.Construction
