import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.UniversalFunction.ChoiceKernelBaseChange
import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Relative.ComplexChoices
import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Reference.ComplexTarget

/-! # Complex Kernel -/

namespace OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.UniversalFunction.ComplexKernel.Construction

noncomputable section

/-! The actual canonical kernel over a complex source point is exactly
the independently defined raw kernel indexed by its relative choices. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj

variable {E K L : Type} [Field E] [NumberField E] [NumberField.IsCMField E] [IsGalois ℚ E]
  [Field K] [CharZero K] [Field L] [NumberField L]
  {d N q : ℕ} [Fact q.Prime] {P : AbelianModuli.ReferenceFamily.Datum.RankThreePELDatum E d} {iota : E →+* K}
  {T : Over (Spec (.of K))} (A : AbelianModuli.ReferenceFamily.PEL.Objects.PELObject P iota N T)
  (hA : GlobalFunctions.Construction.HasUniversalGlobalFunctions A.polarized.abelian.scheme)
  {c : Foundations.Scheme.ProjectiveSpace.complexBase ⟶ Spec (.of K)} (x : Over.mk c ⟶ T)
  {κ : L →+* ℂ} (j : PELModuli.CMPoints.Arithmetic.QadicChoice L κ q) (arithmeticEmbedding : E →+* L)
  (hsplit : j.HasSplitCoordinates arithmeticEmbedding)
  (h : ℕ) (labels : ChoiceKernel.Construction.KernelIndex d ≃ Gal(E/ℚ))
  (M : Fin d → Type) [∀ v, AddCommGroup (M v)] [∀ v, Module (ZMod (q ^ h)) (M v)] [∀ v, Finite (M v)]

variable (hd : 0 < d) (hdegree : Module.finrank ℚ E = 2 * d)
  (a : Fin d → Fin 3 → ℕ) (ha : ∀ v i, a v i ≤ h) (hdominant : ∀ v, Antitone (a v))
  (eM : ∀ v, M v ≃+ (∀ i, ZMod (q ^ a v i)))

local instance universalFunctionComplexParameter_noetherian : IsLocallyNoetherian (Over.mk x.left).left :=
  inferInstanceAs (IsLocallyNoetherian Foundations.Scheme.ProjectiveSpace.complexBase)

local instance universalFunctionComplexSource_noetherian : IsLocallyNoetherian (Over.mk c).left :=
  inferInstanceAs (IsLocallyNoetherian Foundations.Scheme.ProjectiveSpace.complexBase)

set_option backward.isDefEq.respectTransparency false in
theorem universalFunctionCanonicalKernel_eq_originalRawKernel
    (U : ∀ v, SubgroupFunctor.Construction.SupportedChoice A.polarized.abelian.scheme (q ^ h) (M v)
      (A.action.map (j.projector arithmeticEmbedding hsplit h (labels (.inl v)))) (Over.mk x.left)) :
    Relative.ParameterBaseChange.Construction.relativeSubgroupOverParameter (Grp.mk A.polarized.abelian.scheme) (Over.mk x.left)
      (ChoiceKernelBaseChange.Construction.universalFunctionCMPointsChoiceKernel j arithmeticEmbedding hsplit A.polarized.abelian A.action A.polarized.dual
        A.polarized.polarization (GlobalFunctions.Construction.universalGlobalFunctions_of_finiteFlat_source A.polarized.polarization.isogeny.hom hA) h d labels M (Over.mk x.left) U) =
    Reference.ComplexTarget.Construction.originalComplexRawKernel (A.pullback x) j arithmeticEmbedding hsplit hd hdegree h labels M a ha hdominant eM
      (Relative.ComplexChoices.Construction.relativeComplexRawChoices A x j arithmeticEmbedding hsplit h labels M hd hdegree a ha hdominant eM U) := by
  let V := fun v => Parameter.SubgroupChoice.Construction.supportedChoiceOverParameter A.polarized.abelian (Over.mk x.left) (q ^ h) (M v)
    (A.action.map (j.projector arithmeticEmbedding hsplit h (labels (.inl v)))) (U v)
  have hU : (Reference.ComplexChoices.Construction.originalComplexRawChoices (A.pullback x) j arithmeticEmbedding hsplit hd hdegree h labels M a ha hdominant eM).symm
      (Relative.ComplexChoices.Construction.relativeComplexRawChoices A x j arithmeticEmbedding hsplit h labels M hd hdegree a ha hdominant eM U) = V := by
    rw [Relative.ComplexChoices.Construction.relativeComplexRawChoices_actual_parameter]
    exact (Reference.ComplexChoices.Construction.originalComplexRawChoices (A.pullback x) j arithmeticEmbedding hsplit hd hdegree h labels M a ha hdominant eM).symm_apply_apply V
  have hc := ChoiceKernelBaseChange.Construction.universalFunctionCMPointsChoiceKernel_parameterBaseChange j arithmeticEmbedding hsplit A.polarized.abelian A.action
    A.polarized.dual A.polarized.polarization (GlobalFunctions.Construction.universalGlobalFunctions_of_finiteFlat_source A.polarized.polarization.isogeny.hom hA) h d labels M (Over.mk x.left) U
  have hr : Reference.ComplexTarget.Construction.originalComplexRawKernel (A.pullback x) j arithmeticEmbedding hsplit hd hdegree h labels M a ha hdominant eM
      (Relative.ComplexChoices.Construction.relativeComplexRawChoices A x j arithmeticEmbedding hsplit h labels M hd hdegree a ha hdominant eM U) =
    ChoiceKernelBaseChange.Construction.universalFunctionCMPointsChoiceKernel j arithmeticEmbedding hsplit (A.pullback x).polarized.abelian (A.pullback x).action
      (A.pullback x).polarized.dual (A.pullback x).polarized.polarization ((GlobalFunctions.Construction.universalGlobalFunctions_of_finiteFlat_source A.polarized.polarization.isogeny.hom hA).pullback x.left) h d labels M (Over.mk (𝟙 Foundations.Scheme.ProjectiveSpace.complexBase)) V :=
    congrArg (fun W => ChoiceKernelBaseChange.Construction.universalFunctionCMPointsChoiceKernel j arithmeticEmbedding hsplit (A.pullback x).polarized.abelian (A.pullback x).action
      (A.pullback x).polarized.dual (A.pullback x).polarized.polarization ((GlobalFunctions.Construction.universalGlobalFunctions_of_finiteFlat_source A.polarized.polarization.isogeny.hom hA).pullback x.left) h d labels M (Over.mk (𝟙 Foundations.Scheme.ProjectiveSpace.complexBase)) W) hU
  exact hc.trans hr.symm

end

end OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.UniversalFunction.ComplexKernel.Construction
