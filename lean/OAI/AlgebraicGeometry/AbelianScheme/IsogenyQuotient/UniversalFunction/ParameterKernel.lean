import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.UniversalFunction.ComplexKernel
import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Relative.FiberEquiv

/-! # Parameter Kernel -/

namespace OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.UniversalFunction.ParameterKernel.Construction

noncomputable section

/-! The universal chosen-and-opposite kernel specializes to the
independent raw kernel at exactly the raw index of the source-fiber point. -/

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

variable (Q : Over T.left)
  (repr : (Parameter.Products.Construction.blockTupleFunctor d (fun v => SubgroupFunctor.Construction.supportedSubgroupFunctor A.polarized.abelian.scheme (q ^ h) (M v)
    (A.action.map (j.projector arithmeticEmbedding hsplit h (labels (.inl v)))))).RepresentableBy Q)

set_option backward.isDefEq.respectTransparency false in
theorem universalFunctionUniversalKernel_at_rawFiber
    (y : CorrespondenceFibers.Construction.SourceFiber (TotalParameters.Construction.totalParameterSource T Q) x) :
    Relative.ParameterBaseChange.Construction.relativeSubgroupOverParameter (Grp.mk A.polarized.abelian.scheme) (Over.mk x.left)
      ((ChoiceKernelBaseChange.Construction.universalFunctionCMPointsChoiceKernel j arithmeticEmbedding hsplit A.polarized.abelian A.action
        A.polarized.dual A.polarized.polarization (GlobalFunctions.Construction.universalGlobalFunctions_of_finiteFlat_source A.polarized.polarization.isogeny.hom hA) h d labels M Q
          (Universal.Choices.Construction.universalBlockChoice (q ^ h) d M
            (CM.PointsIntrinsicFamily.Construction.l45ChosenProjectors j arithmeticEmbedding hsplit A.polarized.abelian A.action h d labels) repr)).baseChange
        (TotalParameters.Construction.totalParameterFiberLiftEquiv T Q (Over.mk c) x y)) =
    Reference.ComplexTarget.Construction.originalComplexRawKernel (A.pullback x) j arithmeticEmbedding hsplit hd hdegree h labels M a ha hdominant eM
      (Relative.FiberEquiv.Construction.relativeParameterRawFiberEquiv A x j arithmeticEmbedding hsplit h labels M hd hdegree
        a ha hdominant eM Q repr y) := by
  let p := CM.PointsIntrinsicFamily.Construction.l45ChosenProjectors j arithmeticEmbedding hsplit A.polarized.abelian A.action h d labels
  let r := CM.PointsIntrinsicFamily.Construction.l45OppositeProjectors j arithmeticEmbedding hsplit A.polarized.abelian A.action h d labels
  let ep := CM.PointsPerfectKernel.Construction.l45SourceBlockPairing j arithmeticEmbedding hsplit A.polarized.abelian A.action h d labels
    (PolarizationAdapter.Construction.universalFunctionNativePolarizationPairing A.polarized.abelian A.polarized.dual A.polarized.polarization (GlobalFunctions.Construction.universalGlobalFunctions_of_finiteFlat_source A.polarized.polarization.isogeny.hom hA)
      (q ^ h) (pow_pos (Fact.out : q.Prime).pos h))
  let b := TotalParameters.Construction.totalParameterFiberLiftEquiv T Q (Over.mk c) x y
  let U := Universal.Choices.Construction.blockTupleCoordinates d (fun v => SubgroupFunctor.Construction.supportedSubgroupFunctor A.polarized.abelian.scheme
    (q ^ h) (M v) (p v)) (.op (Over.mk x.left)) (repr.homEquiv b)
  have hc := Universal.KernelQuotient.Construction.classified_full_kernel_is_pullback (q ^ h) d M p r ep repr b
  exact (congrArg (Relative.ParameterBaseChange.Construction.relativeSubgroupOverParameter (Grp.mk A.polarized.abelian.scheme) (Over.mk x.left)) hc.symm).trans
    (ComplexKernel.Construction.universalFunctionCanonicalKernel_eq_originalRawKernel A hA x j arithmeticEmbedding hsplit h labels M hd hdegree
      a ha hdominant eM U)

end

end OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.UniversalFunction.ParameterKernel.Construction
