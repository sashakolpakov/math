import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.UniversalFunction.ParameterKernel
import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.CompositeParameterPoints
import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.TargetDetermination

/-! # Parameter Multiset -/

namespace OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.UniversalFunction.ParameterMultiset.Construction

noncomputable section

section

/-! The actual fine target at each source-fiber point equals the
independently constructed raw target of its original complex PEL source. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj BigOperators

variable {E K L : Type} [Field E] [NumberField E] [NumberField.IsCMField E] [IsGalois ℚ E]
  [Field K] [NumberField K] [CharZero K] [Field L] [NumberField L]
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

variable
  (hcop : Nat.Coprime q N) (hpol : Nat.Coprime (q ^ h) ((∏ i, P.polarizationType i) ^ 2))
  (hlabels : ∀ i, labels (Sum.swap i) = PELModuli.CMPoints.Arithmetic.rationalConjugation E * labels i)
  (h_FiniteDescent : IsogenyComplement.Construction.FiniteDescentInput.{0}) (Z : AbelianModuli.ReferenceFamily.Models.FinePELModel P iota N) (hZ : Z.IsFine)

variable (R : (ChoiceKernelBaseChange.Construction.universalFunctionCMPointsChoiceKernel j arithmeticEmbedding hsplit A.polarized.abelian A.action
  A.polarized.dual A.polarized.polarization (GlobalFunctions.Construction.universalGlobalFunctions_of_finiteFlat_source A.polarized.polarization.isogeny.hom hA) h d labels M Q
    (Universal.Choices.Construction.universalBlockChoice (q ^ h) d M
      (CM.PointsIntrinsicFamily.Construction.l45ChosenProjectors j arithmeticEmbedding hsplit A.polarized.abelian A.action h d labels) repr)).Model)
  (f : IntrinsicFineTargetData.Construction.NativeFinePELTarget (A.pullback (TotalParameters.Construction.totalParameterSource T Q)) (q ^ h) Z)
  (hker : ∀ (U : Over (TotalParameters.Construction.totalParameter T Q).left)
    (z : U ⟶ (A.polarized.abelian.pullback Q.hom).scheme),
    z ≫ f.isogeny.hom = 1 ↔ ∃! w : U ⟶ (Subgroup.Construction.subgroupGroupScheme (ChoiceKernelBaseChange.Construction.universalFunctionCMPointsChoiceKernel j arithmeticEmbedding hsplit A.polarized.abelian A.action
  A.polarized.dual A.polarized.polarization (GlobalFunctions.Construction.universalGlobalFunctions_of_finiteFlat_source A.polarized.polarization.isogeny.hom hA) h d labels M Q
    (Universal.Choices.Construction.universalBlockChoice (q ^ h) d M
      (CM.PointsIntrinsicFamily.Construction.l45ChosenProjectors j arithmeticEmbedding hsplit A.polarized.abelian A.action h d labels) repr)) R).X,
      w ≫ Intrinsic.Stability.Construction.nativeSubgroupInclusion A.polarized.abelian Q (ChoiceKernelBaseChange.Construction.universalFunctionCMPointsChoiceKernel j arithmeticEmbedding hsplit A.polarized.abelian A.action
  A.polarized.dual A.polarized.polarization (GlobalFunctions.Construction.universalGlobalFunctions_of_finiteFlat_source A.polarized.polarization.isogeny.hom hA) h d labels M Q
    (Universal.Choices.Construction.universalBlockChoice (q ^ h) d M
      (CM.PointsIntrinsicFamily.Construction.l45ChosenProjectors j arithmeticEmbedding hsplit A.polarized.abelian A.action h d labels) repr)) R = z)

include hker in
set_option backward.isDefEq.respectTransparency false in
theorem universalFunctionParameterFineTarget_eq_raw (y : CorrespondenceFibers.Construction.SourceFiber (TotalParameters.Construction.totalParameterSource T Q) x) :
    y.val ≫ f.target =
      Reference.ComplexTarget.Construction.originalComplexRawTarget (A.pullback x) j arithmeticEmbedding hsplit hd hdegree h labels M a ha hdominant eM
        hcop hpol hlabels h_FiniteDescent Z hZ
        (Relative.FiberEquiv.Construction.relativeParameterRawFiberEquiv A x j arithmeticEmbedding hsplit h labels M hd hdegree
          a ha hdominant eM Q repr y) := by
  let r := f.toQuotient.pullbackCompositeSource A (TotalParameters.Construction.totalParameterSource T Q) y.val x y.property
  have he := ParameterKernel.Construction.universalFunctionUniversalKernel_at_rawFiber A hA x j arithmeticEmbedding hsplit h labels M hd hdegree
    a ha hdominant eM Q repr y
  have hk : ∀ (U : Over Foundations.Scheme.ProjectiveSpace.complexBase) (z : U ⟶ (A.pullback x).polarized.abelian.scheme),
      z ≫ r.isogeny.hom = 1 ↔ z ∈
        (Reference.ComplexTarget.Construction.originalComplexRawKernel (A.pullback x) j arithmeticEmbedding hsplit hd hdegree h labels M a ha hdominant eM
          (Relative.FiberEquiv.Construction.relativeParameterRawFiberEquiv A x j arithmeticEmbedding hsplit h labels M hd hdegree
            a ha hdominant eM Q repr y)).points U (Over.homMk U.hom (Category.comp_id U.hom)) := by
    intro U z
    let t : U ⟶ Over.mk (𝟙 Foundations.Scheme.ProjectiveSpace.complexBase) := Over.homMk U.hom (Category.comp_id U.hom)
    exact (CompositeParameterPoints.Construction.sourceFiberQuotient_kernel A Q (ChoiceKernelBaseChange.Construction.universalFunctionCMPointsChoiceKernel j arithmeticEmbedding hsplit A.polarized.abelian A.action
  A.polarized.dual A.polarized.polarization (GlobalFunctions.Construction.universalGlobalFunctions_of_finiteFlat_source A.polarized.polarization.isogeny.hom hA) h d labels M Q
    (Universal.Choices.Construction.universalBlockChoice (q ^ h) d M
      (CM.PointsIntrinsicFamily.Construction.l45ChosenProjectors j arithmeticEmbedding hsplit A.polarized.abelian A.action h d labels) repr)) R f.toQuotient hker y.val x y.property U z t).trans
      (iff_of_eq (congrArg (fun H => z ∈ H.points U t) he))
  have ht : FinePELTarget.Construction.finePELClassifyingMap Z hZ ((Z.universal.pullback f.target).pullback y.val) = y.val ≫ f.target :=
    (FinePELPolarization.Construction.finePELClassifyingMap_pullback Z hZ (Z.universal.pullback f.target) y.val).trans
      (congrArg (y.val ≫ ·) (FinePELTarget.Construction.finePELClassifyingMap_unique Z hZ (Z.universal.pullback f.target)
        f.target ⟨AbelianModuli.ReferenceFamily.Models.PELPullbackIso.canonical Z.universal f.target⟩).symm)
  exact ht.symm.trans (TargetDetermination.Construction.originalComplexRawQuotient_target_eq_of_kernel (A.pullback x) j arithmeticEmbedding hsplit
    hd hdegree h labels M a ha hdominant eM hcop hpol hlabels h_FiniteDescent Z hZ _ r hk)

end

/-! Every point of the actual source fiber contributes the independent
raw target once. Distinct kernels with equal targets retain their multiplicity. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj BigOperators

variable {E K L : Type} [Field E] [NumberField E] [NumberField.IsCMField E] [IsGalois ℚ E]
  [Field K] [NumberField K] [CharZero K] [Field L] [NumberField L]
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

variable
  (hcop : Nat.Coprime q N) (hpol : Nat.Coprime (q ^ h) ((∏ i, P.polarizationType i) ^ 2))
  (hlabels : ∀ i, labels (Sum.swap i) = PELModuli.CMPoints.Arithmetic.rationalConjugation E * labels i)
  (h_FiniteDescent : IsogenyComplement.Construction.FiniteDescentInput.{0}) (Z : AbelianModuli.ReferenceFamily.Models.FinePELModel P iota N) (hZ : Z.IsFine)

variable (R : (ChoiceKernelBaseChange.Construction.universalFunctionCMPointsChoiceKernel j arithmeticEmbedding hsplit A.polarized.abelian A.action
  A.polarized.dual A.polarized.polarization (GlobalFunctions.Construction.universalGlobalFunctions_of_finiteFlat_source A.polarized.polarization.isogeny.hom hA) h d labels M Q
    (Universal.Choices.Construction.universalBlockChoice (q ^ h) d M
      (CM.PointsIntrinsicFamily.Construction.l45ChosenProjectors j arithmeticEmbedding hsplit A.polarized.abelian A.action h d labels) repr)).Model)
  (f : IntrinsicFineTargetData.Construction.NativeFinePELTarget (A.pullback (TotalParameters.Construction.totalParameterSource T Q)) (q ^ h) Z)
  (hker : ∀ (U : Over (TotalParameters.Construction.totalParameter T Q).left)
    (z : U ⟶ (A.polarized.abelian.pullback Q.hom).scheme),
    z ≫ f.isogeny.hom = 1 ↔ ∃! w : U ⟶ (Subgroup.Construction.subgroupGroupScheme (ChoiceKernelBaseChange.Construction.universalFunctionCMPointsChoiceKernel j arithmeticEmbedding hsplit A.polarized.abelian A.action
  A.polarized.dual A.polarized.polarization (GlobalFunctions.Construction.universalGlobalFunctions_of_finiteFlat_source A.polarized.polarization.isogeny.hom hA) h d labels M Q
    (Universal.Choices.Construction.universalBlockChoice (q ^ h) d M
      (CM.PointsIntrinsicFamily.Construction.l45ChosenProjectors j arithmeticEmbedding hsplit A.polarized.abelian A.action h d labels) repr)) R).X,
      w ≫ Intrinsic.Stability.Construction.nativeSubgroupInclusion A.polarized.abelian Q (ChoiceKernelBaseChange.Construction.universalFunctionCMPointsChoiceKernel j arithmeticEmbedding hsplit A.polarized.abelian A.action
  A.polarized.dual A.polarized.polarization (GlobalFunctions.Construction.universalGlobalFunctions_of_finiteFlat_source A.polarized.polarization.isogeny.hom hA) h d labels M Q
    (Universal.Choices.Construction.universalBlockChoice (q ^ h) d M
      (CM.PointsIntrinsicFamily.Construction.l45ChosenProjectors j arithmeticEmbedding hsplit A.polarized.abelian A.action h d labels) repr)) R = z)

include hker in
theorem universalFunctionParameterFineTarget_multiset :
    letI : Finite (CorrespondenceFibers.Construction.SourceFiber (TotalParameters.Construction.totalParameterSource T Q) x) :=
      Relative.FiberEquiv.Construction.relativeParameterRawFiber_finite A x j arithmeticEmbedding hsplit h labels M hd hdegree a ha hdominant eM Q repr
    CorrespondenceFibers.Construction.finiteTargetMultiset (fun y : CorrespondenceFibers.Construction.SourceFiber (TotalParameters.Construction.totalParameterSource T Q) x => y.val ≫ f.target) =
      ChoiceMultisets.Construction.rawSplitTargetMultiset d q (SplitHeckeChoices.Construction.naturalIntegralLocalType d h a hdominant)
        (Reference.ComplexTarget.Construction.originalComplexRawTarget (A.pullback x) j arithmeticEmbedding hsplit hd hdegree h labels M a ha hdominant eM
          hcop hpol hlabels h_FiniteDescent Z hZ) := by
  let : Finite (CorrespondenceFibers.Construction.SourceFiber (TotalParameters.Construction.totalParameterSource T Q) x) :=
    Relative.FiberEquiv.Construction.relativeParameterRawFiber_finite A x j arithmeticEmbedding hsplit h labels M hd hdegree a ha hdominant eM Q repr
  let e := Relative.FiberEquiv.Construction.relativeParameterRawFiberEquiv A x j arithmeticEmbedding hsplit h labels M hd hdegree
    a ha hdominant eM Q repr
  let target := Reference.ComplexTarget.Construction.originalComplexRawTarget (A.pullback x) j arithmeticEmbedding hsplit hd hdegree
    h labels M a ha hdominant eM hcop hpol hlabels h_FiniteDescent Z hZ
  have ht : (fun raw => (e.symm raw).val ≫ f.target) = target := by
    funext raw
    exact (universalFunctionParameterFineTarget_eq_raw A hA x j arithmeticEmbedding hsplit h labels M hd hdegree
      a ha hdominant eM Q repr hcop hpol hlabels h_FiniteDescent Z hZ R f hker (e.symm raw)).trans
        (congrArg target (e.apply_symm_apply raw))
  exact (CorrespondenceFibers.Construction.finiteTargetMultiset_reindex e (fun y => y.val ≫ f.target)).trans
    (congrArg (ChoiceMultisets.Construction.rawSplitTargetMultiset d q (SplitHeckeChoices.Construction.naturalIntegralLocalType d h a hdominant)) ht)

end

end OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.UniversalFunction.ParameterMultiset.Construction
