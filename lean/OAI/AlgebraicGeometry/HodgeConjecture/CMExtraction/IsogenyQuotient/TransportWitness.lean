import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.UniversalFunction.PolarizationAdapter
import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Reference.HeckeTargets
import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.CM.PointsPerfectKernel
import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Intrinsic.TorsionPairingBaseChange
import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Intrinsic.MorphismKernel
import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Intrinsic.Stability
import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.TotalParameters

/-! # Transport Witness -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.IsogenyQuotient.TransportWitness

noncomputable section

/-! The complete native fiber witness with the universal-functions proof
exposed as data. That proof is derived from the full fine ReferenceFamily geometry in
the separate faithfulness theorem; it is not an extra hypothesis of the
geometric wrapper. All native kernel, polarization, marking, and raw
multiset clauses retain the same cover and target. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj BigOperators

variable {E K L : Type} [Field E] [NumberField E] [NumberField.IsCMField E] [IsGalois ℚ E]
    [Field K] [NumberField K] [CharZero K] [Field L] [NumberField L]
    {d N q : ℕ} [NeZero N] [Fact q.Prime] {P : AbelianModuli.ReferenceFamily.Datum.RankThreePELDatum E d} {iota : E →+* K}
    (Z : AbelianModuli.ReferenceFamily.Models.FinePELModel P iota N) (hZ : Z.IsFine)
    (hA : AbelianScheme.IsogenyQuotient.GlobalFunctions.Construction.HasUniversalGlobalFunctions Z.universal.polarized.abelian.scheme)
    {κ : L →+* ℂ} (j : PELModuli.CMPoints.Arithmetic.QadicChoice L κ q) (arithmeticEmbedding : E →+* L)
    (hsplit : j.HasSplitCoordinates arithmeticEmbedding)
    (hd : 0 < d) (hdegree : Module.finrank ℚ E = 2 * d)
    (h : ℕ) (labels : AbelianScheme.IsogenyQuotient.ChoiceKernel.Construction.KernelIndex d ≃ Gal(E/ℚ))
    (hlabels : ∀ i, labels (Sum.swap i) = PELModuli.CMPoints.Arithmetic.rationalConjugation E * labels i)
    (a : Fin d → Fin 3 → ℕ) (ha : ∀ v i, a v i ≤ h) (hdominant : ∀ v, Antitone (a v))
    (hcop : Nat.Coprime q N) (hpol : Nat.Coprime q (∏ i, P.polarizationType i))
    (h_FiniteDescent : AbelianScheme.IsogenyQuotient.IsogenyComplement.Construction.FiniteDescentInput.{0})

def TransportIntegralFiberWitnessAtAction (Q : Over Z.space.left)
    (f : AbelianScheme.IsogenyQuotient.IntrinsicFineTargetData.Construction.NativeFinePELTarget (Z.universal.pullback (AbelianScheme.IsogenyQuotient.TotalParameters.Construction.totalParameterSource Z.space Q)) (q ^ h) Z)
    (action : AbelianModuli.ReferenceFamily.ActionData.IntegralAction (NumberField.RingOfIntegers E) Z.universal.polarized.abelian) : Prop :=
  let A := Z.universal
  let M := fun v => AbelianScheme.IsogenyQuotient.ElementaryModules.Construction.RankThreeElementaryModule.{0} q (a v)
  letI : ∀ v, Module (ZMod (q ^ h)) (M v) :=
    fun v => AbelianScheme.IsogenyQuotient.ElementaryModules.Construction.rankThreeElementaryModule_structure q h (a v) (ha v)
  let p := AbelianScheme.IsogenyQuotient.CM.PointsIntrinsicFamily.Construction.l45ChosenProjectors j arithmeticEmbedding hsplit A.polarized.abelian action h d labels
  let r := AbelianScheme.IsogenyQuotient.CM.PointsIntrinsicFamily.Construction.l45OppositeProjectors j arithmeticEmbedding hsplit A.polarized.abelian action h d labels
  let b := AbelianScheme.IsogenyQuotient.UniversalFunction.PolarizationAdapter.Construction.universalFunctionNativePolarizationPairing A.polarized.abelian A.polarized.dual
    A.polarized.polarization (AbelianScheme.IsogenyQuotient.GlobalFunctions.Construction.universalGlobalFunctions_of_finiteFlat_source A.polarized.polarization.isogeny.hom hA)
      (q ^ h) (pow_pos (Fact.out : q.Prime).pos h)
  let ep := AbelianScheme.IsogenyQuotient.CM.PointsPerfectKernel.Construction.l45SourceBlockPairing j arithmeticEmbedding hsplit A.polarized.abelian action h d labels b
  let AC := A.pullback (AbelianScheme.IsogenyQuotient.TotalParameters.Construction.totalParameterSource Z.space Q)
  let f' : AbelianScheme.IsogenyQuotient.IntrinsicFineTargetData.Construction.NativeFinePELTarget AC (q ^ h) Z := f
  ∃ repr : (AbelianScheme.IsogenyQuotient.Parameter.Products.Construction.blockTupleFunctor d (fun v =>
      AbelianScheme.IsogenyQuotient.SubgroupFunctor.Construction.supportedSubgroupFunctor A.polarized.abelian.scheme (q ^ h) (M v) (p v))).RepresentableBy Q,
    ∃ e : uliftYoneda.{1}.obj (AbelianScheme.IsogenyQuotient.TotalParameters.Construction.totalParameter Z.space Q) ≅
      AbelianScheme.IsogenyQuotient.TotalParameters.Construction.totalParameterFunctor Z.space Q _ repr,
    e.hom ≫ AbelianScheme.IsogenyQuotient.TotalParameters.Construction.totalParameterForget Z.space Q _ repr =
      uliftYoneda.{1}.map (AbelianScheme.IsogenyQuotient.TotalParameters.Construction.totalParameterSource Z.space Q) ∧
    IsFinite (AbelianScheme.IsogenyQuotient.TotalParameters.Construction.totalParameterSource Z.space Q).left ∧
    Etale (AbelianScheme.IsogenyQuotient.TotalParameters.Construction.totalParameterSource Z.space Q).left ∧
    let F := AbelianScheme.IsogenyQuotient.ChoiceKernel.Construction.choiceFullKernel (q ^ h) d M p r ep (AbelianScheme.IsogenyQuotient.Universal.Choices.Construction.universalBlockChoice (q ^ h) d M p repr)
    ∃ R : F.Model,
      (∀ (U : Over (AbelianScheme.IsogenyQuotient.TotalParameters.Construction.totalParameter Z.space Q).left) (z : U ⟶ AC.polarized.abelian.scheme),
        z ≫ f'.isogeny.hom = 1 ↔ ∃! w : U ⟶ (AbelianScheme.IsogenyQuotient.Subgroup.Construction.subgroupGroupScheme F R).X,
          w ≫ AbelianScheme.IsogenyQuotient.Intrinsic.Stability.Construction.nativeSubgroupInclusion A.polarized.abelian Q F R = z) ∧
      (let H := AbelianScheme.IsogenyQuotient.SubgroupTransport.Construction.relativeSubgroupPullback (AbelianScheme.IsogenyQuotient.Torsion.Groups.Construction.nativeTorsionInclusion AC.polarized.abelian.scheme (q ^ h))
          (AbelianScheme.IsogenyQuotient.Intrinsic.MorphismKernel.Construction.nativeMorphismKernel f'.isogeny.hom);
        (AbelianScheme.IsogenyQuotient.Intrinsic.TorsionPairingBaseChange.Construction.nativeTorsionPairingPullback Q.hom (Grp.mk A.polarized.abelian.scheme)
          (Grp.mk A.polarized.abelian.scheme) (q ^ h) b).relativeAnnihilator H = H) ∧
      ∀ (c : Foundations.Scheme.ProjectiveSpace.complexBase ⟶ Spec (.of K)) (x : Over.mk c ⟶ Z.space),
        ∃ hfin : Finite (AbelianScheme.IsogenyQuotient.CorrespondenceFibers.Construction.SourceFiber (AbelianScheme.IsogenyQuotient.TotalParameters.Construction.totalParameterSource Z.space Q) x),
          @AbelianScheme.IsogenyQuotient.CorrespondenceFibers.Construction.correspondenceFiberMultiset _ _ _ _ _ (AbelianScheme.IsogenyQuotient.TotalParameters.Construction.totalParameterSource Z.space Q) f'.target x hfin =
            AbelianScheme.IsogenyQuotient.Reference.HeckeTargets.Construction.originalRawHeckeMultiset Z hZ j arithmeticEmbedding hsplit hd hdegree h labels hlabels
              a ha hdominant hcop hpol h_FiniteDescent x

abbrev TransportIntegralFiberWitness (Q : Over Z.space.left)
    (f : AbelianScheme.IsogenyQuotient.IntrinsicFineTargetData.Construction.NativeFinePELTarget (Z.universal.pullback (AbelianScheme.IsogenyQuotient.TotalParameters.Construction.totalParameterSource Z.space Q)) (q ^ h) Z) : Prop :=
  TransportIntegralFiberWitnessAtAction Z hZ hA j arithmeticEmbedding hsplit hd hdegree h labels hlabels
    a ha hdominant hcop hpol h_FiniteDescent Q f Z.universal.action

end

end OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.IsogenyQuotient.TransportWitness
