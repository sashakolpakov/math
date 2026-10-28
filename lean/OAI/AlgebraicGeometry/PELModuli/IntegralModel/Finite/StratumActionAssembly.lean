import OAI.AlgebraicGeometry.PELModuli.IntegralModel.LocallyConstantBasePartition
import OAI.AlgebraicGeometry.PELModuli.IntegralModel.RosatiRestriction

/-! # Stratum Action Assembly -/

namespace OAI.AlgebraicGeometry.PELModuli.IntegralModel.Finite.StratumActionAssembly

noncomputable section

/-! Assemble finitely many action parameter schemes on disjoint base
strata. The universal integral action and the all-reduced-test
classification are constructed by actual morphism and action gluing. -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

open OAI.AlgebraicGeometry.PELModuli.IntegralModel.LocallyConstantBasePartition.FiniteBasePartition

theorem assemble_finite_stratum_action_ambient
    {E : Type} [Field E] [NumberField E] [NumberField.IsCMField E]
    {S : Scheme.{0}} {I : Type} [Finite I] (c : LocallyConstant S I)
    {g N : ℕ} {δ : Fin g → ℕ} (A : AbelianModuli.HilbertConstruction.PolarizationData.PolarizedAbelianWithFullLevel g δ N S)
    (Z : I → Over S) [∀ i, IsReduced (Z i).left]
    [∀ i, LocallyOfFiniteType (Z i).hom] [∀ i, QuasiCompact (Z i).hom] [∀ i, IsSeparated (Z i).hom]
    (hZ : ∀ i, ∀ z : (Z i).left, c ((Z i).hom z) = i)
    (ρZ : ∀ i, AbelianModuli.ReferenceFamily.ActionData.IntegralAction (NumberField.RingOfIntegers E) (A.abelian.pullback (Z i).hom))
    (hclass : ∀ i, ∀ (T : Over S) [IsReduced T.left]
      (_hT : ∀ t : T.left, c (T.hom t) = i)
      (ρ : AbelianModuli.ReferenceFamily.ActionData.IntegralAction (NumberField.RingOfIntegers E) (A.abelian.pullback T.hom)),
      AbelianModuli.ReferenceFamily.ActionData.RosatiConjugation (A.pullback T.hom) ρ →
        ∃! f : T ⟶ Z i, Integral.ActionScheme.restrictIntegralAction A.abelian (ρZ i) f = ρ) :
    ∃ M : Over S, IsReduced M.left ∧ LocallyOfFiniteType M.hom ∧ QuasiCompact M.hom ∧ IsSeparated M.hom ∧
      ∃ ρM : AbelianModuli.ReferenceFamily.ActionData.IntegralAction (NumberField.RingOfIntegers E) (A.abelian.pullback M.hom),
        ∀ (T : Over S) [IsReduced T.left]
          (ρ : AbelianModuli.ReferenceFamily.ActionData.IntegralAction (NumberField.RingOfIntegers E) (A.abelian.pullback T.hom)),
          AbelianModuli.ReferenceFamily.ActionData.RosatiConjugation (A.pullback T.hom) ρ →
            ∃! f : T ⟶ M, Integral.ActionScheme.restrictIntegralAction A.abelian ρM f = ρ := by
  let M := ParameterSum.FiniteBasePartition.sumParameter Z
  let k := ParameterSum.FiniteBasePartition.sumParameterInclusion Z
  let ρM := PartitionActions.FiniteBasePartition.glueIntegralAction Z M k (ParameterSum.FiniteBasePartition.sumParameterIsColimit Z) A.abelian ρZ
  have hρM (i : I) : Integral.ActionScheme.restrictIntegralAction A.abelian ρM (k i) = ρZ i :=
    PartitionActions.FiniteBasePartition.glueIntegralAction_restrict Z M k (ParameterSum.FiniteBasePartition.sumParameterIsColimit Z) A.abelian ρZ i
  refine ⟨M, inferInstance, inferInstance, inferInstance, inferInstance, ρM, ?_⟩
  intro T hred ρ hρ
  let U := LocallyConstantBasePartition.FiniteBasePartition.testPart c T
  let j := LocallyConstantBasePartition.FiniteBasePartition.testPartInclusion c T
  let H := LocallyConstantBasePartition.FiniteBasePartition.testPartitionIsColimit c T
  have hU (i : I) : IsReduced (U i).left :=
    inferInstanceAs (IsReduced (AbelianModuli.HilbertConstruction.ConstantScheme.Iff.locallyConstantFiber (LocallyConstantBasePartition.FiniteBasePartition.testIndex c T) i).toScheme)
  let := hU
  have hd (i : I) : ∃! f : U i ⟶ Z i,
      Integral.ActionScheme.restrictIntegralAction A.abelian (ρZ i) f = Integral.ActionScheme.restrictIntegralAction A.abelian ρ (j i) :=
    hclass i (U i) (LocallyConstantBasePartition.FiniteBasePartition.testPart_index c T i) (Integral.ActionScheme.restrictIntegralAction A.abelian ρ (j i))
      (RosatiRestriction.rosati_restrictIntegralAction (T := U i) (U := T) A ρ hρ (j i))
  choose f hf huniq using hd
  let q := PartitionBaseMaps.FiniteBasePartition.glueBase U T j H M (fun i => f i ≫ k i)
  have hq (i : I) : j i ≫ q = f i ≫ k i := PartitionBaseMaps.FiniteBasePartition.glueBase_restrict U T j H M _ i
  refine ⟨q, ?_, ?_⟩
  · apply PartitionActions.FiniteBasePartition.integralAction_ext_of_restrictions U T j H A.abelian
    intro i
    rw [← Integral.ActionScheme.restrictIntegralAction_comp, hq, Integral.ActionScheme.restrictIntegralAction_comp, hρM]
    exact hf i
  · intro p hp
    apply PartitionBaseMaps.FiniteBasePartition.base_hom_ext U T j H M
    intro i
    have hindex (t : (U i).left) : c ((U i).hom t) = i := LocallyConstantBasePartition.FiniteBasePartition.testPart_index c T i t
    obtain ⟨a, ha, _⟩ := LocallyConstantBasePartition.FiniteBasePartition.sumParameter_factor_at_index c Z hZ (j i ≫ p) i hindex
    have har : Integral.ActionScheme.restrictIntegralAction A.abelian (ρZ i) a =
        Integral.ActionScheme.restrictIntegralAction A.abelian ρ (j i) := by
      rw [← hρM, ← Integral.ActionScheme.restrictIntegralAction_comp, ha, Integral.ActionScheme.restrictIntegralAction_comp, hp]
    have hea : a = f i := huniq i a har
    exact ha.symm.trans ((congrArg (fun a => a ≫ k i) hea).trans (hq i).symm)

end

end OAI.AlgebraicGeometry.PELModuli.IntegralModel.Finite.StratumActionAssembly
