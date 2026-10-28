import OAI.AlgebraicGeometry.PELModuli.IntegralModel.LocallyConstantBasePartition
import OAI.AlgebraicGeometry.PELModuli.IntegralModel.RosatiRestriction

/-! # Stratum Action Assembly -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Finite.StratumActionAssembly

noncomputable section

/-! Glue finitely many integral-action schemes over a clopen base
partition. The universal action and unique classifiers are constructed
on arbitrary test schemes by the original morphism and action gluing. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

open OAI.AlgebraicGeometry.PELModuli.IntegralModel.RosatiRestriction OAI.AlgebraicGeometry.PELModuli.IntegralModel.LocallyConstantBasePartition.FiniteBasePartition

theorem assemble_all_test_stratum_action_ambient
    {E : Type} [Field E] [NumberField E] [NumberField.IsCMField E]
    {S : Scheme.{0}} {I : Type} [Finite I] (c : LocallyConstant S I)
    {g N : ℕ} {δ : Fin g → ℕ} (A : HilbertConstruction.PolarizationData.PolarizedAbelianWithFullLevel g δ N S)
    (Z : I → Over S)
    [∀ i, LocallyOfFiniteType (Z i).hom] [∀ i, QuasiCompact (Z i).hom]
    [∀ i, IsSeparated (Z i).hom]
    (hZ : ∀ i, ∀ z : (Z i).left, c ((Z i).hom z) = i)
    (ρZ : ∀ i, ActionData.IntegralAction (NumberField.RingOfIntegers E) (A.abelian.pullback (Z i).hom))
    (hclass : ∀ i, ∀ (T : Over S)
      (_hT : ∀ t : T.left, c (T.hom t) = i)
      (ρ : ActionData.IntegralAction (NumberField.RingOfIntegers E) (A.abelian.pullback T.hom)),
      ActionData.RosatiConjugation (A.pullback T.hom) ρ →
        ∃! f : T ⟶ Z i, PELModuli.IntegralModel.Integral.ActionScheme.restrictIntegralAction A.abelian (ρZ i) f = ρ) :
    ∃ M : Over S, LocallyOfFiniteType M.hom ∧ QuasiCompact M.hom ∧ IsSeparated M.hom ∧
      ∃ ρM : ActionData.IntegralAction (NumberField.RingOfIntegers E) (A.abelian.pullback M.hom),
        ∀ (T : Over S)
          (ρ : ActionData.IntegralAction (NumberField.RingOfIntegers E) (A.abelian.pullback T.hom)),
          ActionData.RosatiConjugation (A.pullback T.hom) ρ →
            ∃! f : T ⟶ M, PELModuli.IntegralModel.Integral.ActionScheme.restrictIntegralAction A.abelian ρM f = ρ := by
  let M := PELModuli.IntegralModel.Finite.ParameterSum.FiniteBasePartition.sumParameter Z
  let k := PELModuli.IntegralModel.Finite.ParameterSum.FiniteBasePartition.sumParameterInclusion Z
  let ρM := PELModuli.IntegralModel.Finite.PartitionActions.FiniteBasePartition.glueIntegralAction Z M k (PELModuli.IntegralModel.Finite.ParameterSum.FiniteBasePartition.sumParameterIsColimit Z) A.abelian ρZ
  have hρM (i : I) : PELModuli.IntegralModel.Integral.ActionScheme.restrictIntegralAction A.abelian ρM (k i) = ρZ i :=
    PELModuli.IntegralModel.Finite.PartitionActions.FiniteBasePartition.glueIntegralAction_restrict Z M k (PELModuli.IntegralModel.Finite.ParameterSum.FiniteBasePartition.sumParameterIsColimit Z) A.abelian ρZ i
  refine ⟨M, inferInstance, inferInstance, inferInstance, ρM, ?_⟩
  intro T ρ hρ
  let U := PELModuli.IntegralModel.LocallyConstantBasePartition.FiniteBasePartition.testPart c T
  let j := PELModuli.IntegralModel.LocallyConstantBasePartition.FiniteBasePartition.testPartInclusion c T
  let H := PELModuli.IntegralModel.LocallyConstantBasePartition.FiniteBasePartition.testPartitionIsColimit c T
  have hd (i : I) : ∃! f : U i ⟶ Z i,
      PELModuli.IntegralModel.Integral.ActionScheme.restrictIntegralAction A.abelian (ρZ i) f = PELModuli.IntegralModel.Integral.ActionScheme.restrictIntegralAction A.abelian ρ (j i) :=
    hclass i (U i) (PELModuli.IntegralModel.LocallyConstantBasePartition.FiniteBasePartition.testPart_index c T i) (PELModuli.IntegralModel.Integral.ActionScheme.restrictIntegralAction A.abelian ρ (j i))
      (PELModuli.IntegralModel.RosatiRestriction.rosati_restrictIntegralAction (T := U i) (U := T) A ρ hρ (j i))
  choose f hf huniq using hd
  let q := PELModuli.IntegralModel.Finite.PartitionBaseMaps.FiniteBasePartition.glueBase U T j H M (fun i => f i ≫ k i)
  have hq (i : I) : j i ≫ q = f i ≫ k i := PELModuli.IntegralModel.Finite.PartitionBaseMaps.FiniteBasePartition.glueBase_restrict U T j H M _ i
  refine ⟨q, ?_, ?_⟩
  · apply PELModuli.IntegralModel.Finite.PartitionActions.FiniteBasePartition.integralAction_ext_of_restrictions U T j H A.abelian
    intro i
    rw [← PELModuli.IntegralModel.Integral.ActionScheme.restrictIntegralAction_comp, hq, PELModuli.IntegralModel.Integral.ActionScheme.restrictIntegralAction_comp, hρM]
    exact hf i
  · intro p hp
    apply PELModuli.IntegralModel.Finite.PartitionBaseMaps.FiniteBasePartition.base_hom_ext U T j H M
    intro i
    have hindex (t : (U i).left) : c ((U i).hom t) = i := PELModuli.IntegralModel.LocallyConstantBasePartition.FiniteBasePartition.testPart_index c T i t
    obtain ⟨a, ha, _⟩ := PELModuli.IntegralModel.LocallyConstantBasePartition.FiniteBasePartition.sumParameter_factor_at_index c Z hZ (j i ≫ p) i hindex
    have har : PELModuli.IntegralModel.Integral.ActionScheme.restrictIntegralAction A.abelian (ρZ i) a =
        PELModuli.IntegralModel.Integral.ActionScheme.restrictIntegralAction A.abelian ρ (j i) := by
      rw [← hρM, ← PELModuli.IntegralModel.Integral.ActionScheme.restrictIntegralAction_comp, ha, PELModuli.IntegralModel.Integral.ActionScheme.restrictIntegralAction_comp, hp]
    have hea : a = f i := huniq i a har
    exact ha.symm.trans ((congrArg (fun a => a ≫ k i) hea).trans (hq i).symm)

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Finite.StratumActionAssembly
