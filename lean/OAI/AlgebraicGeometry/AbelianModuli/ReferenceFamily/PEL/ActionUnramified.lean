import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.FieldRelativePELAction
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.UnramifiedQuasiFinite
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Integral.ActionFieldFaithfulness
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Field.FaithfulPullbackParameter
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Finite.TypeParameterNoetherian
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.SchemeUnramifiedFieldCriterion

/-! # Action Unramified -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.PEL.ActionUnramified

noncomputable section

/-! The constructed all-test PEL-action parameter is formally unramified
over its original noetherian base, including at nonreduced tests. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry Opposite

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

theorem exists_global_unramified_relative_pel_action_representation
    {E R : Type} [Field E] [NumberField E] [Algebra ℚ E]
    [NumberField.IsCMField E] [CommRing R] [Algebra ℚ R]
    {s N : ℕ} (P : Datum.RankThreePELDatum E s)
    (iotaO : NumberField.RingOfIntegers E →+* R)
    (M : Over (Spec (.of R))) [IsNoetherian M.left]
    (A : HilbertConstruction.PolarizationData.PolarizedAbelianWithFullLevel (3 * s) P.polarizationType N M.left)
    (D : PELModuli.IntegralModel.CM.GeneratorReconstruction.CMIntegralGeneratorData E)
    (hc : ∀ x : M.left, IsUnit (D.conductor : M.left.presheaf.stalk x)) :
    ∃ Z : Over M.left, IsNoetherian Z.left ∧
      LocallyOfFiniteType Z.hom ∧ QuasiCompact Z.hom ∧ IsSeparated Z.hom ∧
      FormallyUnramified Z.hom ∧
      ∃ u : (PELModuli.IntegralModel.Relative.ActionFunctor.relativePELActionFunctor P iotaO M A).obj (op Z),
        ∀ (T : Over M.left), Function.Bijective
          (fun f : T ⟶ Z => (PELModuli.IntegralModel.Relative.ActionFunctor.relativePELActionFunctor P iotaO M A).map f.op u) := by
  obtain ⟨Z, hn, hft, hqc, hsep, u, hclass⟩ :=
    Global.RelativePELAction.exists_global_relative_pel_action_representation P iotaO M A D hc
  let := hft
  let := hqc
  have hu : FormallyUnramified Z.hom := by
    apply HilbertConstruction.SchemeUnramifiedFieldCriterion.formallyUnramified_of_fieldPullbacks Z.hom
    intro K _ k
    have hN : IsNoetherian
        (pullback ((Over.pullback k).obj Z).hom ((Over.pullback k).obj Z).hom) :=
      HilbertConstruction.Finite.TypeParameterNoetherian.finiteTypeParameter_pullback_selfProduct_noetherian Z k
    apply HilbertConstruction.RigidParameterDiagonal.fieldFaithfulParameter_formallyUnramified ((Over.pullback k).obj Z)
    apply HilbertConstruction.Field.FaithfulPullbackParameter.fieldFaithfulParameter_pullback
    intro F _ T _ s a b hab
    let V : Over M.left := Over.mk (T.hom ≫ k)
    let W : Over M.left := Over.mk (s ≫ V.hom)
    let c : W ⟶ V := Over.homMk s rfl
    have he : c ≫ a = c ≫ b := Over.OverMorphism.ext hab
    apply (hclass V).injective
    apply Subtype.ext
    apply Integral.ActionFieldFaithfulness.integralAction_eq_of_field_restriction A.abelian k T s
    have hv := congrArg
      (fun f : W ⟶ Z => (PELModuli.IntegralModel.Relative.ActionFunctor.relativePELActionFunctor P iotaO M A).map f.op u) he
    have hr := congrArg Subtype.val hv
    change PELModuli.IntegralModel.Integral.ActionScheme.restrictIntegralAction A.abelian u.val (c ≫ a) =
      PELModuli.IntegralModel.Integral.ActionScheme.restrictIntegralAction A.abelian u.val (c ≫ b) at hr
    exact (PELModuli.IntegralModel.Integral.ActionScheme.restrictIntegralAction_comp A.abelian c a u.val).symm.trans
      (hr.trans (PELModuli.IntegralModel.Integral.ActionScheme.restrictIntegralAction_comp A.abelian c b u.val))
  exact ⟨Z, hn, hft, hqc, hsep, hu, u, hclass⟩

theorem exists_field_unramified_relative_pel_action_representation
    {E K : Type} [Field E] [NumberField E] [Algebra ℚ E]
    [NumberField.IsCMField E] [Field K] [CharZero K]
    {s N : ℕ} (P : Datum.RankThreePELDatum E s)
    (iotaO : NumberField.RingOfIntegers E →+* K)
    (M : Over (Spec (.of K))) [IsNoetherian M.left]
    (A : HilbertConstruction.PolarizationData.PolarizedAbelianWithFullLevel (3 * s) P.polarizationType N M.left) :
    ∃ Z : Over M.left, IsNoetherian Z.left ∧
      LocallyOfFiniteType Z.hom ∧ QuasiCompact Z.hom ∧ IsSeparated Z.hom ∧
      FormallyUnramified Z.hom ∧ LocallyQuasiFinite Z.hom ∧
      ∃ u : (PELModuli.IntegralModel.Relative.ActionFunctor.relativePELActionFunctor P iotaO M A).obj (op Z),
        ∀ (T : Over M.left), Function.Bijective
          (fun f : T ⟶ Z => (PELModuli.IntegralModel.Relative.ActionFunctor.relativePELActionFunctor P iotaO M A).map f.op u) := by
  let D := Classical.choice (PELModuli.IntegralModel.CM.GeneratorReconstruction.cm_integral_generator_data_exists E)
  obtain ⟨Z, hn, hft, hqc, hsep, hu, u, hclass⟩ :=
    exists_global_unramified_relative_pel_action_representation P iotaO M A D
      (fun x => FieldRelativePELAction.positive_integer_unit_in_field_base_stalk M.hom D.conductor
        (Nat.pos_of_ne_zero D.conductor_ne_zero) x)
  let := hft
  let := hu
  exact ⟨Z, hn, hft, hqc, hsep, hu, HilbertConstruction.UnramifiedQuasiFinite.locallyQuasiFinite_of_unramified Z.hom, u, hclass⟩

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.PEL.ActionUnramified
