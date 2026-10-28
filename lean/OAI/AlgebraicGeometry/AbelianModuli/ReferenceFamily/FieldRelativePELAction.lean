import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Global.RelativePELAction
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Pure.Fine

/-! # Field Relative PEL Action -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.FieldRelativePELAction

noncomputable section

/-! In characteristic zero the explicitly constructed integral
generator's conductor is a unit. No generator or equation-representability
hypothesis remains in the relative PEL representation theorem. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry Opposite

theorem positive_integer_unit_in_field_base_stalk
    {K : Type} [Field K] [CharZero K] {S : Scheme.{0}}
    (p : S ⟶ Spec (.of K)) (n : ℕ) (hn : 0 < n) (x : S) :
    IsUnit (n : S.presheaf.stalk x) := by
  simpa only [map_natCast] using
    (Pure.Fine.positive_integer_unit_on_field_base p n hn).map (S.presheaf.Γgerm x).hom

theorem exists_field_relative_pel_action_representation
    {E K : Type} [Field E] [NumberField E] [Algebra ℚ E] [NumberField.IsCMField E]
    [Field K] [CharZero K] {s N : ℕ} (P : Datum.RankThreePELDatum E s)
    (iotaO : NumberField.RingOfIntegers E →+* K) (M : Over (Spec (.of K)))
    (A : HilbertConstruction.PolarizationData.PolarizedAbelianWithFullLevel (3 * s) P.polarizationType N M.left)
    [IsNoetherian M.left] :
    ∃ Z : Over M.left, IsNoetherian Z.left ∧
      LocallyOfFiniteType Z.hom ∧ QuasiCompact Z.hom ∧ IsSeparated Z.hom ∧
      ∃ u : (PELModuli.IntegralModel.Relative.ActionFunctor.relativePELActionFunctor P iotaO M A).obj (op Z),
        ∀ (T : Over M.left), Function.Bijective
          (fun f : T ⟶ Z => (PELModuli.IntegralModel.Relative.ActionFunctor.relativePELActionFunctor P iotaO M A).map f.op u) := by
  let D := Classical.choice (PELModuli.IntegralModel.CM.GeneratorReconstruction.cm_integral_generator_data_exists E)
  exact Global.RelativePELAction.exists_global_relative_pel_action_representation P iotaO M A D
    (fun x => positive_integer_unit_in_field_base_stalk M.hom D.conductor
      (Nat.pos_of_ne_zero D.conductor_ne_zero) x)

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.FieldRelativePELAction
