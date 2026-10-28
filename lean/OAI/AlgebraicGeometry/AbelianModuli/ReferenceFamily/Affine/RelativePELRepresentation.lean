import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.BoundedRelativePELAction
import OAI.AlgebraicGeometry.PELModuli.IntegralModel.Relative.ActionFunctor

/-! # Relative PEL Representation -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Affine.RelativePELRepresentation

noncomputable section

/-! The constructed affine PEL-action scheme represents the original
relative action functor on all test schemes. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry Opposite

open OAI.AlgebraicGeometry.PELModuli.IntegralModel.Relative.ActionFunctor
variable {E R : Type} [Field E] [NumberField E] [Algebra ℚ E] [NumberField.IsCMField E]
    [CommRing R] [Algebra ℚ R] {s N : ℕ} (P : Datum.RankThreePELDatum E s)
    (iotaO : NumberField.RingOfIntegers E →+* R) (M : Over (Spec (.of R)))
    (A : HilbertConstruction.PolarizationData.PolarizedAbelianWithFullLevel (3 * s) P.polarizationType N M.left)

theorem exists_affine_relative_pel_action_representation
    [IsAffine M.left] [IsLocallyNoetherian M.left] (D : PELModuli.IntegralModel.CM.GeneratorReconstruction.CMIntegralGeneratorData E)
    (hc : ∀ x : M.left, IsUnit (D.conductor : M.left.presheaf.stalk x)) :
    ∃ Z : Over M.left, LocallyOfFiniteType Z.hom ∧ QuasiCompact Z.hom ∧ IsSeparated Z.hom ∧
      ∃ u : (PELModuli.IntegralModel.Relative.ActionFunctor.relativePELActionFunctor P iotaO M A).obj (op Z),
        ∀ (T : Over M.left),
          Function.Bijective (fun f : T ⟶ Z => (PELModuli.IntegralModel.Relative.ActionFunctor.relativePELActionFunctor P iotaO M A).map f.op u) := by
  obtain ⟨Z, hft, hqc, hsep, ρZ, hRos, hLie, hclass⟩ :=
    BoundedRelativePELAction.exists_bounded_relative_pel_action_scheme D P iotaO M A hc
  let u : (PELModuli.IntegralModel.Relative.ActionFunctor.relativePELActionFunctor P iotaO M A).obj (op Z) := ⟨ρZ, hRos, hLie⟩
  refine ⟨Z, hft, hqc, hsep, u, fun T => ?_⟩
  apply (Function.bijective_iff_existsUnique _).mpr
  intro ρ
  obtain ⟨f, hf, huniq⟩ := (hclass T ρ.val).mp ρ.property
  refine ⟨f, Subtype.ext hf, fun e he => huniq e ?_⟩
  exact congrArg Subtype.val he

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Affine.RelativePELRepresentation
