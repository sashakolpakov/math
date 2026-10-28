import OAI.AlgebraicGeometry.PELModuli.IntegralModel.BoundedRelativeAction
import OAI.AlgebraicGeometry.PELModuli.IntegralModel.Integral.ActionFunctor
import OAI.AlgebraicGeometry.PELModuli.IntegralModel.Integral.LieRankRestriction
import OAI.AlgebraicGeometry.PELModuli.IntegralModel.PEL.BaseChange

/-! # Action Functor -/

namespace OAI.AlgebraicGeometry.PELModuli.IntegralModel.Relative.ActionFunctor

noncomputable section

/-! The actual integral PEL-action functor on a fixed varying polarized
family, with the constructed affine representing objects on reduced tests. -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open _root_.CategoryTheory _root_.AlgebraicGeometry Opposite

variable {E R : Type} [Field E] [NumberField E] [Algebra ℚ E] [NumberField.IsCMField E]
    [CommRing R] {s N : ℕ} (P : AbelianModuli.ReferenceFamily.Datum.RankThreePELDatum E s)
    (iotaO : NumberField.RingOfIntegers E →+* R) (M : Over (Spec (.of R)))
    (A : AbelianModuli.HilbertConstruction.PolarizationData.PolarizedAbelianWithFullLevel (3 * s) P.polarizationType N M.left)

def relativePELActionSubfunctor : Subfunctor (Integral.ActionFunctor.integralActionFunctor A.abelian E) where
  obj T := {ρ | AbelianModuli.ReferenceFamily.ActionData.RosatiConjugation (A.pullback T.unop.hom) ρ ∧
    PEL.Has.HasIntegralLieRanks P R iotaO ((Over.map M.hom).obj T.unop) (A.abelian.pullback T.unop.hom) ρ}
  map {T U} f := by
    intro ρ hρ
    refine ⟨RosatiRestriction.rosati_restrictIntegralAction A ρ hρ.1 f.unop, ?_⟩
    apply (Integral.LieRankRestriction.integralLieRanks_restrict_iff P iotaO M A.abelian ρ f.unop).mpr
    exact PEL.BaseChange.integralLieRanks_pullback (P := P) (R := R) (iotaO := iotaO)
      (X := (Over.map M.hom).obj T.unop) (Y := (Over.map M.hom).obj U.unop)
      (A.abelian.pullback T.unop.hom) ρ hρ.2
      ((Over.map M.hom).map f.unop)

def relativePELActionFunctor : (Over M.left)ᵒᵖ ⥤ Type :=
  (relativePELActionSubfunctor P iotaO M A).toFunctor

theorem exists_affine_relative_pel_action_representation
    [IsAffine M.left] [IsLocallyNoetherian M.left] (D : CM.GeneratorReconstruction.CMIntegralGeneratorData E)
    (hPresentations : Presentations.Hilbert.EndomorphismEquationsInput.{0})
    (hc : ∀ x : M.left, IsUnit (D.conductor : M.left.presheaf.stalk x)) :
    ∃ Z : Over M.left, IsReduced Z.left ∧ LocallyOfFiniteType Z.hom ∧ QuasiCompact Z.hom ∧ IsSeparated Z.hom ∧
      ∃ u : (relativePELActionFunctor P iotaO M A).obj (op Z),
        ∀ (T : Over M.left) [IsReduced T.left],
          Function.Bijective (fun f : T ⟶ Z => (relativePELActionFunctor P iotaO M A).map f.op u) := by
  obtain ⟨Z, hr, hft, hqc, hsep, ρZ, hRos, hLie, hclass⟩ :=
    BoundedRelativeAction.exists_bounded_relative_pel_action_scheme D P iotaO M A hPresentations hc
  let u : (relativePELActionFunctor P iotaO M A).obj (op Z) := ⟨ρZ, hRos, hLie⟩
  refine ⟨Z, hr, hft, hqc, hsep, u, fun T _ => ?_⟩
  apply (Function.bijective_iff_existsUnique _).mpr
  intro ρ
  obtain ⟨f, hf, huniq⟩ := (hclass T ρ.val).mp ρ.property
  refine ⟨f, Subtype.ext hf, fun e he => huniq e ?_⟩
  exact congrArg Subtype.val he

end

end OAI.AlgebraicGeometry.PELModuli.IntegralModel.Relative.ActionFunctor
