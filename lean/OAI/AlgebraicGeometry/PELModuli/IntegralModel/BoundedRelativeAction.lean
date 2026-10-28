import OAI.AlgebraicGeometry.PELModuli.IntegralModel.Affine.PolarizationEmbedding
import OAI.AlgebraicGeometry.PELModuli.IntegralModel.Presentations.RelativeActionScheme

/-! # Bounded Relative Action -/

namespace OAI.AlgebraicGeometry.PELModuli.IntegralModel.BoundedRelativeAction

noncomputable section

/-! The full corrected Presentations input constructs bounded integral PEL-action
moduli on any polarized family over an affine noetherian parameter scheme.
The canonical line, section embedding, and graph bounds are constructed. -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open _root_.CategoryTheory _root_.AlgebraicGeometry

theorem exists_bounded_relative_pel_action_scheme
    {E R : Type} [Field E] [NumberField E] [Algebra ℚ E] [NumberField.IsCMField E]
    [CommRing R] (D : CM.GeneratorReconstruction.CMIntegralGeneratorData E)
    {s N : ℕ} (P : AbelianModuli.ReferenceFamily.Datum.RankThreePELDatum E s)
    (iotaO : NumberField.RingOfIntegers E →+* R) (M : Over (Spec (.of R)))
    [IsAffine M.left] [IsLocallyNoetherian M.left]
    (A : AbelianModuli.HilbertConstruction.PolarizationData.PolarizedAbelianWithFullLevel (3 * s) P.polarizationType N M.left)
    (hPresentations : Presentations.Hilbert.EndomorphismEquationsInput.{0})
    (hc : ∀ x : M.left, IsUnit (D.conductor : M.left.presheaf.stalk x)) :
    ∃ Z : Over M.left, IsReduced Z.left ∧ LocallyOfFiniteType Z.hom ∧ QuasiCompact Z.hom ∧ IsSeparated Z.hom ∧
      ∃ ρZ : AbelianModuli.ReferenceFamily.ActionData.IntegralAction (NumberField.RingOfIntegers E) (A.abelian.pullback Z.hom),
        AbelianModuli.ReferenceFamily.ActionData.RosatiConjugation (A.pullback Z.hom) ρZ ∧
        PEL.Has.HasIntegralLieRanks P R iotaO ((Over.map M.hom).obj Z) (A.abelian.pullback Z.hom) ρZ ∧
        ∀ (T : Over M.left) [IsReduced T.left]
          (ρ : AbelianModuli.ReferenceFamily.ActionData.IntegralAction (NumberField.RingOfIntegers E) (A.abelian.pullback T.hom)),
          (AbelianModuli.ReferenceFamily.ActionData.RosatiConjugation (A.pullback T.hom) ρ ∧
            PEL.Has.HasIntegralLieRanks P R iotaO ((Over.map M.hom).obj T) (A.abelian.pullback T.hom) ρ) ↔
            ∃! f : T ⟶ Z, Integral.ActionScheme.restrictIntegralAction A.abelian ρZ f = ρ := by
  have : IsNoetherianRing Γ(M.left, ⊤) :=
    IsLocallyNoetherian.component_noetherian ⟨⊤, isAffineOpen_top M.left⟩
  obtain ⟨d, _, L, hL, n, q, hq, he⟩ := Affine.PolarizationEmbedding.polarized_exists_affine_section_embedding A
  exact Presentations.RelativeActionScheme.exists_e34_reduced_relative_pel_action_scheme D P iotaO M A L d hL q hq he hPresentations hc

end

end OAI.AlgebraicGeometry.PELModuli.IntegralModel.BoundedRelativeAction
