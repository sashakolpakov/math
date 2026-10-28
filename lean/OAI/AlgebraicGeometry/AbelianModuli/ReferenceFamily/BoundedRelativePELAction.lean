import OAI.AlgebraicGeometry.PELModuli.IntegralModel.Affine.PolarizationEmbedding
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Relative.PELActionScheme

/-! # Bounded Relative PEL Action -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.BoundedRelativePELAction

noncomputable section

/-! Construct bounded integral PEL-action moduli over an affine
noetherian parameter in characteristic zero. The canonical polarization
embedding and all-test Rosati and Lie conditions are proved constructions. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

open OAI.AlgebraicGeometry.PELModuli.IntegralModel.Affine.PolarizationEmbedding

theorem exists_bounded_relative_pel_action_scheme
    {E R : Type} [Field E] [NumberField E] [Algebra ℚ E] [NumberField.IsCMField E]
    [CommRing R] [Algebra ℚ R] (D : PELModuli.IntegralModel.CM.GeneratorReconstruction.CMIntegralGeneratorData E)
    {s N : ℕ} (P : Datum.RankThreePELDatum E s)
    (iotaO : NumberField.RingOfIntegers E →+* R) (M : Over (Spec (.of R)))
    [IsAffine M.left] [IsLocallyNoetherian M.left]
    (A : HilbertConstruction.PolarizationData.PolarizedAbelianWithFullLevel (3 * s) P.polarizationType N M.left)
    (hc : ∀ x : M.left, IsUnit (D.conductor : M.left.presheaf.stalk x)) :
    ∃ Z : Over M.left, LocallyOfFiniteType Z.hom ∧ QuasiCompact Z.hom ∧ IsSeparated Z.hom ∧
      ∃ ρZ : ActionData.IntegralAction (NumberField.RingOfIntegers E) (A.abelian.pullback Z.hom),
        ActionData.RosatiConjugation (A.pullback Z.hom) ρZ ∧
        PELModuli.IntegralModel.PEL.Has.HasIntegralLieRanks P R iotaO ((Over.map M.hom).obj Z) (A.abelian.pullback Z.hom) ρZ ∧
        ∀ (T : Over M.left)
          (ρ : ActionData.IntegralAction (NumberField.RingOfIntegers E) (A.abelian.pullback T.hom)),
          (ActionData.RosatiConjugation (A.pullback T.hom) ρ ∧
            PELModuli.IntegralModel.PEL.Has.HasIntegralLieRanks P R iotaO ((Over.map M.hom).obj T) (A.abelian.pullback T.hom) ρ) ↔
            ∃! f : T ⟶ Z, PELModuli.IntegralModel.Integral.ActionScheme.restrictIntegralAction A.abelian ρZ f = ρ := by
  have : IsNoetherianRing Γ(M.left, ⊤) :=
    IsLocallyNoetherian.component_noetherian ⟨⊤, isAffineOpen_top M.left⟩
  obtain ⟨d, _, L, hL, n, q, hq, he⟩ := PELModuli.IntegralModel.Affine.PolarizationEmbedding.polarized_exists_affine_section_embedding A
  exact Relative.PELActionScheme.exists_embedded_relative_pel_action_scheme D P iotaO M A L d hL q hq he hc

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.BoundedRelativePELAction
