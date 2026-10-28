import OAI.AlgebraicGeometry.PELModuli.IntegralModel.CM.EmbeddedGraphPowers
import OAI.AlgebraicGeometry.PELModuli.IntegralModel.SourcePowerHilbertPolynomial
import OAI.AlgebraicGeometry.PELModuli.IntegralModel.SegreSectionPowers
import OAI.AlgebraicGeometry.PELModuli.IntegralModel.Presentations.Coefficient

/-! # Source Hilbert Polynomial -/

namespace OAI.AlgebraicGeometry.PELModuli.IntegralModel.CM

noncomputable section

/-! Choose the CM graph polynomial from fixed source sections before
choosing any action, field extension, or Segre presentation. -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open _root_.CategoryTheory _root_.AlgebraicGeometry

attribute [local instance] MvPolynomial.gradedAlgebra

theorem GeneratorReconstruction.CMIntegralGeneratorData.exists_fixed_section_embedding_and_source_polynomial
    {E : Type} [Field E] [NumberField E] [Algebra ℚ E] [NumberField.IsCMField E]
    (D : GeneratorReconstruction.CMIntegralGeneratorData E)
    {k : Type} [Field k] [IsAlgClosed k] {g N : ℕ} {δ : Fin g → ℕ}
    (A : AbelianModuli.HilbertConstruction.PolarizationData.PolarizedAbelianWithFullLevel g δ N (Spec (.of k))) :
    ∃ (d : ℕ), 0 < d ∧ ∃ (P : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle A.abelian.scheme.left),
      AbelianModuli.HilbertConstruction.Tensor.Powers.IsTensorPower (PoincareClass.PoincareClasses.polarizationLine A.dual A.polarization.isogeny.hom).sheaf d P.sheaf ∧
      ∃ (n : ℕ) (s : Fin (n + 1) → (AbelianModuli.HilbertConstruction.Line.Bundles.structureModule A.abelian.scheme.left ⟶ P.sheaf))
        (hs : ∀ x : A.abelian.scheme.left, ∃ i, x ∈ AbelianModuli.HilbertConstruction.Ample.LineBundles.sectionNonvanishing (s i)),
        IsClosedImmersion (AbelianModuli.HilbertConstruction.SectionsProjectiveMorphism.sectionProjectiveMorphism A.abelian.scheme.hom s hs).left ∧
        ∃ (Q : Polynomial ℚ) (b : ℕ), ∀ m : ℕ, b ≤ m →
          (Module.finrank Γ(Spec (.of Γ(Spec (.of k), ⊤)), ⊤)
            ((SheafCohomology.Projective.AdditiveCoproductSections.baseGlobalSectionsFunctor (A.abelian.scheme.hom ≫ (Spec (.of k)).toSpecΓ)).obj
              (P.tensorPower ((D.multiplier ^ 2 + 1) * m)).sheaf) : ℚ) = Q.eval (m : ℚ) := by
  classical
  have hR : IsField Γ(Spec (.of k), ⊤) :=
    (Scheme.ΓSpecIso (.of k)).commRingCatIsoToRingEquiv.toMulEquiv.isField (Field.toIsField k)
  let := hR.toField
  obtain ⟨_, d, hd, P, hP, n, s, hs, he, _⟩ :=
    D.exists_fixed_section_embedding_and_graph_powers A
  let BA := SegreSectionPowers.PolarizationEmbedding.e34SectionPresentation A.abelian.scheme P s hs he
  have hf : IsClosedImmersion BA.coefficientEmbedding := Presentations.Coefficient.PolarizationEmbedding.e34CoefficientEmbedding_closed BA
  let := hf
  have htwists (m : ℕ) : Nonempty ((Scheme.Modules.pullback BA.coefficientEmbedding).obj
      (SheafCohomology.Projective.TwistPowers.MvPolynomial.coordinateHyperplanePoleSheafPower (R := Γ(Spec (.of k), ⊤))
        (0 : Fin (n + 1)) m) ≅ (P.tensorPower m).sheaf) := by
    change Nonempty ((Scheme.Modules.pullback
      (SegreSectionPowers.PolarizationEmbedding.e34SectionPresentation A.abelian.scheme P s hs he).coefficientEmbedding).obj _ ≅ _)
    rw [SegreSectionPowers.PolarizationEmbedding.e34SectionPresentation_coefficient]
    exact IntrinsicProjectivePowers.PolarizationEmbedding.nativeHyperplane_section_pullback P A.abelian.scheme.hom s hs 0 m
  obtain ⟨Q, b, hQ⟩ := SourcePowerHilbertPolynomial.PolarizationEmbedding.exists_sourcePower_sections_polynomial BA.coefficientEmbedding
    (A.abelian.scheme.hom ≫ (Spec (.of k)).toSpecΓ) (Presentations.Coefficient.PolarizationEmbedding.e34CoefficientEmbedding_over BA)
    0 P htwists (D.multiplier ^ 2 + 1) (Nat.succ_pos _)
  exact ⟨d, hd, P, hP, n, s, hs, he, Q, b, hQ⟩

end

end OAI.AlgebraicGeometry.PELModuli.IntegralModel.CM
