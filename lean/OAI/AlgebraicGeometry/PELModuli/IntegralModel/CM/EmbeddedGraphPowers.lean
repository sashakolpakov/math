import OAI.AlgebraicGeometry.PELModuli.IntegralModel.CM.PolarizationLine
import OAI.AlgebraicGeometry.PELModuli.IntegralModel.PolarizationLineTransport
import OAI.AlgebraicGeometry.PELModuli.IntegralModel.AmpleSectionEmbedding
import OAI.AlgebraicGeometry.PELModuli.IntegralModel.GraphPowerSections

/-! # Embedded Graph Powers -/

namespace OAI.AlgebraicGeometry.PELModuli.IntegralModel.CM

noncomputable section

/-! Choose a single closed section embedding independently of the CM
action, while retaining the fixed power identities for every generator
graph in the chosen polarization. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

open OAI.AlgebraicGeometry.PELModuli.IntegralModel.PolarizationLineTransport.PolarizationAmpleness

universe u

theorem EmbeddedGraphPowers.tensorPowerWitness_class {X : Scheme.{u}} (L P : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle X) (d : ℕ)
    (hP : AbelianModuli.HilbertConstruction.Tensor.Powers.IsTensorPower L.sheaf d P.sheaf) :
    AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf P = AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf L ^ d :=
  (show AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf P = AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf (L.tensorPower d) from
    Quotient.sound (hP.unique (L.tensorPower_isTensorPower d))).trans (AmpleTensor.PolarizationAmpleness.tensorPower_class L d)

variable {E : Type} [Field E] [NumberField E] [Algebra ℚ E] [NumberField.IsCMField E]
  (D : GeneratorReconstruction.CMIntegralGeneratorData E)
  {k : Type} [Field k] [IsAlgClosed k] {g N : ℕ} {δ : Fin g → ℕ}
  (A : AbelianModuli.HilbertConstruction.PolarizationData.PolarizedAbelianWithFullLevel g δ N (Spec (.of k)))

/-- Both the section coordinates and their line bundle are fixed before
the action is supplied. All resulting graph powers have the same source
line-bundle class, with exponent determined only by the CM generator. -/
theorem GeneratorReconstruction.CMIntegralGeneratorData.exists_fixed_section_embedding_and_graph_powers :
    let L := PoincareClass.PoincareClasses.polarizationLine A.dual A.polarization.isogeny.hom
    L.IsAmple ∧ ∃ (d : ℕ), 0 < d ∧ ∃ (P : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle A.abelian.scheme.left),
      AbelianModuli.HilbertConstruction.Tensor.Powers.IsTensorPower L.sheaf d P.sheaf ∧
      ∃ (n : ℕ) (s : Fin (n + 1) → (AbelianModuli.HilbertConstruction.Line.Bundles.structureModule A.abelian.scheme.left ⟶ P.sheaf))
        (hs : ∀ x : A.abelian.scheme.left, ∃ i, x ∈ AbelianModuli.HilbertConstruction.Ample.LineBundles.sectionNonvanishing (s i)),
        IsClosedImmersion (AbelianModuli.HilbertConstruction.SectionsProjectiveMorphism.sectionProjectiveMorphism A.abelian.scheme.hom s hs).left ∧
        ∀ (ρ : AbelianModuli.ReferenceFamily.ActionData.IntegralAction (NumberField.RingOfIntegers E) A.abelian),
          AbelianModuli.ReferenceFamily.ActionData.RosatiConjugation A ρ → ∀ m : ℕ, Nonempty
            ((((GraphPolarizationPowers.GraphPolarization.productLine A.abelian.scheme P).tensorPower m).pullback
              (GraphPolarizationPowers.GraphPolarization.graph A.abelian.scheme (ρ.map D.generator)).left).sheaf ≅
              (P.tensorPower ((D.multiplier ^ 2 + 1) * m)).sheaf) := by
  let L := PoincareClass.PoincareClasses.polarizationLine A.dual A.polarization.isogeny.hom
  have hL : L.IsAmple := PolarizationLineTransport.PolarizationAmpleness.polarizationLine_isAmple A
  obtain ⟨d, hd, P, hP, n, s, hs, he⟩ :=
    AmpleSectionEmbedding.PolarizationEmbedding.exists_closed_section_embedding L A.abelian.scheme.hom hL
  refine ⟨hL, d, hd, P, hP, n, s, hs, he, fun ρ hρ m => ?_⟩
  have hc : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf P = AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf L ^ d := EmbeddedGraphPowers.tensorPowerWitness_class L P d hP
  have hfL : Picard.Homomorphisms.SchemePullback.Construction.schemePicardPullback (ρ.map D.generator).left (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf L) =
      AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf L ^ (D.multiplier ^ 2) := by
    have h : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf (L.pullback (ρ.map D.generator).left) =
        AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf (L.tensorPower (D.multiplier ^ 2)) :=
      Quotient.sound (D.polarizationLine_power A ρ hρ)
    exact h.trans (AmpleTensor.PolarizationAmpleness.tensorPower_class L (D.multiplier ^ 2))
  have hfP : Picard.Homomorphisms.SchemePullback.Construction.schemePicardPullback (ρ.map D.generator).left (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf P) =
      AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf P ^ (D.multiplier ^ 2) := by
    rw [hc, map_pow, hfL, ← pow_mul, ← pow_mul, Nat.mul_comm d]
  have h : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf
        (((GraphPolarizationPowers.GraphPolarization.productLine A.abelian.scheme P).tensorPower m).pullback
          (GraphPolarizationPowers.GraphPolarization.graph A.abelian.scheme (ρ.map D.generator)).left) =
      AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf (P.tensorPower ((D.multiplier ^ 2 + 1) * m)) := by
    change Picard.Homomorphisms.SchemePullback.Construction.schemePicardPullback (GraphPolarizationPowers.GraphPolarization.graph A.abelian.scheme (ρ.map D.generator)).left
      (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf ((GraphPolarizationPowers.GraphPolarization.productLine A.abelian.scheme P).tensorPower m)) = _
    rw [AmpleTensor.PolarizationAmpleness.tensorPower_class, map_pow, GraphPolarizationPowers.GraphPolarization.graph_product_class, hfP,
      ← pow_succ', ← pow_mul, AmpleTensor.PolarizationAmpleness.tensorPower_class]
  exact Quotient.exact h

end

end OAI.AlgebraicGeometry.PELModuli.IntegralModel.CM
