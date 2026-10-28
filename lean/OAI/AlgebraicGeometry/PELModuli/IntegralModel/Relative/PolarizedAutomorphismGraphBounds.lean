import OAI.AlgebraicGeometry.PELModuli.IntegralModel.Relative.CMPolarizationLine
import OAI.AlgebraicGeometry.PELModuli.IntegralModel.Relative.FieldSourceTwists
import OAI.AlgebraicGeometry.PELModuli.IntegralModel.Relative.FieldGraphTwists
import OAI.AlgebraicGeometry.PELModuli.IntegralModel.Relative.ScaledPolynomialBounds
import OAI.AlgebraicGeometry.PELModuli.IntegralModel.PolarizationLineTransport

/-! # Polarized Automorphism Graph Bounds -/

namespace OAI

noncomputable section

namespace AlgebraicGeometry.PELModuli.IntegralModel

/-! A canonical section embedding of a varying polarized family gives
a finite bound on the actual CM graph polynomials. The bound is chosen
before the geometric field, the action, and the Segre presentation. -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

theorem CM.GeneratorReconstruction.CMIntegralGeneratorData.exists_finite_relative_geometric_graph_polynomials
    {E : Type} [Field E] [NumberField E] [Algebra ℚ E] [NumberField.IsCMField E]
    (D : CM.GeneratorReconstruction.CMIntegralGeneratorData E)
    {S : Scheme.{0}} [IsAffine S] [IsLocallyNoetherian S]
    {g N : ℕ} {δ : Fin g → ℕ} (A : AbelianModuli.HilbertConstruction.PolarizationData.PolarizedAbelianWithFullLevel g δ N S)
    (P : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle A.abelian.scheme.left) (d : ℕ)
    (hP : AbelianModuli.HilbertConstruction.Tensor.Powers.IsTensorPower (Relative.PoincareSimilitude.RelativePoincareClasses.polarizationLine A.dual
      A.polarization.isogeny.hom).sheaf d P.sheaf)
    {n : ℕ} (s : Fin (n + 1) → (AbelianModuli.HilbertConstruction.Line.Bundles.structureModule A.abelian.scheme.left ⟶ P.sheaf))
    (hs : ∀ x : A.abelian.scheme.left, ∃ i, x ∈ AbelianModuli.HilbertConstruction.Ample.LineBundles.sectionNonvanishing (s i))
    (he : IsClosedImmersion (AbelianModuli.HilbertConstruction.SectionsProjectiveMorphism.sectionProjectiveMorphism A.abelian.scheme.hom s hs).left) :
    ∃ F : Finset (Polynomial ℚ),
      ∀ (B : HilbertScheme.Presentations.Has.Core.ProjectivePresentation (A.abelian.scheme ⨯ A.abelian.scheme)),
        HilbertScheme.Presentations.Segre.Open.Core.IsSegrePresentation (SegreSectionPowers.PolarizationEmbedding.e34SectionPresentation A.abelian.scheme P s hs he)
          (SegreSectionPowers.PolarizationEmbedding.e34SectionPresentation A.abelian.scheme P s hs he) B →
        ∀ (K : Type) [Field K] [IsAlgClosed K] (a : Spec (.of K) ⟶ S)
          (ρ : AbelianModuli.ReferenceFamily.ActionData.IntegralAction (NumberField.RingOfIntegers E) (A.pullback a).abelian),
          AbelianModuli.ReferenceFamily.ActionData.RosatiConjugation (A.pullback a) ρ →
          ∃ Q ∈ F, HilbertScheme.Presentations.Hilbert.Polynomial.GradedHilbert.HasHilbertPolynomial (HilbertScheme.Presentations.ChartHomogeneousIdeal.GradedHilbert.homogeneousIdealOfSheaf
            (Relative.FieldGraphEmbeddings.PolarizationEmbedding.relativeFieldGraphEmbedding A.abelian B a (ρ.map D.generator)).ker).toIdeal Q := by
  classical
  let : IsNoetherianRing Γ(S, ⊤) :=
    IsLocallyNoetherian.component_noetherian ⟨⊤, isAffineOpen_top S⟩
  let BA := SegreSectionPowers.PolarizationEmbedding.e34SectionPresentation A.abelian.scheme P s hs he
  have : IsClosedImmersion BA.coefficientEmbedding := Presentations.Coefficient.PolarizationEmbedding.e34CoefficientEmbedding_closed BA
  obtain ⟨F, hF⟩ := Relative.ScaledPolynomialBounds.PolarizationEmbedding.exists_finite_scaled_fiber_polynomials BA.coefficientEmbedding
    (D.multiplier ^ 2 + 1) (Nat.succ_pos _)
  refine ⟨F, fun B hB K _ _ a ρ hρ => ?_⟩
  let j := Relative.FieldSourceEmbedding.PolarizationEmbedding.relativeFieldSourceEmbedding BA a
  let v := ρ.map D.generator
  let f := Relative.FieldGraphEmbeddings.PolarizationEmbedding.relativeFieldGraphEmbedding A.abelian B a v
  have : IsClosedImmersion f := Relative.FieldGraphEmbeddings.PolarizationEmbedding.relativeFieldGraphEmbedding_closed A.abelian B a v
  have hb : f ≫ SheafCohomology.Projective.MvPolynomialClosure.MvPolynomial.homogeneousProjπ (R := K) =
      j ≫ SheafCohomology.Projective.MvPolynomialClosure.MvPolynomial.homogeneousProjπ (R := K) :=
    (Relative.FieldGraphEmbeddings.PolarizationEmbedding.relativeFieldGraphEmbedding_over A.abelian B a v).trans
      (Relative.FieldSourceEmbedding.PolarizationEmbedding.relativeFieldSourceEmbedding_over BA a).symm
  have hv := D.geometric_relative_polarization_power A a P d hP ρ hρ
  apply hF K (AbelianModuli.HilbertConstruction.AffineProjective.Charts.affinePointCoefficients a).hom (A.pullback a).abelian.scheme.left j
    (pullback.fst A.abelian.scheme.hom a) (Relative.FieldSourceEmbedding.PolarizationEmbedding.relativeFieldSourceEmbedding_isPullback BA a)
    B.dimension f hb
  intro m
  obtain ⟨e⟩ := Relative.FieldGraphTwists.PolarizationEmbedding.relativeFieldGraphEmbedding_twists A.abelian B a v P s hs he hB 0 m
  obtain ⟨q⟩ := Relative.GraphPolarizationPowers.PolarizationEmbedding.relativeGraphToProduct_power A.abelian (Over.mk a) v P (D.multiplier ^ 2) m hv
  obtain ⟨t⟩ := Relative.FieldSourceTwists.PolarizationEmbedding.relativeFieldSourceEmbedding_twists A.abelian.scheme P s hs he a 0
    ((D.multiplier ^ 2 + 1) * m)
  exact ⟨e ≪≫ q ≪≫ t.symm⟩

end AlgebraicGeometry.PELModuli.IntegralModel

namespace AlgebraicGeometry.PELModuli.IntegralModel.Relative.PolarizedAutomorphismGraphBounds

/-! Graph polynomials of polarized automorphisms have a finite bound
chosen before the geometric field or automorphism. The bound follows
from preservation of the actual canonical polarization line. -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

open OAI.AlgebraicGeometry.PELModuli.IntegralModel.PolarizationLineTransport.PolarizationAmpleness

theorem geometric_polarized_automorphism_preserves_embedding_line
    {S : Scheme.{0}} {g N : ℕ} {δ : Fin g → ℕ}
    (A : AbelianModuli.HilbertConstruction.PolarizationData.PolarizedAbelianWithFullLevel g δ N S)
    {k : Type} [Field k] (f : Spec (.of k) ⟶ S)
    (P : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle A.abelian.scheme.left) (d : ℕ)
    (hP : AbelianModuli.HilbertConstruction.Tensor.Powers.IsTensorPower (PoincareSimilitude.RelativePoincareClasses.polarizationLine A.dual
      A.polarization.isogeny.hom).sheaf d P.sheaf)
    (e : AbelianModuli.HilbertConstruction.Moduli.Isomorphisms.LevelPreservingIso (A.pullback f) (A.pullback f)) :
    let Q := P.pullback (pullback.fst A.abelian.scheme.hom f)
    Picard.Homomorphisms.SchemePullback.Construction.schemePicardPullback e.abelian.hom.left (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf Q) = AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf Q := by
  let L := PoincareClass.PoincareClasses.polarizationLine (A.pullback f).dual (A.pullback f).polarization.isogeny.hom
  let Q := P.pullback (pullback.fst A.abelian.scheme.hom f)
  have hc : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf Q = AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf L ^ d := by
    change Picard.Homomorphisms.SchemePullback.Construction.schemePicardPullback (pullback.fst A.abelian.scheme.hom f) (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf P) = _
    rw [CM.EmbeddedGraphPowers.tensorPowerWitness_class _ P d hP, map_pow]
    exact congrArg (fun c : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.IsoClass (A.pullback f).abelian.scheme.left => c ^ d)
      (CMPolarizationLine.RelativePoincareClasses.polarizationLine_baseChange_class A.dual A.polarization.isogeny.hom f).symm
  change Picard.Homomorphisms.SchemePullback.Construction.schemePicardPullback e.abelian.hom.left (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf Q) = AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf Q
  rw [hc, map_pow]
  exact congrArg (fun c => c ^ d) (PolarizationLineTransport.PolarizationAmpleness.polarizationLine_transport e)

theorem exists_finite_polarized_automorphism_graph_polynomials
    {S : Scheme.{0}} [IsAffine S] [IsLocallyNoetherian S]
    {g N : ℕ} {δ : Fin g → ℕ} (A : AbelianModuli.HilbertConstruction.PolarizationData.PolarizedAbelianWithFullLevel g δ N S)
    (P : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle A.abelian.scheme.left) (d : ℕ)
    (hP : AbelianModuli.HilbertConstruction.Tensor.Powers.IsTensorPower (PoincareSimilitude.RelativePoincareClasses.polarizationLine A.dual
      A.polarization.isogeny.hom).sheaf d P.sheaf)
    {n : ℕ} (s : Fin (n + 1) → (AbelianModuli.HilbertConstruction.Line.Bundles.structureModule A.abelian.scheme.left ⟶ P.sheaf))
    (hs : ∀ x : A.abelian.scheme.left, ∃ i, x ∈ AbelianModuli.HilbertConstruction.Ample.LineBundles.sectionNonvanishing (s i))
    (he : IsClosedImmersion (AbelianModuli.HilbertConstruction.SectionsProjectiveMorphism.sectionProjectiveMorphism A.abelian.scheme.hom s hs).left) :
    ∃ F : Finset (Polynomial ℚ),
      ∀ (B : HilbertScheme.Presentations.Has.Core.ProjectivePresentation (A.abelian.scheme ⨯ A.abelian.scheme)),
        HilbertScheme.Presentations.Segre.Open.Core.IsSegrePresentation (SegreSectionPowers.PolarizationEmbedding.e34SectionPresentation A.abelian.scheme P s hs he)
          (SegreSectionPowers.PolarizationEmbedding.e34SectionPresentation A.abelian.scheme P s hs he) B →
        ∀ (K : Type) [Field K] [IsAlgClosed K] (a : Spec (.of K) ⟶ S)
          (e : AbelianModuli.HilbertConstruction.Moduli.Isomorphisms.LevelPreservingIso (A.pullback a) (A.pullback a)),
          ∃ Q ∈ F, HilbertScheme.Presentations.Hilbert.Polynomial.GradedHilbert.HasHilbertPolynomial (HilbertScheme.Presentations.ChartHomogeneousIdeal.GradedHilbert.homogeneousIdealOfSheaf
            (FieldGraphEmbeddings.PolarizationEmbedding.relativeFieldGraphEmbedding A.abelian B a e.abelian.hom).ker).toIdeal Q := by
  classical
  let : IsNoetherianRing Γ(S, ⊤) :=
    IsLocallyNoetherian.component_noetherian ⟨⊤, isAffineOpen_top S⟩
  let BA := SegreSectionPowers.PolarizationEmbedding.e34SectionPresentation A.abelian.scheme P s hs he
  have : IsClosedImmersion BA.coefficientEmbedding := Presentations.Coefficient.PolarizationEmbedding.e34CoefficientEmbedding_closed BA
  obtain ⟨F, hF⟩ := ScaledPolynomialBounds.PolarizationEmbedding.exists_finite_scaled_fiber_polynomials BA.coefficientEmbedding 2 (by decide)
  refine ⟨F, fun B hB K _ _ a e => ?_⟩
  let j := FieldSourceEmbedding.PolarizationEmbedding.relativeFieldSourceEmbedding BA a
  let v := e.abelian.hom
  let f := FieldGraphEmbeddings.PolarizationEmbedding.relativeFieldGraphEmbedding A.abelian B a v
  have : IsClosedImmersion f := FieldGraphEmbeddings.PolarizationEmbedding.relativeFieldGraphEmbedding_closed A.abelian B a v
  have hb : f ≫ SheafCohomology.Projective.MvPolynomialClosure.MvPolynomial.homogeneousProjπ (R := K) =
      j ≫ SheafCohomology.Projective.MvPolynomialClosure.MvPolynomial.homogeneousProjπ (R := K) :=
    (FieldGraphEmbeddings.PolarizationEmbedding.relativeFieldGraphEmbedding_over A.abelian B a v).trans
      (FieldSourceEmbedding.PolarizationEmbedding.relativeFieldSourceEmbedding_over BA a).symm
  have hv := geometric_polarized_automorphism_preserves_embedding_line A a P d hP e
  apply hF K (AbelianModuli.HilbertConstruction.AffineProjective.Charts.affinePointCoefficients a).hom (A.pullback a).abelian.scheme.left j
    (pullback.fst A.abelian.scheme.hom a) (FieldSourceEmbedding.PolarizationEmbedding.relativeFieldSourceEmbedding_isPullback BA a)
    B.dimension f hb
  intro m
  obtain ⟨b⟩ := FieldGraphTwists.PolarizationEmbedding.relativeFieldGraphEmbedding_twists A.abelian B a v P s hs he hB 0 m
  obtain ⟨q⟩ := GraphPolarizationPowers.PolarizationEmbedding.relativeGraphToProduct_power A.abelian (Over.mk a) v P 1 m (by
    exact hv.trans (pow_one _).symm)
  obtain ⟨t⟩ := FieldSourceTwists.PolarizationEmbedding.relativeFieldSourceEmbedding_twists A.abelian.scheme P s hs he a 0 (2 * m)
  exact ⟨b ≪≫ q ≪≫ t.symm⟩

end AlgebraicGeometry.PELModuli.IntegralModel.Relative.PolarizedAutomorphismGraphBounds

end

end OAI
