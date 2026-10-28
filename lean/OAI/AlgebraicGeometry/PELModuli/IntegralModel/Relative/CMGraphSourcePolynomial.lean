import OAI.AlgebraicGeometry.PELModuli.IntegralModel.Relative.CMFieldGraphBounds
import OAI.AlgebraicGeometry.PELModuli.IntegralModel.Relative.SourcePolynomial

/-! # CM Graph Source Polynomial -/

namespace OAI

noncomputable section

namespace AlgebraicGeometry.PELModuli.IntegralModel

/-! The actual CM graph polynomial is the fixed scaling of the source
fiber polynomial at the base point, including actions first acquired
over an arbitrary coefficient field. -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

open OAI.AlgebraicGeometry.PELModuli.IntegralModel.Relative.SourcePolynomial.PolarizationEmbedding
variable {E : Type} [Field E] [NumberField E] [Algebra ℚ E] [NumberField.IsCMField E]
    (D : CM.GeneratorReconstruction.CMIntegralGeneratorData E)
    {S : Scheme.{0}} [IsAffine S] [IsLocallyNoetherian S]
    {g N : ℕ} {δ : Fin g → ℕ} (A : AbelianModuli.HilbertConstruction.PolarizationData.PolarizedAbelianWithFullLevel g δ N S)
    (P : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle A.abelian.scheme.left) (d : ℕ)
    (hP : AbelianModuli.HilbertConstruction.Tensor.Powers.IsTensorPower (Relative.PoincareSimilitude.RelativePoincareClasses.polarizationLine A.dual
      A.polarization.isogeny.hom).sheaf d P.sheaf)
    {n : ℕ} (s : Fin (n + 1) → (AbelianModuli.HilbertConstruction.Line.Bundles.structureModule A.abelian.scheme.left ⟶ P.sheaf))
    (hs : ∀ x : A.abelian.scheme.left, ∃ i, x ∈ AbelianModuli.HilbertConstruction.Ample.LineBundles.sectionNonvanishing (s i))
    (he : IsClosedImmersion (AbelianModuli.HilbertConstruction.SectionsProjectiveMorphism.sectionProjectiveMorphism A.abelian.scheme.hom s hs).left)
    (B : HilbertScheme.Presentations.Has.Core.ProjectivePresentation (A.abelian.scheme ⨯ A.abelian.scheme))
    (hB : HilbertScheme.Presentations.Segre.Open.Core.IsSegrePresentation (SegreSectionPowers.PolarizationEmbedding.e34SectionPresentation A.abelian.scheme P s hs he)
      (SegreSectionPowers.PolarizationEmbedding.e34SectionPresentation A.abelian.scheme P s hs he) B)

include hP hB in
theorem CM.GeneratorReconstruction.CMIntegralGeneratorData.relative_geometric_graph_source_polynomial
    {K : Type} [Field K] [IsAlgClosed K] (a : Spec (.of K) ⟶ S)
    (ρ : AbelianModuli.ReferenceFamily.ActionData.IntegralAction (NumberField.RingOfIntegers E) (A.pullback a).abelian)
    (hρ : AbelianModuli.ReferenceFamily.ActionData.RosatiConjugation (A.pullback a) ρ) :
    HilbertScheme.Presentations.Hilbert.Polynomial.GradedHilbert.HasHilbertPolynomial (HilbertScheme.Presentations.ChartHomogeneousIdeal.GradedHilbert.homogeneousIdealOfSheaf
      (Relative.FieldGraphEmbeddings.PolarizationEmbedding.relativeFieldGraphEmbedding A.abelian B a (ρ.map D.generator)).ker).toIdeal
        ((Relative.SourcePolynomial.PolarizationEmbedding.e34SourceHilbertPolynomial (SegreSectionPowers.PolarizationEmbedding.e34SectionPresentation A.abelian.scheme P s hs he)
          (a (IsLocalRing.closedPoint K))).comp
            (Polynomial.C ((D.multiplier ^ 2 + 1 : ℕ) : ℚ) * Polynomial.X)) := by
  let BA := SegreSectionPowers.PolarizationEmbedding.e34SectionPresentation A.abelian.scheme P s hs he
  let j := Relative.FieldSourceEmbedding.PolarizationEmbedding.relativeFieldSourceEmbedding BA a
  let v := ρ.map D.generator
  let f := Relative.FieldGraphEmbeddings.PolarizationEmbedding.relativeFieldGraphEmbedding A.abelian B a v
  have : IsClosedImmersion j := Relative.FieldSourceEmbedding.PolarizationEmbedding.relativeFieldSourceEmbedding_closed BA a
  have : IsClosedImmersion f := Relative.FieldGraphEmbeddings.PolarizationEmbedding.relativeFieldGraphEmbedding_closed A.abelian B a v
  have hb : f ≫ SheafCohomology.Projective.MvPolynomialClosure.MvPolynomial.homogeneousProjπ (R := K) =
      j ≫ SheafCohomology.Projective.MvPolynomialClosure.MvPolynomial.homogeneousProjπ (R := K) :=
    (Relative.FieldGraphEmbeddings.PolarizationEmbedding.relativeFieldGraphEmbedding_over A.abelian B a v).trans
      (Relative.FieldSourceEmbedding.PolarizationEmbedding.relativeFieldSourceEmbedding_over BA a).symm
  have hv := D.geometric_relative_polarization_power A a P d hP ρ hρ
  apply ScaledTwistHilbertPolynomial.PolarizationEmbedding.e34HilbertPolynomial_of_scaled_twists j f hb (D.multiplier ^ 2 + 1) (Nat.succ_pos _)
    _ _ (Relative.SourcePolynomial.PolarizationEmbedding.relativeFieldSourceEmbedding_hasHilbertPolynomial BA a)
  intro m
  obtain ⟨e⟩ := Relative.FieldGraphTwists.PolarizationEmbedding.relativeFieldGraphEmbedding_twists A.abelian B a v P s hs he hB 0 m
  obtain ⟨q⟩ := Relative.GraphPolarizationPowers.PolarizationEmbedding.relativeGraphToProduct_power A.abelian (Over.mk a) v P (D.multiplier ^ 2) m hv
  obtain ⟨t⟩ := Relative.FieldSourceTwists.PolarizationEmbedding.relativeFieldSourceEmbedding_twists A.abelian.scheme P s hs he a 0
    ((D.multiplier ^ 2 + 1) * m)
  exact ⟨e ≪≫ q ≪≫ t.symm⟩

include hP hB in
theorem CM.GeneratorReconstruction.CMIntegralGeneratorData.relative_field_graph_source_polynomial
    {K : Type} [Field K] (a : Spec (.of K) ⟶ S)
    (ρ : AbelianModuli.ReferenceFamily.ActionData.IntegralAction (NumberField.RingOfIntegers E) (A.pullback a).abelian)
    (hρ : AbelianModuli.ReferenceFamily.ActionData.RosatiConjugation (A.pullback a) ρ) :
    HilbertScheme.Presentations.Hilbert.Polynomial.GradedHilbert.HasHilbertPolynomial (HilbertScheme.Presentations.ChartHomogeneousIdeal.GradedHilbert.homogeneousIdealOfSheaf
      (Relative.FieldGraphEmbeddings.PolarizationEmbedding.relativeFieldGraphEmbedding A.abelian B a (ρ.map D.generator)).ker).toIdeal
        ((Relative.SourcePolynomial.PolarizationEmbedding.e34SourceHilbertPolynomial (SegreSectionPowers.PolarizationEmbedding.e34SectionPresentation A.abelian.scheme P s hs he)
          (a (IsLocalRing.closedPoint K))).comp
            (Polynomial.C ((D.multiplier ^ 2 + 1 : ℕ) : ℚ) * Polynomial.X)) := by
  let L := AlgebraicClosure K
  let β := Spec.map (CommRingCat.ofHom (algebraMap K L))
  let b : Over.mk (β ≫ a) ⟶ Over.mk a := Over.homMk β rfl
  let σ := Integral.ActionScheme.restrictIntegralAction A.abelian ρ b
  have hσ : AbelianModuli.ReferenceFamily.ActionData.RosatiConjugation (A.pullback (β ≫ a)) σ :=
    RosatiRestriction.rosati_restrictIntegralAction (T := Over.mk (β ≫ a)) (U := Over.mk a)
      (E := E) A ρ hρ b
  have hp := D.relative_geometric_graph_source_polynomial A P d hP s hs he B hB (β ≫ a) σ hσ
  have hx : (β ≫ a) (IsLocalRing.closedPoint L) = a (IsLocalRing.closedPoint K) := by
    change a (β (IsLocalRing.closedPoint L)) = a (IsLocalRing.closedPoint K)
    exact congrArg (fun x => a x) (Subsingleton.elim _ _)
  have hQ := congrArg (fun x : S =>
    (Relative.SourcePolynomial.PolarizationEmbedding.e34SourceHilbertPolynomial (SegreSectionPowers.PolarizationEmbedding.e34SectionPresentation A.abelian.scheme P s hs he) x).comp
      (Polynomial.C ((D.multiplier ^ 2 + 1 : ℕ) : ℚ) * Polynomial.X)) hx
  exact (FieldGraphBaseChange.PolarizationEmbedding.relativeIntegralGraph_hilbertPolynomial_baseChange_iff
    a (algebraMap K L) A.abelian B ρ D.generator _).mp (hQ ▸ hp)

end AlgebraicGeometry.PELModuli.IntegralModel

namespace AlgebraicGeometry.PELModuli.IntegralModel.Relative.CMGraphSourcePolynomial

/-! The scaled source polynomial gives finitely many open-and-closed
strata of the base, chosen independently of all actions and tests. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

open OAI.AlgebraicGeometry.PELModuli.IntegralModel.Relative.SourcePolynomial.PolarizationEmbedding
variable {E : Type} [Field E] [NumberField E] [Algebra ℚ E] [NumberField.IsCMField E]
    (D : CM.GeneratorReconstruction.CMIntegralGeneratorData E)
    {S : Scheme.{0}} {X : Over S} (B : HilbertScheme.Presentations.Has.Core.ProjectivePresentation X)

def relativeCMGraphPolynomial (x : S) : Polynomial ℚ :=
  (SourcePolynomial.PolarizationEmbedding.e34SourceHilbertPolynomial B x).comp
    (Polynomial.C ((D.multiplier ^ 2 + 1 : ℕ) : ℚ) * Polynomial.X)

variable [IsAffine S] [IsLocallyNoetherian S] [Flat X.hom]

theorem relativeCMGraphPolynomial_isLocallyConstant : IsLocallyConstant (relativeCMGraphPolynomial D B) :=
  (SourcePolynomial.PolarizationEmbedding.e34SourceHilbertPolynomial_isLocallyConstant B).comp
    (fun P => P.comp (Polynomial.C ((D.multiplier ^ 2 + 1 : ℕ) : ℚ) * Polynomial.X))

def relativeCMPolynomialOpen (Q : Polynomial ℚ) : S.Opens :=
  ⟨{x | relativeCMGraphPolynomial D B x = Q},
    (relativeCMGraphPolynomial_isLocallyConstant D B).isOpen_fiber Q⟩

theorem relativeCMPolynomialOpen_isClopen (Q : Polynomial ℚ) :
    IsClopen (relativeCMPolynomialOpen D B Q : Set S) :=
  (relativeCMGraphPolynomial_isLocallyConstant D B).isClopen_fiber Q

theorem relativeCMPolynomialOpen_disjoint {Q P : Polynomial ℚ} (h : Q ≠ P) :
    Disjoint (relativeCMPolynomialOpen D B Q : Set S) (relativeCMPolynomialOpen D B P : Set S) := by
  apply Set.disjoint_left.mpr
  intro x hQ hP
  exact h (hQ.symm.trans hP)

theorem exists_finite_relativeCMPolynomial_cover :
    ∃ F : Finset (Polynomial ℚ), ∀ x : S, ∃ Q ∈ F, x ∈ relativeCMPolynomialOpen D B Q := by
  classical
  let hF := (relativeCMGraphPolynomial_isLocallyConstant D B).range_finite
  refine ⟨hF.toFinset, fun x => ?_⟩
  exact ⟨relativeCMGraphPolynomial D B x, hF.mem_toFinset.mpr ⟨x, rfl⟩, rfl⟩

end AlgebraicGeometry.PELModuli.IntegralModel.Relative.CMGraphSourcePolynomial

end

end OAI
