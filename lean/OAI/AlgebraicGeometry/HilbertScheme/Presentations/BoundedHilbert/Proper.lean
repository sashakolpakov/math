import OAI.AlgebraicGeometry.HilbertScheme.Presentations.BoundedHilbert.ValuativeCriterion
import OAI.AlgebraicGeometry.HilbertScheme.Presentations.BoundedHilbert.StructureProperties
import OAI.AlgebraicGeometry.HilbertScheme.Presentations.Relative.GrassmannianProjectivity

/-! # Proper -/

namespace OAI.AlgebraicGeometry.HilbertScheme.Presentations.BoundedHilbert.Proper.GradedHilbert

noncomputable section

/-! Valuation-ring lifts make the actual bounded Hilbert scheme proper.
Its immersion into the Grassmannian is therefore a closed immersion. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u
variable {ι : Type u} [Fintype ι] [DecidableEq ι] {n N : ℕ}
variable {S : Scheme.{u}} [IsLocallyNoetherian S]
variable (P : Polynomial ℚ)
variable (hP : DegreeLocus.GradedHilbert.RankProfileRealizes.{u} n N (Presentations.Polynomial.DegreeRankProfile.GradedHilbert.polynomialDegreeRankProfile.{u} n N P) P)
variable (hN : Hilbert.Truncation.GradedHilbert.hilbertParameterDegree.{u} n P ≤ N)
variable (hr : Fintype.card ι = (P.eval (N : ℚ)).num.toNat)
include hP hN hr

theorem boundedHilbertOver_isProper :
    IsProper (Data.GradedHilbert.boundedHilbertOver (ι := ι) n N S (Presentations.Polynomial.DegreeRankProfile.GradedHilbert.polynomialDegreeRankProfile.{u} n N P)).hom := by
  let : UniversallyClosed (Data.GradedHilbert.boundedHilbertOver (ι := ι) n N S (Presentations.Polynomial.DegreeRankProfile.GradedHilbert.polynomialDegreeRankProfile.{u} n N P)).hom :=
    UniversallyClosed.of_valuativeCriterion _ (ValuativeCriterion.GradedHilbert.boundedHilbert_valuative_existence P hP hN hr)
  exact ⟨⟩

theorem boundedHilbertParameter_isClosedImmersion :
    IsClosedImmersion (Data.GradedHilbert.boundedHilbertParameter (ι := ι) n N S (Presentations.Polynomial.DegreeRankProfile.GradedHilbert.polynomialDegreeRankProfile.{u} n N P)) := by
  let q := Presentations.Polynomial.DegreeRankProfile.GradedHilbert.polynomialDegreeRankProfile.{u} n N P
  let p := Data.GradedHilbert.boundedHilbertParameter (ι := ι) n N S q
  let g := Grassmannian.Gluing.grassmannianStructureMap (ι := ι) (ν := Homogeneous.CoordinateBasis.GradedHilbert.DegreeIndex.{u} n N) S
  let : IsProper (p ≫ g) := boundedHilbertOver_isProper P hP hN hr
  let : IsProper p := IsProper.of_comp p g
  exact IsClosedImmersion.of_isPreimmersion p p.isClosedMap.isClosed_range

theorem boundedHilbert_projective_embedding :
    ∃ e : (Data.GradedHilbert.boundedHilbertOver (ι := ι) n N S (Presentations.Polynomial.DegreeRankProfile.GradedHilbert.polynomialDegreeRankProfile.{u} n N P)).left ⟶
      Relative.GrassmannianProjectivity.PolynomialProjective.relativeProjectiveSpace (ι → Homogeneous.CoordinateBasis.GradedHilbert.DegreeIndex.{u} n N) S,
      IsClosedImmersion e ∧ e ≫ Relative.GrassmannianProjectivity.PolynomialProjective.relativeProjectiveSpaceProjection (ι → Homogeneous.CoordinateBasis.GradedHilbert.DegreeIndex.{u} n N) S =
        (Data.GradedHilbert.boundedHilbertOver (ι := ι) n N S (Presentations.Polynomial.DegreeRankProfile.GradedHilbert.polynomialDegreeRankProfile.{u} n N P)).hom := by
  let p : (Data.GradedHilbert.boundedHilbertOver (ι := ι) n N S (Presentations.Polynomial.DegreeRankProfile.GradedHilbert.polynomialDegreeRankProfile.{u} n N P)).left ⟶
      Grassmannian.Gluing.grassmannianScheme (ι := ι) (ν := Homogeneous.CoordinateBasis.GradedHilbert.DegreeIndex.{u} n N) S :=
    Data.GradedHilbert.boundedHilbertParameter (ι := ι) n N S (Presentations.Polynomial.DegreeRankProfile.GradedHilbert.polynomialDegreeRankProfile.{u} n N P)
  let : IsClosedImmersion p := boundedHilbertParameter_isClosedImmersion P hP hN hr
  refine ⟨p ≫ Relative.GrassmannianProjectivity.Grassmannian.relativeGrassmannianPluckerEmbedding (ι := ι) (ν := Homogeneous.CoordinateBasis.GradedHilbert.DegreeIndex.{u} n N) S,
    inferInstance, ?_⟩
  rw [Category.assoc, Relative.GrassmannianProjectivity.Grassmannian.relativeGrassmannianPluckerEmbedding_over]
  rfl

end

end OAI.AlgebraicGeometry.HilbertScheme.Presentations.BoundedHilbert.Proper.GradedHilbert
