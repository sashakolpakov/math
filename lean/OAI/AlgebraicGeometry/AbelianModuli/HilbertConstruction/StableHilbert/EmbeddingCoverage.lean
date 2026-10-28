import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.StableHilbert.CoordinateCoverage
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.PowerEmbedding.LinearCoordinateChange
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.ProjectiveFrame.PointNormalization

/-! # Embedding Coverage -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.StableHilbert.EmbeddingCoverage.StableHilbertCoverage

noncomputable section

/-! The stable chart coordinates are obtained by an actual invertible
coordinate change of the original power embedding. The original source,
tensor power, and complete linear system are retained. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
universe u
variable (R : Type u) [CommRing R] (B : Over (Spec (.of R)))
variable {X : Over B.left} {L : Line.Bundles.LineBundle X.left}
variable (E : Power.ProjectiveEmbeddings.PowerProjectiveEmbedding L X.hom) {m : ℕ}
variable (i : Fin m) (j : Stable.BalancedFrameIndex.StableBalancedFrameIndex.{u} (E.dimension + 1) m)
variable (x : Fin m → (Over.mk (𝟙 B.left) ⟶ X))
variable (e : ∀ z, (E.power.pullback (x z).left).sheaf ≅ Line.Bundles.structureModule B.left)

def embeddingVectors : Fin m → Fin (E.dimension + 1) → Γ(B.left, ⊤) :=
  fun z k => Family.FramedSectionEvaluation.familyFramedSectionValue E.power (x z).left (e z) (E.sections k)

variable (hv : IsUnit (Balanced.MonomialAlgebra.exponentMonomial
  (fun τ => LabeledDeterminantPolynomials.labeledDeterminant τ (embeddingVectors R B E x e)) j.exponent))

def embeddingChartPoint : B ⟶ Stable.ConfigurationPolynomialRankLocus.stableConfigurationPolynomialRankAmbient R i j :=
  CoordinateCoverage.StableHilbertCoverage.chartPoint R i j B (embeddingVectors R B E x e) hv

theorem exists_chart_normalizing_coordinates :
    ∃ a : (Fin (E.dimension + 1) →₀ Γ(B.left, ⊤)) ≃ₗ[Γ(B.left, ⊤)]
        (Fin (E.dimension + 1) →₀ Γ(B.left, ⊤)),
      (E.HasCompleteSections → (E.changeCoordinates a).HasCompleteSections) ∧
      ∀ z,
        x z ≫ (E.changeCoordinates a).projectivePresentation.embedding =
          Balanced.FrameChartProjectivePoints.balancedFrameChartProjectivePoint R i j.frame j.additional j.coordinate
            j.exponent j.complement j.balanced j.complete B.left
            ((embeddingChartPoint R B E i j x e hv).left.appTop.hom.comp
              (Scheme.ΓSpecIso (.of (Balanced.FrameChartCoordinates.balancedDeterminantChartRing R i j.exponent j.balanced))).inv.hom) z := by
  let v := embeddingVectors R B E x e
  let ρ := (embeddingChartPoint R B E i j x e hv).left.appTop.hom.comp
    (Scheme.ΓSpecIso (.of (Balanced.FrameChartCoordinates.balancedDeterminantChartRing R i j.exponent j.balanced))).inv.hom
  let w := fun z k => ρ (Balanced.FrameChartNormalization.balancedFrameChartVectors R i j.frame j.additional j.coordinate
    j.exponent j.complement j.balanced j.complete z k)
  obtain ⟨U, c, hc⟩ := CoordinateCoverage.StableHilbertCoverage.chartPoint_normalization R i j B v hv
  have hcoord (z k) : w z k = (c z : Γ(B.left, ⊤)) * U (v z) k := hc z k
  have hw (z) : ∀ y : B.left, ∃ k, y ∈ B.left.basicOpen (w z k) :=
    Balanced.FrameChartProjectivePoints.balancedFrameChartProjectiveCoordinates_cover R i j.frame j.additional j.coordinate
      j.exponent j.complement j.balanced j.complete B.left ρ z
  have hU (z) : ∀ y : B.left, ∃ k, y ∈ B.left.basicOpen (U (v z) k) := by
    intro y
    obtain ⟨k, hk⟩ := hw z y
    rw [hcoord, B.left.basicOpen_mul] at hk
    exact ⟨k, hk.2⟩
  refine ⟨(Dual.CoordinateTransform.pointCoordinateCoefficientTransform U).symm,
    fun h => Power.ProjectiveEmbeddings.PowerProjectiveEmbedding.HasCompleteSections.changeCoordinates E
      (Dual.CoordinateTransform.pointCoordinateCoefficientTransform U).symm h, fun z => ?_⟩
  let p₀ : X ⟶ Projective.ProjectivePresentations.projectiveSpaceOver B.left E.dimension := E.projectivePresentation.embedding
  let p₁ : X ⟶ Projective.ProjectivePresentations.projectiveSpaceOver B.left E.dimension :=
    (E.changeCoordinates (Dual.CoordinateTransform.pointCoordinateCoefficientTransform U).symm).projectivePresentation.embedding
  let q := Relative.LinearCoordinateIsomorphism.relativeLinearCoordinateIso E.dimension B.left (Dual.CoordinateTransform.pointCoordinateCoefficientTransform U).symm
  have hp : p₁ = p₀ ≫ q.hom := E.changeCoordinates_embedding _
  have hz : ∀ y : B.left, ∃ k, y ∈ B.left.basicOpen (v z k) :=
    Family.SectionProjectiveCoordinates.familySectionCoordinates_cover E.power E.sections E.covers (x z).left (e z)
  have hx : x z ≫ p₀ = Family.SectionProjectiveCoordinates.scalarCoordinateProjectivePoint (v z) hz :=
    Family.SectionProjectiveCoordinates.familySection_projectivePoint X.hom E.power E.sections E.covers
      (x z).left (x z).w (e z)
  change x z ≫ p₁ = Family.SectionProjectiveCoordinates.scalarCoordinateProjectivePoint (w z) (hw z)
  calc
    x z ≫ p₁ = x z ≫ (p₀ ≫ q.hom) := congrArg (fun k => x z ≫ k) hp
    _ = (x z ≫ p₀) ≫ q.hom := (Category.assoc _ _ _).symm
    _ = Family.SectionProjectiveCoordinates.scalarCoordinateProjectivePoint (v z) hz ≫ q.hom := congrArg (fun k => k ≫ q.hom) hx
    _ = Family.SectionProjectiveCoordinates.scalarCoordinateProjectivePoint (U (v z)) (hU z) :=
      Scalar.ProjectiveCoordinateAction.scalarCoordinateProjectivePoint_linear_action B.left (v z) U hz (hU z)
    _ = Family.SectionProjectiveCoordinates.scalarCoordinateProjectivePoint (w z) (hw z) :=
      (ProjectiveFrame.PointNormalization.scalarCoordinateProjectivePoint_eq_of_unit_mul B.left (w z) (U (v z))
        (c z) (hcoord z) (hw z) (hU z)).symm

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.StableHilbert.EmbeddingCoverage.StableHilbertCoverage
