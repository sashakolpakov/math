import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Segre.StandardChartRingMap

/-! # Standard Chart Evaluation -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Segre.StandardChartEvaluation

noncomputable section

/-! The actual standard Segre embedding maps a normalized product chart
by the products of its row and column coordinates. This is an equality of
scheme morphisms, using the native graded projective map. -/
open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.MvPolynomial
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable {R A : Type u} [CommRing R] [CommRing A] [Algebra R A]
variable (𝒜 : ℕ → Submodule R A) [GradedAlgebra 𝒜]

theorem homogeneousAwayEquivOfEq_awayι {f g : A} (h : f = g) {k : ℕ}
    (hf : f ∈ 𝒜 k) (hg : g ∈ 𝒜 k) (hk : 0 < k) :
    Spec.map (CommRingCat.ofHom (StandardChartRingMap.homogeneousAwayEquivOfEq 𝒜 h).toRingHom) ≫
      Proj.awayι 𝒜 f hf hk = Proj.awayι 𝒜 g hg hk := by
  subst g
  change Spec.map (𝟙 (CommRingCat.of (HomogeneousLocalization.Away 𝒜 f))) ≫
    Proj.awayι 𝒜 f hf hk = Proj.awayι 𝒜 f hg hk
  rw [Spec.map_id, Category.id_comp]

variable (R) {n m d : ℕ} (e : ChartProjections.SegreProjectiveIndex.{u} n m ≃ Fin (d + 1)) (i : Fin (d + 1))
variable {T : Scheme.{u}} [Algebra R Γ(T, ⊤)]
variable (r : Fin (n + 1) → Γ(T, ⊤)) (c : Fin (m + 1) → Γ(T, ⊤))
variable (hr : r (e.symm i).1.down = 1) (hc : c (e.symm i).2.down = 1)

include hr hc in
theorem reindexedSegreSectionCoordinates_pivot_inverse :
    ReindexedSegreEvaluation.reindexedSegreSectionCoordinates e r c i = 1 := by
  change r (e.symm i).1.down * c (e.symm i).2.down = 1
  rw [hr, hc, one_mul]

theorem segreStandardChart_evaluation :
    (T.toSpecΓ ≫ Spec.map (CommRingCat.ofHom
      (TensorCoordinates.segreHomogeneousSectionEvaluation R (e.symm i) r c hr hc).toRingHom) ≫
        (ProjectiveScheme.segreHomogeneousChartMap (CommRingCat.of R) (e.symm i).1 (e.symm i).2).left) ≫
      (ProjectiveScheme.segreProjectiveInclusion (CommRingCat.of R) ≫ (Projective.SpaceReindex.affineProjectiveSpaceReindexIso R e).hom.left) =
    ProjectiveChart.Evaluation.projectiveChartMap (algebraMap R Γ(T, ⊤)) (ReindexedSegreEvaluation.reindexedSegreSectionCoordinates e r c) i
      (reindexedSegreSectionCoordinates_pivot_inverse e i r c hr hc) := by
  let G := StandardGradedMap.segreStandardGradedMap R e
  let Q := ChartCoordinates.segreQuotientGrading (σ := ULift.{u} (Fin (n + 1))) (τ := ULift.{u} (Fin (m + 1))) R
  let hG := StandardGradedMap.segreStandardGradedMap_irrelevant R e
  let hvar := StandardGradedMap.segreStandardGradedMap_variable R e i
  let a := StandardChartRingMap.homogeneousAwayEquivOfEq Q hvar
  let φ := TensorCoordinates.segreHomogeneousSectionEvaluation R (e.symm i) r c hr hc
  let ψ := φ.toRingHom.comp a.toRingHom
  have hC (z : R) : ψ (HomogeneousLocalization.Away.map G (X i)
      (algebraMap R (ProjectiveChart.Evaluation.projectiveChartRing R d i) z)) = algebraMap R Γ(T, ⊤) z := by
    change φ (StandardChartRingMap.segreStandardChartRingMap R e i (algebraMap R (ProjectiveChart.Evaluation.projectiveChartRing R d i) z)) = _
    rw [StandardChartRingMap.segreStandardChartRingMap_constant]
    exact φ.commutes z
  have hX (j : Fin (d + 1)) : ψ (HomogeneousLocalization.Away.map G (X i)
      (HilbertScheme.Presentations.Polynomial.Dehomogenization.PolynomialProjective.dehomogenize i (X j))) = ReindexedSegreEvaluation.reindexedSegreSectionCoordinates e r c j := by
    change φ (StandardChartRingMap.segreStandardChartRingMap R e i (HilbertScheme.Presentations.Polynomial.Dehomogenization.PolynomialProjective.dehomogenize i (X j))) = _
    rw [StandardChartRingMap.segreStandardChartRingMap_coordinate]
    exact TensorCoordinates.segreHomogeneousSectionEvaluation_coordinate R (e.symm i) r c hr hc
      (e.symm j).1.down (e.symm j).2.down
  have h := ProjectiveChart.MapRecognition.projectiveMap_chart_of_coordinates Q G hG (algebraMap R Γ(T, ⊤))
    (ReindexedSegreEvaluation.reindexedSegreSectionCoordinates e r c) i
    (reindexedSegreSectionCoordinates_pivot_inverse e i r c hr hc) ψ hC hX
  have hmap : Spec.map (CommRingCat.ofHom ψ) =
      Spec.map (CommRingCat.ofHom φ.toRingHom) ≫ Spec.map (CommRingCat.ofHom a.toRingHom) :=
    Spec.map_comp (CommRingCat.ofHom a.toRingHom) (CommRingCat.ofHom φ.toRingHom)
  have hp : T.toSpecΓ ≫ Spec.map (CommRingCat.ofHom ψ) ≫
      Proj.awayι Q (G (X i)) (G.map_mem (isHomogeneous_X R i)) Nat.zero_lt_one =
      T.toSpecΓ ≫ Spec.map (CommRingCat.ofHom φ.toRingHom) ≫
        (ProjectiveScheme.segreHomogeneousChartMap (CommRingCat.of R) (e.symm i).1 (e.symm i).2).left := by
    rw [hmap, Category.assoc,
      homogeneousAwayEquivOfEq_awayι Q hvar (G.map_mem (isHomogeneous_X R i))
        (ChartCoordinates.segreVariable R (e.symm i)).property Nat.zero_lt_one]
    rfl
  rw [← StandardGradedMap.segreStandardGradedMap_proj R e]
  exact (congrArg (fun k => k ≫ Proj.map G hG) hp).symm.trans h

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Segre.StandardChartEvaluation
