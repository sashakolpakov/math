import OAI.AlgebraicGeometry.Albanese.Construction.Smooth
import OAI.AlgebraicGeometry.CycleClass.Thom.Affine.Coordinates

/-! # Projective Cover -/

namespace OAI.AlgebraicGeometry.CycleClass.Thom.ProjectiveCover.Constructions.Products

noncomputable section

open _root_.CategoryTheory _root_.AlgebraicGeometry
open MonoidalCategory CartesianMonoidalCategory

open OAI.AlgebraicGeometry.Albanese.Construction.Smooth

/-- The polynomial coordinate chart as a scheme over the complex base. -/
abbrev polynomialChartOver (n : ℕ) (i : Fin (n + 1)) : Over Foundations.Scheme.ProjectiveSpace.complexBase :=
  Over.mk (Foundations.Scheme.ProjectiveChart.projectiveChartPolynomialToBase n i)

/-- The actual chart inclusion over the complex base. -/
def polynomialChartOverMap (n : ℕ) (i : Fin (n + 1)) :
    polynomialChartOver n i ⟶ Over.mk (Foundations.Scheme.ProjectiveSpace.projectiveSpaceToBase n) :=
  Over.homMk (Foundations.Scheme.ProjectiveChart.projectiveAffineChartMap n i) (Foundations.Scheme.ProjectiveChart.projectiveAffineChartMap_over n i)

instance polynomialChart_smooth (n : ℕ) (i : Fin (n + 1)) :
    Smooth (polynomialChartOver n i).hom := by
  change Smooth (Spec.map (CommRingCat.ofHom (MvPolynomial.C : ℂ →+* Foundations.Scheme.ProjectiveChartToPolynomial.projectiveChartPolynomial n i)))
  rw [HasRingHomProperty.Spec_iff (P := @Smooth)]
  change (MvPolynomial.C : ℂ →+* Foundations.Scheme.ProjectiveChartToPolynomial.projectiveChartPolynomial n i).Smooth
  rw [← MvPolynomial.algebraMap_eq, RingHom.smooth_algebraMap]
  exact {}

/-- Every projective point lies in the image of an actual polynomial chart. -/
theorem exists_polynomialChart_preimage (n : ℕ) (x : Foundations.Scheme.ProjectiveSpace.projectiveSpace n) :
    ∃ (i : Fin (n + 1)) (y : (polynomialChartOver n i).left),
      (polynomialChartOverMap n i).left y = x := by
  obtain ⟨i, hi⟩ := Foundations.Scheme.ProjectiveCoordinateCover.exists_mem_projectiveCoordinateOpen n x
  refine ⟨i, (Foundations.Scheme.ProjectiveChart.projectiveCoordinateIsoSpec n i).hom ⟨x, hi⟩, ?_⟩
  change ((Foundations.Scheme.ProjectiveChart.projectiveCoordinateIsoSpec n i).hom ≫ (Foundations.Scheme.ProjectiveChart.projectiveCoordinateIsoSpec n i).inv ≫
    (Foundations.Scheme.ProjectiveCoordinateCover.projectiveCoordinateOpen n i).ι) ⟨x, hi⟩ = x
  simp

/-- The finite polynomial-chart cover of projective space. -/
def polynomialProjectiveCover (n : ℕ) : (Foundations.Scheme.ProjectiveSpace.projectiveSpace n).OpenCover :=
  Scheme.Cover.mkOfCovers (Fin (n + 1)) (fun i => (polynomialChartOver n i).left)
    (fun i => (polynomialChartOverMap n i).left) (exists_polynomialChart_preimage n)
    (fun i => inferInstanceAs (IsOpenImmersion (Foundations.Scheme.ProjectiveChart.projectiveAffineChartMap n i)))

set_option backward.isDefEq.respectTransparency false in
/-- Projective space is smooth over the complex base, as checked on the
actual polynomial affine charts. -/
theorem projectiveSpace_smooth (n : ℕ) : Smooth (Foundations.Scheme.ProjectiveSpace.projectiveSpaceToBase n) := by
  have : ∀ i, IsAffine ((polynomialProjectiveCover n).X i) :=
    fun i => inferInstanceAs (IsAffine (Spec (.of (Foundations.Scheme.ProjectiveChartToPolynomial.projectiveChartPolynomial n i))))
  apply HasRingHomProperty.of_source_openCover (P := @Smooth) (polynomialProjectiveCover n)
  intro i
  have h : Smooth (Foundations.Scheme.ProjectiveChart.projectiveAffineChartMap n i ≫ Foundations.Scheme.ProjectiveSpace.projectiveSpaceToBase n) := by
    rw [Foundations.Scheme.ProjectiveChart.projectiveAffineChartMap_over]
    exact polynomialChart_smooth n i
  exact HasRingHomProperty.appTop (P := @Smooth) _ h

/-- The range of a product map is detected on both factors. -/
theorem range_tensorHom {X X' Y Y' : Over Foundations.Scheme.ProjectiveSpace.complexBase} (a : X' ⟶ X) (b : Y' ⟶ Y) :
    Set.range (a ⊗ₘ b).left =
      (fst X Y).left ⁻¹' Set.range a.left ∩ (snd X Y).left ⁻¹' Set.range b.left := by
  rw [Over.tensorHom_left, Scheme.Pullback.range_map]
  rfl

/-- Products of polynomial charts cover the product of projective spaces. -/
def projectiveProductCover (m n : ℕ) :
    (Over.mk (Foundations.Scheme.ProjectiveSpace.projectiveSpaceToBase m) ⊗ Over.mk (Foundations.Scheme.ProjectiveSpace.projectiveSpaceToBase n)).left.OpenCover := by
  refine Scheme.Cover.mkOfCovers (Fin (m + 1) × Fin (n + 1))
    (fun ij => (polynomialChartOver m ij.1 ⊗ polynomialChartOver n ij.2).left)
    (fun ij => (polynomialChartOverMap m ij.1 ⊗ₘ polynomialChartOverMap n ij.2).left) ?_ ?_
  · intro x
    obtain ⟨i, u, hu⟩ := exists_polynomialChart_preimage m
      ((fst (Over.mk (Foundations.Scheme.ProjectiveSpace.projectiveSpaceToBase m)) (Over.mk (Foundations.Scheme.ProjectiveSpace.projectiveSpaceToBase n))).left x)
    obtain ⟨j, v, hv⟩ := exists_polynomialChart_preimage n
      ((snd (Over.mk (Foundations.Scheme.ProjectiveSpace.projectiveSpaceToBase m)) (Over.mk (Foundations.Scheme.ProjectiveSpace.projectiveSpaceToBase n))).left x)
    have hx : x ∈ Set.range (polynomialChartOverMap m i ⊗ₘ polynomialChartOverMap n j).left := by
      rw [range_tensorHom]
      exact ⟨⟨u, hu⟩, ⟨v, hv⟩⟩
    exact ⟨(i, j), hx⟩
  · intro ij
    rw [Over.tensorHom_left]
    have : IsOpenImmersion (polynomialChartOverMap m ij.1).left :=
      inferInstanceAs (IsOpenImmersion (Foundations.Scheme.ProjectiveChart.projectiveAffineChartMap m ij.1))
    have : IsOpenImmersion (polynomialChartOverMap n ij.2).left :=
      inferInstanceAs (IsOpenImmersion (Foundations.Scheme.ProjectiveChart.projectiveAffineChartMap n ij.2))
    infer_instance

end

end OAI.AlgebraicGeometry.CycleClass.Thom.ProjectiveCover.Constructions.Products
