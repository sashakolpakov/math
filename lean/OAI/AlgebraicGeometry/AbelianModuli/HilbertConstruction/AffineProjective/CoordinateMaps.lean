import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.ProjectiveCoordinate.Rescaling
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.ProjectiveChart.Naturality
import OAI.AlgebraicGeometry.HilbertScheme.Presentations.Relative.AffinePoints

/-! # Coordinate Maps -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.AffineProjective.CoordinateMaps

noncomputable section

/-! Projective-coordinate maps directly from affine algebra spectra. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open OAI.AlgebraicGeometry.HilbertScheme.Presentations.Relative.AffinePoints

universe u

variable (R : CommRingCat.{u}) (A : Type u) [CommRing A] [Algebra R A] {n : ℕ}

def affineProjectiveCoordinateMap (v : Fin (n + 1) → A) (i : Fin (n + 1)) (hi : v i = 1) :
    Spec (CommRingCat.of A) ⟶ (Projective.ProjectivePresentations.affineProjectiveSpace R n).left :=
  Spec.map (CommRingCat.ofHom (ProjectiveChart.Evaluation.projectiveChartEvaluation (algebraMap R A) v i hi)) ≫
    Proj.awayι (Projective.ProjectivePresentations.coordinateGrading R n) (MvPolynomial.X i)
      (MvPolynomial.isHomogeneous_X R i) Nat.zero_lt_one

theorem affineProjectiveCoordinateMap_global (v : Fin (n + 1) → A)
    (i : Fin (n + 1)) (hi : v i = 1) :
    affineProjectiveCoordinateMap R A v i hi =
      ProjectiveChart.Evaluation.projectiveChartMap ((Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom.comp (algebraMap R A))
        (fun k => (Scheme.ΓSpecIso (CommRingCat.of A)).inv (v k)) i
        ((congrArg (Scheme.ΓSpecIso (CommRingCat.of A)).inv hi).trans (map_one _)) := by
  let j : Spec (CommRingCat.of (ProjectiveChart.Evaluation.projectiveChartRing R n i)) ⟶
      (Projective.ProjectivePresentations.affineProjectiveSpace R n).left := Proj.awayι (Projective.ProjectivePresentations.coordinateGrading R n) (MvPolynomial.X i)
        (MvPolynomial.isHomogeneous_X R i) Nat.zero_lt_one
  let T : Scheme.{u} := Spec (CommRingCat.of A)
  let e : A →+* Γ(T, ⊤) := (Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom
  let ev : ProjectiveChart.Evaluation.projectiveChartRing R n i →+* Γ(T, ⊤) :=
    ProjectiveChart.Evaluation.projectiveChartEvaluation (e.comp (algebraMap R A)) (fun k => e (v k)) i
      ((congrArg e hi).trans e.map_one)
  have he : e.comp (ProjectiveChart.Evaluation.projectiveChartEvaluation (algebraMap R A) v i hi) = ev :=
    ProjectiveChart.Naturality.projectiveChartEvaluation_comp e (algebraMap R A) v i hi
  change Spec.map (CommRingCat.ofHom (ProjectiveChart.Evaluation.projectiveChartEvaluation (algebraMap R A) v i hi)) ≫ j =
    T.toSpecΓ ≫ Spec.map (CommRingCat.ofHom (S := Γ(T, ⊤)) ev) ≫ j
  rw [← he, CommRingCat.ofHom_comp, Spec.map_comp, ← Category.assoc,
    ← Category.assoc]
  have h : T.toSpecΓ ≫ Spec.map (CommRingCat.ofHom (S := Γ(T, ⊤)) e) = 𝟙 T :=
    toSpecΓ_SpecMap_ΓSpecIso_inv (CommRingCat.of A)
  rw [h, Category.id_comp]

theorem affineProjectiveCoordinateMap_natural
    {B : Type u} [CommRing B] [Algebra R B] (φ : A →ₐ[R] B)
    (v : Fin (n + 1) → A) (i : Fin (n + 1)) (hi : v i = 1) :
    Spec.map (CommRingCat.ofHom φ.toRingHom) ≫ affineProjectiveCoordinateMap R A v i hi =
      affineProjectiveCoordinateMap R B (fun k => φ (v k)) i
        ((congrArg φ hi).trans φ.map_one) := by
  let j : Spec (CommRingCat.of (ProjectiveChart.Evaluation.projectiveChartRing R n i)) ⟶
      (Projective.ProjectivePresentations.affineProjectiveSpace R n).left := Proj.awayι (Projective.ProjectivePresentations.coordinateGrading R n) (MvPolynomial.X i)
        (MvPolynomial.isHomogeneous_X R i) Nat.zero_lt_one
  change Spec.map (CommRingCat.ofHom φ.toRingHom) ≫
    Spec.map (CommRingCat.ofHom (ProjectiveChart.Evaluation.projectiveChartEvaluation (algebraMap R A) v i hi)) ≫ j =
      Spec.map (CommRingCat.ofHom
        (ProjectiveChart.Evaluation.projectiveChartEvaluation (algebraMap R B) (fun k => φ (v k)) i _)) ≫ j
  rw [← Spec.map_comp_assoc]
  have he := ProjectiveChart.Naturality.projectiveChartEvaluation_comp φ.toRingHom (algebraMap R A) v i hi
  have hc : φ.toRingHom.comp (algebraMap R A) = algebraMap R B := RingHom.ext φ.commutes
  rw [hc] at he
  exact congrArg (fun h => Spec.map (CommRingCat.ofHom h) ≫ j) he

theorem affineProjectiveCoordinateMap_eq_of_cross
    (v w : Fin (n + 1) → A) (i j : Fin (n + 1)) (hi : v i = 1) (hj : w j = 1)
    (hu : IsUnit (v j)) (hcross : ∀ k, v j * w k = v k) :
    affineProjectiveCoordinateMap R A v i hi = affineProjectiveCoordinateMap R A w j hj := by
  rw [affineProjectiveCoordinateMap_global, affineProjectiveCoordinateMap_global]
  apply ProjectiveCoordinate.Rescaling.projectiveChartMap_eq_of_cross
  · exact hu.map (Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom
  · intro k
    rw [← map_mul, hcross k]

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.AffineProjective.CoordinateMaps
