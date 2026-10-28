import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Projective.ProjectivePresentations
import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Basic
import Mathlib.RingTheory.Localization.Away.Basic

/-! # Evaluation -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.ProjectiveChart.Evaluation

noncomputable section

/-! Construct actual morphisms to standard projective charts from normalized regular coordinates. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

variable {R B : Type u} [CommRing R] [CommRing B] {n : ℕ}

/-- The coordinate ring of the ith standard chart of projective n-space. -/
abbrev projectiveChartRing (R : Type u) [CommRing R] (n : ℕ) (i : Fin (n + 1)) :=
  HomogeneousLocalization.Away (Projective.ProjectivePresentations.coordinateGrading R n) (MvPolynomial.X i)

/-- Evaluate a projective-chart function at coordinates with the ith coordinate equal to one. -/
def projectiveChartEvaluation (c : R →+* B) (v : Fin (n + 1) → B)
    (i : Fin (n + 1)) (hi : v i = 1) : projectiveChartRing R n i →+* B := by
  let ev := MvPolynomial.eval₂Hom c v
  have hu : IsUnit (ev (MvPolynomial.X i)) := by
    change IsUnit (MvPolynomial.eval₂Hom c v (MvPolynomial.X i))
    rw [MvPolynomial.eval₂Hom_X', hi]
    exact isUnit_one
  exact (IsLocalization.Away.lift
    (S := Localization.Away (MvPolynomial.X i : Projective.ProjectivePresentations.coordinateRing R n)) (g := ev)
    (MvPolynomial.X i) hu).comp
      (algebraMap (projectiveChartRing R n i)
        (Localization.Away (MvPolynomial.X i : Projective.ProjectivePresentations.coordinateRing R n)))

/-- Evaluation on a chart restricts to the given coefficient-ring map. -/
theorem projectiveChartEvaluation_constant (c : R →+* B) (v : Fin (n + 1) → B)
    (i : Fin (n + 1)) (hi : v i = 1) (r : R) :
    projectiveChartEvaluation c v i hi
      (HomogeneousLocalization.fromZeroRingHom (Projective.ProjectivePresentations.coordinateGrading R n) _
        (Projective.ProjectivePresentations.degreeZeroConstants R n r)) = c r := by
  have hv : (HomogeneousLocalization.fromZeroRingHom (Projective.ProjectivePresentations.coordinateGrading R n)
      (Submonoid.powers (MvPolynomial.X i)) (Projective.ProjectivePresentations.degreeZeroConstants R n r)).val =
      algebraMap (Projective.ProjectivePresentations.coordinateRing R n) (Localization.Away (MvPolynomial.X i : Projective.ProjectivePresentations.coordinateRing R n))
        (MvPolynomial.C r) := by
    change Localization.mk (MvPolynomial.C r) 1 = _
    rw [Localization.mk_eq_mk', IsLocalization.mk'_one]
  dsimp [projectiveChartEvaluation]
  rw [hv, IsLocalization.Away.lift_eq]
  exact MvPolynomial.eval₂_C _ _ _

/-- A homogeneous fraction is evaluated by its numerator when the chart denominator is one. -/
theorem projectiveChartEvaluation_mk (c : R →+* B) (v : Fin (n + 1) → B)
    (i : Fin (n + 1)) (hi : v i = 1) (d : ℕ) (p : Projective.ProjectivePresentations.coordinateRing R n)
    (hp : p ∈ Projective.ProjectivePresentations.coordinateGrading R n d) :
    projectiveChartEvaluation c v i hi
      (HomogeneousLocalization.Away.mk (Projective.ProjectivePresentations.coordinateGrading R n) (MvPolynomial.isHomogeneous_X R i)
        d p (by simpa only [smul_eq_mul, mul_one] using hp)) = MvPolynomial.eval₂Hom c v p := by
  let ev := MvPolynomial.eval₂Hom c v
  have hv : ev (MvPolynomial.X i) * (1 : B) = 1 := by
    rw [mul_one]
    exact (MvPolynomial.eval₂Hom_X' c v i).trans hi
  change (Localization.awayLift ev (MvPolynomial.X i) (isUnit_iff_exists_inv.mpr ⟨1, hv⟩))
      (Localization.mk p ⟨(MvPolynomial.X i : Projective.ProjectivePresentations.coordinateRing R n) ^ d, d, rfl⟩) = ev p
  exact (Localization.awayLift_mk ev (MvPolynomial.X i) p 1 hv d).trans (by rw [one_pow, mul_one])

/-- The jth affine coordinate of the ith chart evaluates to the supplied normalized coordinate. -/
theorem projectiveChartEvaluation_coordinate (c : R →+* B) (v : Fin (n + 1) → B)
    (i : Fin (n + 1)) (hi : v i = 1) (j : Fin (n + 1)) :
    projectiveChartEvaluation c v i hi
      (HomogeneousLocalization.Away.mk (Projective.ProjectivePresentations.coordinateGrading R n) (MvPolynomial.isHomogeneous_X R i)
        1 (MvPolynomial.X j) (by
          change (MvPolynomial.X j : Projective.ProjectivePresentations.coordinateRing R n).IsHomogeneous 1
          exact MvPolynomial.isHomogeneous_X R j)) = v j :=
  (projectiveChartEvaluation_mk c v i hi 1 (MvPolynomial.X j) (MvPolynomial.isHomogeneous_X R j)).trans
    (MvPolynomial.eval₂Hom_X' c v j)

variable {T : Scheme.{u}}

/-- Regular normalized coordinates define a morphism from any scheme into a projective chart. -/
def projectiveChartMap (c : R →+* Γ(T, ⊤)) (v : Fin (n + 1) → Γ(T, ⊤))
    (i : Fin (n + 1)) (hi : v i = 1) : T ⟶ (Projective.ProjectivePresentations.affineProjectiveSpace R n).left :=
  T.toSpecΓ ≫ Spec.map (CommRingCat.ofHom (projectiveChartEvaluation c v i hi)) ≫
    Proj.awayι (Projective.ProjectivePresentations.coordinateGrading R n) (MvPolynomial.X i)
      (MvPolynomial.isHomogeneous_X R i) Nat.zero_lt_one

/-- The resulting projective-chart morphism lies over the prescribed coefficient-ring map. -/
theorem projectiveChartMap_over (c : R →+* Γ(T, ⊤)) (v : Fin (n + 1) → Γ(T, ⊤))
    (i : Fin (n + 1)) (hi : v i = 1) :
    projectiveChartMap c v i hi ≫ (Projective.ProjectivePresentations.affineProjectiveSpace R n).hom =
      T.toSpecΓ ≫ Spec.map (CommRingCat.ofHom c) := by
  have hc : CommRingCat.ofHom (Projective.ProjectivePresentations.degreeZeroConstants R n).toRingHom ≫
      CommRingCat.ofHom (HomogeneousLocalization.fromZeroRingHom (Projective.ProjectivePresentations.coordinateGrading R n)
        (Submonoid.powers (MvPolynomial.X i))) ≫
      CommRingCat.ofHom (projectiveChartEvaluation c v i hi) = CommRingCat.ofHom c := by
    ext r
    exact projectiveChartEvaluation_constant c v i hi r
  change (T.toSpecΓ ≫ Spec.map (CommRingCat.ofHom (projectiveChartEvaluation c v i hi)) ≫
      Proj.awayι (Projective.ProjectivePresentations.coordinateGrading R n) (MvPolynomial.X i)
        (MvPolynomial.isHomogeneous_X R i) Nat.zero_lt_one) ≫
      (Proj.toSpecZero (Projective.ProjectivePresentations.coordinateGrading R n) ≫
        Spec.map (CommRingCat.ofHom (Projective.ProjectivePresentations.degreeZeroConstants R n).toRingHom)) = _
  have ha := Proj.awayι_toSpecZero (Projective.ProjectivePresentations.coordinateGrading R n) (MvPolynomial.X i)
    (MvPolynomial.isHomogeneous_X R i) Nat.zero_lt_one
  calc
    _ = T.toSpecΓ ≫ Spec.map (CommRingCat.ofHom (projectiveChartEvaluation c v i hi)) ≫
        (Proj.awayι (Projective.ProjectivePresentations.coordinateGrading R n) (MvPolynomial.X i)
          (MvPolynomial.isHomogeneous_X R i) Nat.zero_lt_one ≫
          Proj.toSpecZero (Projective.ProjectivePresentations.coordinateGrading R n)) ≫
        Spec.map (CommRingCat.ofHom (Projective.ProjectivePresentations.degreeZeroConstants R n).toRingHom) := by
      simp only [Category.assoc]
    _ = T.toSpecΓ ≫ Spec.map (CommRingCat.ofHom (projectiveChartEvaluation c v i hi)) ≫
        Spec.map (CommRingCat.ofHom (HomogeneousLocalization.fromZeroRingHom
          (Projective.ProjectivePresentations.coordinateGrading R n) (Submonoid.powers (MvPolynomial.X i)))) ≫
        Spec.map (CommRingCat.ofHom (Projective.ProjectivePresentations.degreeZeroConstants R n).toRingHom) :=
      congrArg (fun z => T.toSpecΓ ≫ Spec.map (CommRingCat.ofHom (projectiveChartEvaluation c v i hi)) ≫
        z ≫ Spec.map (CommRingCat.ofHom (Projective.ProjectivePresentations.degreeZeroConstants R n).toRingHom)) ha
    _ = T.toSpecΓ ≫ Spec.map (CommRingCat.ofHom c) := by
      rw [← Spec.map_comp, ← Spec.map_comp, Category.assoc, hc]

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.ProjectiveChart.Evaluation
