import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Chart.OverlapRings

/-! # Overlap Maps -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Chart.OverlapMaps

noncomputable section

/-! Agreement of actual projective-chart maps under a unit rescaling of homogeneous coordinates. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

variable {R : Type u} [CommRing R] {T : Scheme.{u}} {n : ℕ}

/-- A homogeneous denominator with invertible value defines a morphism through its standard open. -/
def projectiveFractionMap (c : R →+* Γ(T, ⊤)) (v : Fin (n + 1) → Γ(T, ⊤))
    (f : Projective.ProjectivePresentations.coordinateRing R n) (hf : IsUnit (MvPolynomial.eval₂Hom c v f))
    (d : ℕ) (hfd : f ∈ Projective.ProjectivePresentations.coordinateGrading R n d) (hd : 0 < d) :
    T ⟶ (Projective.ProjectivePresentations.affineProjectiveSpace R n).left :=
  T.toSpecΓ ≫ Spec.map (CommRingCat.ofHom (Homogeneous.Fractions.homogeneousFractionEvaluation c v f hf)) ≫
    Proj.awayι (Projective.ProjectivePresentations.coordinateGrading R n) f hfd hd

/-- Passing to the overlap by multiplying the denominator preserves the morphism to projective space. -/
theorem projectiveFractionMap_awayMap (c : R →+* Γ(T, ⊤)) (v : Fin (n + 1) → Γ(T, ⊤))
    (f g x : Projective.ProjectivePresentations.coordinateRing R n) (d e : ℕ)
    (hfd : f ∈ Projective.ProjectivePresentations.coordinateGrading R n d) (hge : g ∈ Projective.ProjectivePresentations.coordinateGrading R n e)
    (hd : 0 < d) (hx : x = f * g)
    (hf : IsUnit (MvPolynomial.eval₂Hom c v f)) (hxu : IsUnit (MvPolynomial.eval₂Hom c v x)) :
    projectiveFractionMap c v f hf d hfd hd =
      projectiveFractionMap c v x hxu (d + e) (hx ▸ SetLike.mul_mem_graded hfd hge)
        (hd.trans_le (d.le_add_right e)) := by
  let b := HomogeneousLocalization.awayMap (Projective.ProjectivePresentations.coordinateGrading R n) hge hx
  have hb : (Homogeneous.Fractions.homogeneousFractionEvaluation c v x hxu).comp b = Homogeneous.Fractions.homogeneousFractionEvaluation c v f hf :=
    OverlapRings.homogeneousFractionEvaluation_awayMap c v f g x e hge hx hf hxu
  have ha := Proj.SpecMap_awayMap_awayι (𝒜 := Projective.ProjectivePresentations.coordinateGrading R n) hfd hd hge hx
  change T.toSpecΓ ≫ Spec.map (CommRingCat.ofHom (Homogeneous.Fractions.homogeneousFractionEvaluation c v f hf)) ≫
    Proj.awayι (Projective.ProjectivePresentations.coordinateGrading R n) f hfd hd = _
  calc
    _ = T.toSpecΓ ≫ Spec.map (CommRingCat.ofHom ((Homogeneous.Fractions.homogeneousFractionEvaluation c v x hxu).comp b)) ≫
        Proj.awayι (Projective.ProjectivePresentations.coordinateGrading R n) f hfd hd :=
      congrArg (fun a => T.toSpecΓ ≫ Spec.map (CommRingCat.ofHom a) ≫
        Proj.awayι (Projective.ProjectivePresentations.coordinateGrading R n) f hfd hd) hb.symm
    _ = T.toSpecΓ ≫ Spec.map (CommRingCat.ofHom (Homogeneous.Fractions.homogeneousFractionEvaluation c v x hxu)) ≫
        (Spec.map (CommRingCat.ofHom b) ≫ Proj.awayι (Projective.ProjectivePresentations.coordinateGrading R n) f hfd hd) := by
      rw [CommRingCat.ofHom_comp, Spec.map_comp, Category.assoc]
    _ = _ := congrArg (fun a =>
      T.toSpecΓ ≫ Spec.map (CommRingCat.ofHom (Homogeneous.Fractions.homogeneousFractionEvaluation c v x hxu)) ≫ a) ha

/-- Normalized chart maps are the corresponding homogeneous-fraction maps. -/
theorem projectiveChartMap_eq_fraction (c : R →+* Γ(T, ⊤)) (v : Fin (n + 1) → Γ(T, ⊤))
    (i : Fin (n + 1)) (hi : v i = 1)
    (hf : IsUnit (MvPolynomial.eval₂Hom c v (MvPolynomial.X i))) :
    ProjectiveChart.Evaluation.projectiveChartMap c v i hi = projectiveFractionMap c v (MvPolynomial.X i) hf 1
      (MvPolynomial.isHomogeneous_X R i) Nat.zero_lt_one :=
  congrArg (fun a => T.toSpecΓ ≫ Spec.map (CommRingCat.ofHom a) ≫
      Proj.awayι (Projective.ProjectivePresentations.coordinateGrading R n) (MvPolynomial.X i) (MvPolynomial.isHomogeneous_X R i) Nat.zero_lt_one)
    (Homogeneous.Fractions.projectiveChartEvaluation_eq_fraction c v i hi hf)

/-- A unit change of the normalized coordinate leaves the actual morphism to projective space unchanged. -/
theorem projectiveChartMap_normalize (c : R →+* Γ(T, ⊤)) (v : Fin (n + 1) → Γ(T, ⊤))
    (i j : Fin (n + 1)) (hi : v i = 1) (a : Γ(T, ⊤)ˣ) (hj : v j = a) :
    ProjectiveChart.Evaluation.projectiveChartMap c v i hi =
      ProjectiveChart.Evaluation.projectiveChartMap c (fun k => (↑a⁻¹ : Γ(T, ⊤)) * v k) j (OverlapRings.normalizedCoordinate_eq_one v j a hj) := by
  let xi : Projective.ProjectivePresentations.coordinateRing R n := MvPolynomial.X i
  let xj : Projective.ProjectivePresentations.coordinateRing R n := MvPolynomial.X j
  have hui : IsUnit (MvPolynomial.eval₂Hom c v xi) :=
    ((MvPolynomial.eval₂Hom_X' c v i).trans hi).symm ▸ isUnit_one
  have huj : IsUnit (MvPolynomial.eval₂Hom c v xj) :=
    ((MvPolynomial.eval₂Hom_X' c v j).trans hj).symm ▸ a.isUnit
  have hprod : IsUnit (MvPolynomial.eval₂Hom c v (xi * xj)) :=
    (map_mul (MvPolynomial.eval₂Hom c v) xi xj).symm ▸ hui.mul huj
  have hiMap := projectiveFractionMap_awayMap c v xi xj (xi * xj) 1 1
    (MvPolynomial.isHomogeneous_X R i) (MvPolynomial.isHomogeneous_X R j)
    Nat.zero_lt_one rfl hui hprod
  have hjMap := projectiveFractionMap_awayMap c v xj xi (xi * xj) 1 1
    (MvPolynomial.isHomogeneous_X R j) (MvPolynomial.isHomogeneous_X R i)
    Nat.zero_lt_one (mul_comm xi xj) huj hprod
  have hn : projectiveFractionMap c v xj huj 1 (MvPolynomial.isHomogeneous_X R j) Nat.zero_lt_one =
      ProjectiveChart.Evaluation.projectiveChartMap c (fun k => (↑a⁻¹ : Γ(T, ⊤)) * v k) j (OverlapRings.normalizedCoordinate_eq_one v j a hj) :=
    congrArg (fun b => T.toSpecΓ ≫ Spec.map (CommRingCat.ofHom b) ≫
      Proj.awayι (Projective.ProjectivePresentations.coordinateGrading R n) xj (MvPolynomial.isHomogeneous_X R j) Nat.zero_lt_one)
      (OverlapRings.homogeneousFractionEvaluation_normalized c v j a hj huj)
  exact (projectiveChartMap_eq_fraction c v i hi hui).trans (hiMap.trans (hjMap.symm.trans hn))

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Chart.OverlapMaps
