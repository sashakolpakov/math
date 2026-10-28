import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.ProjectiveChart.Evaluation

/-! # Naturality -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.ProjectiveChart.Naturality

noncomputable section

/-! Projective-chart evaluation and chart maps are natural under maps of coefficient rings and schemes. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

variable {R B C : Type u} [CommRing R] [CommRing B] [CommRing C] {n : ℕ}

/-- Evaluation on the polynomial ring commutes with the target-ring map. -/
theorem polynomialEvaluation_comp (b : B →+* C) (c : R →+* B) (v : Fin (n + 1) → B) :
    b.comp (MvPolynomial.eval₂Hom c v) = MvPolynomial.eval₂Hom (b.comp c) (fun i => b (v i)) := by
  ext r <;> simp

/-- Evaluation of projective-chart functions commutes with a ring map. -/
theorem projectiveChartEvaluation_comp (b : B →+* C) (c : R →+* B)
    (v : Fin (n + 1) → B) (i : Fin (n + 1)) (hi : v i = 1) :
    b.comp (Evaluation.projectiveChartEvaluation c v i hi) =
      Evaluation.projectiveChartEvaluation (b.comp c) (fun j => b (v j)) i
        ((congrArg b hi).trans b.map_one) := by
  apply RingHom.ext
  intro z
  obtain ⟨d, p, hp, rfl⟩ := HomogeneousLocalization.Away.mk_surjective
    (Projective.ProjectivePresentations.coordinateGrading R n) (MvPolynomial.isHomogeneous_X R i) z
  have hp' : p ∈ Projective.ProjectivePresentations.coordinateGrading R n d := by
    simpa only [smul_eq_mul, mul_one] using hp
  exact (congrArg b (Evaluation.projectiveChartEvaluation_mk c v i hi d p hp')).trans
    ((RingHom.congr_fun (polynomialEvaluation_comp b c v) p).trans
      (Evaluation.projectiveChartEvaluation_mk (b.comp c) (fun j => b (v j)) i
        ((congrArg b hi).trans b.map_one) d p hp').symm)

variable {X Y : Scheme.{u}}

/-- A normalized projective-coordinate map pulls back along any scheme morphism. -/
theorem projectiveChartMap_comp (f : X ⟶ Y) (c : R →+* Γ(Y, ⊤))
    (v : Fin (n + 1) → Γ(Y, ⊤)) (i : Fin (n + 1)) (hi : v i = 1) :
    f ≫ Evaluation.projectiveChartMap c v i hi =
      Evaluation.projectiveChartMap (f.appTop.hom.comp c) (fun j => f.appTop (v j)) i
        ((congrArg (fun a => f.appTop a) hi).trans f.appTop.hom.map_one) := by
  have he : CommRingCat.ofHom (Evaluation.projectiveChartEvaluation c v i hi) ≫ f.appTop =
      CommRingCat.ofHom (Evaluation.projectiveChartEvaluation (f.appTop.hom.comp c)
        (fun j => f.appTop (v j)) i
          ((congrArg (fun a => f.appTop a) hi).trans f.appTop.hom.map_one)) :=
    congrArg CommRingCat.ofHom (projectiveChartEvaluation_comp f.appTop.hom c v i hi)
  change f ≫ (Y.toSpecΓ ≫ Spec.map (CommRingCat.ofHom (Evaluation.projectiveChartEvaluation c v i hi)) ≫
      Proj.awayι (Projective.ProjectivePresentations.coordinateGrading R n) (MvPolynomial.X i)
        (MvPolynomial.isHomogeneous_X R i) Nat.zero_lt_one) = _
  calc
    _ = (f ≫ Y.toSpecΓ) ≫ Spec.map (CommRingCat.ofHom (Evaluation.projectiveChartEvaluation c v i hi)) ≫
        Proj.awayι (Projective.ProjectivePresentations.coordinateGrading R n) (MvPolynomial.X i)
          (MvPolynomial.isHomogeneous_X R i) Nat.zero_lt_one := by simp only [Category.assoc]
    _ = (X.toSpecΓ ≫ Spec.map f.appTop) ≫
        Spec.map (CommRingCat.ofHom (Evaluation.projectiveChartEvaluation c v i hi)) ≫
        Proj.awayι (Projective.ProjectivePresentations.coordinateGrading R n) (MvPolynomial.X i)
          (MvPolynomial.isHomogeneous_X R i) Nat.zero_lt_one :=
      congrArg (fun a => a ≫ Spec.map (CommRingCat.ofHom (Evaluation.projectiveChartEvaluation c v i hi)) ≫
        Proj.awayι (Projective.ProjectivePresentations.coordinateGrading R n) (MvPolynomial.X i)
          (MvPolynomial.isHomogeneous_X R i) Nat.zero_lt_one) (Scheme.toSpecΓ_naturality f)
    _ = _ := by
      simp only [Category.assoc, ← Spec.map_comp_assoc, he, Evaluation.projectiveChartMap]
      rfl

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.ProjectiveChart.Naturality
