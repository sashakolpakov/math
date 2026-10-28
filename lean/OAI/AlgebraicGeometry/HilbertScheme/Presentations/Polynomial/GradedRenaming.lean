import OAI.AlgebraicGeometry.HilbertScheme.Presentations.Polynomial.Projective

/-! # Graded Renaming -/

namespace OAI.AlgebraicGeometry.HilbertScheme.Presentations.Polynomial.GradedRenaming.PolynomialProjective

noncomputable section

/-! Renaming polynomial variables preserves the grading and transports
the irrelevant ideal along a bijection of coordinate index sets. -/

open _root_.MvPolynomial

universe u v w
variable {R : Type u} [CommRing R] {σ : Type v} {τ : Type w}

def gradedRename (f : σ → τ) : Dehomogenization.PolynomialProjective.polynomialGrading σ R →+*ᵍ Dehomogenization.PolynomialProjective.polynomialGrading τ R where
  __ := (MvPolynomial.rename f).toRingHom
  map_mem hf := hf.rename_isHomogeneous

theorem gradedRename_inverse (e : σ ≃ τ) :
    (gradedRename (R := R) e).comp (gradedRename e.symm) = GradedRingHom.id (Dehomogenization.PolynomialProjective.polynomialGrading τ R) := by
  ext1 p
  change MvPolynomial.rename e (MvPolynomial.rename e.symm p) = p
  rw [MvPolynomial.rename_rename]
  simp only [Equiv.self_comp_symm, MvPolynomial.rename_id]
  rfl

theorem irrelevant_gradedRename_le_map (e : σ ≃ τ) :
    HomogeneousIdeal.irrelevant (Dehomogenization.PolynomialProjective.polynomialGrading τ R) ≤
      (HomogeneousIdeal.irrelevant (Dehomogenization.PolynomialProjective.polynomialGrading σ R)).map (gradedRename e) := by
  apply (HomogeneousIdeal.toIdeal_irrelevant_le (Dehomogenization.PolynomialProjective.polynomialGrading τ R)).mpr
  intro d hd p hp
  have he : gradedRename (R := R) e (gradedRename e.symm p) = p :=
    DFunLike.congr_fun (gradedRename_inverse (R := R) e) p
  rw [← he]
  exact Ideal.mem_map_of_mem _ (HomogeneousIdeal.mem_irrelevant_of_mem
    (Dehomogenization.PolynomialProjective.polynomialGrading σ R) hd ((gradedRename e.symm).map_mem hp))

end

end OAI.AlgebraicGeometry.HilbertScheme.Presentations.Polynomial.GradedRenaming.PolynomialProjective
