import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.LinearFormAutomorphism

/-! # Coordinate Normal Form -/

namespace OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Projection.CoordinateNormalForm

noncomputable section

/-! An independent projection coordinate tuple is a standard
coordinate projection after an actual invertible linear change of variables. -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.LinearFormBasis OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.LinearFormBasis.GradedMap

def standard {m n : ℕ} (h : m ≤ n) : Foundations.Scheme.ProjectiveSpace.projectiveGrading m →+*ᵍ Foundations.Scheme.ProjectiveSpace.projectiveGrading n where
  __ := (MvPolynomial.rename (Fin.castLE (Nat.add_le_add_right h 1))).toRingHom
  map_mem {d} {p} hp := (show MvPolynomial.IsHomogeneous p d from hp).rename_isHomogeneous

theorem standard_apply {m n : ℕ} (h : m ≤ n) (p : Foundations.Scheme.ProjectiveSpace.homogeneousCoordinateRing m) :
    standard h p = MvPolynomial.rename (Fin.castLE (Nat.add_le_add_right h 1)) p := rfl

theorem exists_equiv {m n : ℕ} (L : Fin (m + 1) → Foundations.Scheme.ProjectiveSpace.projectiveGrading n 1)
    (hL : LinearIndependent ℂ L) :
    ∃ (h : m ≤ n) (e : Foundations.Scheme.ProjectiveSpace.projectiveGrading n 1 ≃ₗ[ℂ] Foundations.Scheme.ProjectiveSpace.projectiveGrading n 1),
      (∀ i, e (LinearFormBasis.coordinate n (Fin.castLE (Nat.add_le_add_right h 1) i)) = L i) ∧
      HomogeneousCoordinateMap.ofForms (fun i => (L i).val) (fun i => (L i).property) =
        (LinearFormBasis.GradedMap.gradedHom e.toLinearMap).comp (standard h) := by
  have hcard := hL.fintype_card_le_finrank
  rw [Fintype.card_fin, LinearFormBasis.dimension] at hcard
  have h : m ≤ n := by omega
  let j := Fin.castLE (Nat.add_le_add_right h 1)
  obtain ⟨e, he⟩ := LinearFormBasis.extend L hL j (Fin.castLE_injective _)
  refine ⟨h, e, he, ?_⟩
  have halg : MvPolynomial.aeval (fun i => (L i).val) =
      (LinearFormBasis.GradedMap.algebraHom e.toLinearMap).comp (MvPolynomial.rename j) := by
    apply MvPolynomial.algHom_ext
    intro i
    simp only [MvPolynomial.aeval_X, AlgHom.comp_apply, MvPolynomial.rename_X, LinearFormBasis.GradedMap.algebraHom_X,
      LinearEquiv.coe_coe]
    exact (congrArg Subtype.val (he i)).symm
  apply GradedRingHom.ext
  intro p
  exact DFunLike.congr_fun halg p

end

end OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Projection.CoordinateNormalForm
