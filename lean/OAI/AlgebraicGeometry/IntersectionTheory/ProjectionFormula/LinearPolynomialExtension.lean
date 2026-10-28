import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Projection.CoordinateNormalForm
import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.RenamePolynomialExtension

/-! # Linear Polynomial Extension -/

namespace OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.LinearPolynomialExtension

noncomputable section

/-! The homogeneous coordinate map of an independent linear
projection is a polynomial extension after an actual algebra isomorphism. -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

theorem exists_equivalence {m n : ℕ} (L : Fin (m + 1) → Foundations.Scheme.ProjectiveSpace.projectiveGrading n 1)
    (hL : LinearIndependent ℂ L) :
    ∃ (ι : Type) (_ : Finite ι)
      (e : Foundations.Scheme.ProjectiveSpace.homogeneousCoordinateRing n ≃ₐ[ℂ] MvPolynomial ι (Foundations.Scheme.ProjectiveSpace.homogeneousCoordinateRing m)),
      ∀ p : Foundations.Scheme.ProjectiveSpace.homogeneousCoordinateRing m,
        e (HomogeneousCoordinateMap.ofForms (fun i => (L i).val) (fun i => (L i).property) p) = MvPolynomial.C p := by
  obtain ⟨h, g, _, hg⟩ := Projection.CoordinateNormalForm.exists_equiv L hL
  let j := Fin.castLE (Nat.add_le_add_right h 1)
  let e := (LinearFormAutomorphism.algebraEquiv g).symm.trans
    (RenamePolynomialExtension.equivalence j (Fin.castLE_injective _) ℂ)
  refine ⟨RenamePolynomialExtension.complement j,
    inferInstanceAs (Finite {a : Fin (n + 1) // a ∉ Set.range j}), e, ?_⟩
  intro p
  have he := DFunLike.congr_fun hg p
  have he' : HomogeneousCoordinateMap.ofForms (fun i => (L i).val) (fun i => (L i).property) p =
      LinearFormAutomorphism.algebraEquiv g (MvPolynomial.rename j p) := he
  change RenamePolynomialExtension.equivalence j (Fin.castLE_injective _) ℂ
    ((LinearFormAutomorphism.algebraEquiv g).symm
      (HomogeneousCoordinateMap.ofForms (fun i => (L i).val) (fun i => (L i).property) p)) = _
  rw [he', AlgEquiv.symm_apply_apply]
  exact RenamePolynomialExtension.equivalence_rename j (Fin.castLE_injective _) ℂ p

end

end OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.LinearPolynomialExtension
