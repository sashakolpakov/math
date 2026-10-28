import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.IsomorphicFactorizationPoints

/-! # Isomorphic Factorization Naturality -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.IsomorphicFactorizationNaturality

noncomputable section

/-! The point classification preserves composition of test maps, and the original factorization-isomorphism condition is stable under arbitrary base change. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

variable {S : Scheme.{u}} (M : Over S) [IsLocallyNoetherian M.left] {X P Z A : Over M.left}
variable [IsProper X.hom] [Flat X.hom] [IsProper A.hom]
variable (j : Z ⟶ P) [IsClosedImmersion j.left] (i : X ⟶ P) (p : Z ⟶ A)

theorem isomorphicFactorizationPointEquiv_natural {T U : Over S} (f : U ⟶ T)
    (y : T ⟶ FactorizationIsomorphismParameter.factorizationIsomorphismParameter M j i p) :
    (IsomorphicFactorizationPoints.isomorphicFactorizationPointEquiv M j i p U (f ≫ y)).val =
      f ≫ (IsomorphicFactorizationPoints.isomorphicFactorizationPointEquiv M j i p T y).val := by
  simp only [IsomorphicFactorizationPoints.isomorphicFactorizationPointEquiv_val, Category.assoc]

theorem hasIsomorphicFactorization_precomp {T U : Over S} (c : T ⟶ M)
    (hc : FactorizationPointCondition.HasIsomorphicFactorization j i p c.left) (f : U ⟶ T) :
    FactorizationPointCondition.HasIsomorphicFactorization j i p (f ≫ c).left := by
  let e := IsomorphicFactorizationPoints.isomorphicFactorizationPointEquiv M j i p T
  let y := e.symm ⟨c, hc⟩
  have hy : (IsomorphicFactorizationPoints.isomorphicFactorizationPointEquiv M j i p T y).val = c :=
    congrArg Subtype.val (e.apply_symm_apply ⟨c, hc⟩)
  have he : (IsomorphicFactorizationPoints.isomorphicFactorizationPointEquiv M j i p U (f ≫ y)).val = f ≫ c := by
    rw [isomorphicFactorizationPointEquiv_natural, hy]
  have h := (IsomorphicFactorizationPoints.isomorphicFactorizationPointEquiv M j i p U (f ≫ y)).property
  rwa [he] at h

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.IsomorphicFactorizationNaturality
