import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Affine.FieldCoefficientIdentity
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Isogeny.KernelScheme

/-! # Field Coordinate Rank -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction

noncomputable section

/-! The actual coordinate algebra of a finite field scheme has dimension its
scheme-theoretic degree. This gives the specified polarization-kernel dimension. -/
open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj BigOperators
universe u

theorem Finite.FieldCoordinateRank.finiteField_coordinate_finite {K : Type u} [Field K]
    {X : Scheme.{u}} (p : X ⟶ Spec (.of K)) [IsFinite p] :
    let : Algebra K Γ(X, ⊤) := (Coefficient.ModulePresheaf.schemeCoefficientMap p).toAlgebra;
    Module.Finite K Γ(X, ⊤) := by
  let : Algebra K Γ(X, ⊤) := (Coefficient.ModulePresheaf.schemeCoefficientMap p).toAlgebra
  let M : Over (Spec (.of K)) := Over.mk p
  let : Algebra K Γ(M.left, ⊤) := (Coefficient.ModulePresheaf.schemeCoefficientMap M.hom).toAlgebra
  let : IsFinite M.hom := inferInstanceAs (IsFinite p)
  let : IsAffine M.left := isAffine_of_isAffineHom p
  have : Module.Finite K (Affine.OverChartPoints.affineOverAlgebra K M) := Affine.FieldPointCoordinates.finiteAffineField_coordinateAlgebra_finite K M
  let e : Affine.OverChartPoints.affineOverAlgebra K M ≃ₐ[K] Γ(M.left, ⊤) := Affine.FieldCoefficientIdentity.affineOverAlgebraCoefficientEquiv M
  exact Module.Finite.equiv e.toLinearEquiv

theorem Finite.FieldCoordinateRank.finiteField_coordinate_finrank {K : Type u} [Field K]
    {X : Scheme.{u}} (p : X ⟶ Spec (.of K)) [IsFinite p] (x : Spec (.of K)) :
    let : Algebra K Γ(X, ⊤) := (Coefficient.ModulePresheaf.schemeCoefficientMap p).toAlgebra;
    Module.finrank K Γ(X, ⊤) = p.finrank x := by
  let M : Over (Spec (.of K)) := Over.mk p
  let : Algebra K Γ(M.left, ⊤) := (Coefficient.ModulePresheaf.schemeCoefficientMap M.hom).toAlgebra
  let : IsFinite M.hom := inferInstanceAs (IsFinite p)
  let : IsAffine M.left := isAffine_of_isAffineHom p
  let e : Affine.OverChartPoints.affineOverAlgebra K M ≃ₐ[K] Γ(M.left, ⊤) := Affine.FieldCoefficientIdentity.affineOverAlgebraCoefficientEquiv M
  exact e.toLinearEquiv.finrank_eq.symm.trans (Affine.FieldPointCoordinates.finiteAffineField_finrank K M x).symm

theorem Abelian.Schemes.AbelianScheme.Isogeny.HasPolarizationType.kernel_coordinate_finrank
    {K : Type u} [Field K] {g : ℕ} {A B : Abelian.Schemes.AbelianScheme g (Spec (.of K))}
    {p : Abelian.Schemes.AbelianScheme.Isogeny A B} {δ : Fin g → ℕ} (hp : p.HasPolarizationType δ) :
    let : Algebra K Γ(p.kernelScheme.left, ⊤) := (Coefficient.ModulePresheaf.schemeCoefficientMap p.kernelScheme.hom).toAlgebra;
    Module.finrank K Γ(p.kernelScheme.left, ⊤) = (∏ i, δ i) ^ 2 :=
  (HilbertConstruction.Finite.FieldCoordinateRank.finiteField_coordinate_finrank p.kernelScheme.hom (IsLocalRing.closedPoint K)).trans
    ((p.kernelScheme_finrank (IsLocalRing.closedPoint K)).trans
      (hp.degree (η[B.scheme].left (IsLocalRing.closedPoint K))))

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction
