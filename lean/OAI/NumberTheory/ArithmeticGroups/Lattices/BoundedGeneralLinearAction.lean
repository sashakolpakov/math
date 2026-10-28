import OAI.NumberTheory.ArithmeticGroups.Lattices.BoundedDiagonalAction
import OAI.NumberTheory.ArithmeticGroups.Lattices.Infinitesimal.Action
import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs

/-! # Bounded General Linear Action -/

namespace OAI.NumberTheory.ArithmeticGroups.Lattices.BoundedGeneralLinearAction.Construction

noncomputable section

/-! Change of coordinates transports the bounded infinitesimal action. -/

open scoped Classical
open _root_.MvPolynomial

theorem rightTranslate_unit_inverse_left
    {k : Type} [Field k] {n : ℕ} (g : Matrix.GeneralLinearGroup (Fin n) k)
    (p : Algebraic.CoordinatePolynomial n k) :
    PolynomialAction.Construction.rightTranslate ((g⁻¹).val) (PolynomialAction.Construction.rightTranslate (g.val) p) = p := by
  have h := congrArg (fun f : Algebraic.CoordinatePolynomial n k →ₐ[k] Algebraic.CoordinatePolynomial n k => f p)
    (PolynomialAction.Construction.rightTranslate_mul ((g⁻¹).val) (g.val))
  simpa only [Units.inv_mul, PolynomialAction.Construction.rightTranslate_one, AlgHom.id_apply, AlgHom.comp_apply] using h.symm

def rightTranslateUnitEquiv
    {k : Type} [Field k] {n : ℕ} (g : Matrix.GeneralLinearGroup (Fin n) k) :
    Algebraic.CoordinatePolynomial n k ≃ₐ[k] Algebraic.CoordinatePolynomial n k where
  toFun := PolynomialAction.Construction.rightTranslate (g.val)
  invFun := PolynomialAction.Construction.rightTranslate ((g⁻¹).val)
  left_inv := rightTranslate_unit_inverse_left g
  right_inv p := by simpa only [inv_inv] using rightTranslate_unit_inverse_left g⁻¹ p
  map_mul' := map_mul _
  map_add' := map_add _
  commutes' := (PolynomialAction.Construction.rightTranslate (g.val)).commutes

def boundedPolynomialUnitEquiv
    {k : Type} [Field k] {n : ℕ} (d : ℕ) (g : Matrix.GeneralLinearGroup (Fin n) k) :
    BoundedRepresentation.Construction.BoundedPolynomials k n d ≃ₗ[k] BoundedRepresentation.Construction.BoundedPolynomials k n d where
  toFun p := ⟨PolynomialAction.Construction.rightTranslate (g.val) p.val,
    (mem_restrictTotalDegree _ _ _).mpr
      ((PolynomialAction.Construction.rightTranslate_totalDegree_le _ p.val).trans
        ((mem_restrictTotalDegree _ _ _).mp p.property))⟩
  invFun p := ⟨PolynomialAction.Construction.rightTranslate ((g⁻¹).val) p.val,
    (mem_restrictTotalDegree _ _ _).mpr
      ((PolynomialAction.Construction.rightTranslate_totalDegree_le _ p.val).trans
        ((mem_restrictTotalDegree _ _ _).mp p.property))⟩
  left_inv p := Subtype.ext (rightTranslate_unit_inverse_left g p.val)
  right_inv p := Subtype.ext ((rightTranslateUnitEquiv g).apply_symm_apply p.val)
  map_add' p q := Subtype.ext (map_add _ p.val q.val)
  map_smul' c p := Subtype.ext ((PolynomialAction.Construction.rightTranslate (g.val)).toLinearMap.map_smul c p.val)

theorem rightInfinitesimal_unit_conjugation
    {k : Type} [Field k] {n : ℕ} (g : Matrix.GeneralLinearGroup (Fin n) k)
    (A : Matrix (Fin n) (Fin n) k) :
    Infinitesimal.Action.Construction.rightInfinitesimal (g.val * A * (g⁻¹).val) =
      Infinitesimal.Action.Construction.conjugatePolynomialDerivation (rightTranslateUnitEquiv g) (Infinitesimal.Action.Construction.rightInfinitesimal A) := by
  apply MvPolynomial.derivation_ext
  rintro ⟨i, j⟩
  rw [Infinitesimal.Action.Construction.conjugatePolynomialDerivation_apply]
  change Infinitesimal.Action.Construction.rightInfinitesimal (g.val * A * (g⁻¹).val) (X (i, j)) =
    PolynomialAction.Construction.rightTranslate (g.val) (Infinitesimal.Action.Construction.rightInfinitesimal A (PolynomialAction.Construction.rightTranslate ((g⁻¹).val) (X (i, j))))
  rw [Infinitesimal.Action.Construction.rightInfinitesimal_X, PolynomialAction.Construction.rightTranslate_X, Infinitesimal.Action.Construction.rightInfinitesimal_on_linear_entry,
    Infinitesimal.Action.Construction.rightTranslate_on_linear_entry, Matrix.mul_assoc]

theorem boundedInfinitesimal_unit_intertwining
    {k : Type} [Field k] {n : ℕ} (d : ℕ) (g : Matrix.GeneralLinearGroup (Fin n) k)
    (A : Matrix (Fin n) (Fin n) k) :
    (boundedPolynomialUnitEquiv d g).toLinearMap.comp (Infinitesimal.Degree.Construction.boundedInfinitesimal d A) =
      (Infinitesimal.Degree.Construction.boundedInfinitesimal d (g.val * A * (g⁻¹).val)).comp
        (boundedPolynomialUnitEquiv d g).toLinearMap := by
  apply LinearMap.ext
  intro p
  apply Subtype.ext
  change PolynomialAction.Construction.rightTranslate (g.val) (Infinitesimal.Action.Construction.rightInfinitesimal A p.val) =
    Infinitesimal.Action.Construction.rightInfinitesimal (g.val * A * (g⁻¹).val) (PolynomialAction.Construction.rightTranslate (g.val) p.val)
  rw [rightInfinitesimal_unit_conjugation, Infinitesimal.Action.Construction.conjugatePolynomialDerivation_apply]
  change PolynomialAction.Construction.rightTranslate (g.val) (Infinitesimal.Action.Construction.rightInfinitesimal A p.val) =
    PolynomialAction.Construction.rightTranslate (g.val) (Infinitesimal.Action.Construction.rightInfinitesimal A
      (PolynomialAction.Construction.rightTranslate ((g⁻¹).val) (PolynomialAction.Construction.rightTranslate (g.val) p.val)))
  rw [rightTranslate_unit_inverse_left]

theorem boundedInfinitesimal_conjugated_diagonal_isSemisimple
    {k : Type} [Field k] {n : ℕ} (d : ℕ) (g : Matrix.GeneralLinearGroup (Fin n) k)
    (w : Fin n → k) :
    (Infinitesimal.Degree.Construction.boundedInfinitesimal d (g.val * Matrix.diagonal w * (g⁻¹).val)).IsSemisimple := by
  exact (LinearEquiv.isSemisimple_iff _ _ (boundedPolynomialUnitEquiv d g)
    (boundedInfinitesimal_unit_intertwining d g _)).mp
      (BoundedDiagonalAction.Construction.boundedInfinitesimal_diagonal_isSemisimple d w)

end

end OAI.NumberTheory.ArithmeticGroups.Lattices.BoundedGeneralLinearAction.Construction
