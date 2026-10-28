import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Basis
import OAI.AlgebraicGeometry.AbelianScheme.TateComparison.Evaluation

/-! # Tate Coordinates -/

namespace OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.TateCoordinates.Construction

noncomputable section

/-!
Coordinates on actual q^h-torsion obtained by evaluating the inverse-limit
Tate module. In an integral basis the evaluation kernel is the q^h-scaled
lattice, so the resulting residue coordinates describe the original
torsion group, rather than only an abstract group of the same order.
-/

open _root_.Module

variable (q : ℕ) [Fact q.Prime] {d : ℕ}

theorem basisDiagonalSubmodule_const {V : Type*} [AddCommGroup V] [Module ℤ_[q] V]
    (b : Basis (Fin d) ℤ_[q] V) (h : ℕ) :
    IsogenyQuotient.Basis.Construction.basisDiagonalSubmodule q b (fun _ => h) =
      ((q : ℤ_[q]) ^ h • (LinearMap.id : V →ₗ[ℤ_[q]] V)).range := by
  let f : V →ₗ[ℤ_[q]] V := (q : ℤ_[q]) ^ h • LinearMap.id
  change Submodule.span ℤ_[q] (Set.range (f ∘ b)) = f.range
  rw [Set.range_comp, ← Submodule.map_span, b.span_eq, Submodule.map_top]

variable {H : Type*} [AddCommGroup H]
  (b : Basis (Fin d) ℤ_[q] (TateComparison.Add.Tate.Module (H := H) q))
  (hdiv : ∀ x : H, ∃ y, q • y = x) (h : ℕ)

theorem tate_evaluate_ker_eq_diagonal :
    (TateComparison.Evaluation.Tate.evaluate (H := H) q h).ker = IsogenyQuotient.Basis.Construction.basisDiagonalSubmodule q b (fun _ => h) := by
  rw [basisDiagonalSubmodule_const]
  ext x
  change TateComparison.Evaluation.Tate.evaluate q h x = 0 ↔ ∃ y, (q : ℤ_[q]) ^ h • y = x
  exact TateComparison.Evaluation.Tate.evaluate_eq_zero_iff q h x

def tateTorsionCoordinates : TateComparison.Add.Tate.torsion q H h ≃+ (Fin d → ZMod (q ^ h)) :=
  ((TateComparison.Evaluation.Tate.torsionQuotientEquiv q hdiv h).toAddEquiv.symm.trans
    (QuotientAddGroup.quotientAddEquivOfEq
      (congrArg Submodule.toAddSubgroup (tate_evaluate_ker_eq_diagonal q b h)))).trans
    (IsogenyQuotient.Basis.Construction.basisDiagonalQuotientEquiv q b (fun _ => h))

theorem tateTorsionCoordinates_evaluate (x : TateComparison.Add.Tate.Module (H := H) q) :
    tateTorsionCoordinates q b hdiv h (TateComparison.Evaluation.Tate.evaluate q h x) =
      IsogenyQuotient.Basis.Construction.basisCoordinateResidues q b (fun _ => h) x := by
  have hx : (TateComparison.Evaluation.Tate.torsionQuotientEquiv q hdiv h)
      (Submodule.Quotient.mk x) = TateComparison.Evaluation.Tate.evaluate q h x := rfl
  rw [← hx]
  change IsogenyQuotient.Basis.Construction.basisDiagonalQuotientEquiv q b (fun _ => h)
    ((QuotientAddGroup.quotientAddEquivOfEq
      (congrArg Submodule.toAddSubgroup (tate_evaluate_ker_eq_diagonal q b h)))
      ((TateComparison.Evaluation.Tate.torsionQuotientEquiv q hdiv h).symm
        ((TateComparison.Evaluation.Tate.torsionQuotientEquiv q hdiv h) (Submodule.Quotient.mk x)))) = _
  rw [LinearEquiv.symm_apply_apply]
  rfl

end

end OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.TateCoordinates.Construction
