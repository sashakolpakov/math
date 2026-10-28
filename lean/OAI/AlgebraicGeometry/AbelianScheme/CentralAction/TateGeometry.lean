import OAI.AlgebraicGeometry.AbelianScheme.CentralAction.ScalarIsogeny
import OAI.AlgebraicGeometry.AbelianScheme.CentralAction.TateTorsion
import OAI.AlgebraicGeometry.AbelianScheme.TateComparison.Etale

/-! # Tate Geometry -/

namespace OAI.AlgebraicGeometry.AbelianScheme.CentralAction.TateGeometry.Construction

noncomputable section

/-! Geometric abelian points admit coherent q-divisions. Thus evaluation
of the actual Tate module surjects onto every actual q-power torsion group. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj

open OAI.AlgebraicGeometry.AbelianScheme.TateComparison.Etale

variable {K : Type} [Field K] [CharZero K] {S : Scheme} {g : ℕ}

theorem abelian_geometric_points_divisible
    (B : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme g S) (base : S ⟶ Spec (.of K))
    (q : ℕ) (hq : q ≠ 0) {k : Type} [Field k] [IsAlgClosed k]
    (t : Spec (.of k) ⟶ S) :
    ∀ x : Additive (Over.mk t ⟶ B.scheme), ∃ y, q • y = x := by
  have hh := ScalarIsogeny.Construction.abelian_multiplier_finite_etale_surjective B q
    (ScalarIsogeny.Construction.nat_unit_on_charZero_scheme base q hq)
  have : Etale ((𝟙 B.scheme) ^ q).left := hh.2.1
  have : Surjective ((𝟙 B.scheme) ^ q).left := hh.2.2
  intro x
  obtain ⟨y, hy⟩ := TateComparison.Etale.etale_surjective_geometric_lift ((𝟙 B.scheme) ^ q) t x.toMul
  refine ⟨Additive.ofMul y, ?_⟩
  rw [MonObj.comp_pow, Category.comp_id] at hy
  exact congrArg Additive.ofMul hy

/-- The torsion quotients used to read a central Tate lattice are the
actual geometric torsion points of the PEL abelian family. -/
theorem schemeTateEvaluation_surjective
    (B : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme g S) (base : S ⟶ Spec (.of K))
    (q : ℕ) [Fact q.Prime] (n : ℕ) {k : Type} [Field k] [IsAlgClosed k]
    (t : Spec (.of k) ⟶ S) :
    Function.Surjective (TateTorsion.Construction.tateEvaluation (H := Additive (Over.mk t ⟶ B.scheme)) q n) :=
  TateTorsion.Construction.tateEvaluation_surjective q
    (abelian_geometric_points_divisible B base q (Fact.out : q.Prime).ne_zero t) n

end

end OAI.AlgebraicGeometry.AbelianScheme.CentralAction.TateGeometry.Construction
