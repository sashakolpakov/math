import Mathlib.CategoryTheory.Sites.LocallySurjective
import Mathlib.Algebra.Category.Grp.Basic

/-! # Local Surjectivity -/

namespace OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Picard.LocalSurjectivity.Construction

/-! A local lifting criterion for a homomorphism of commutative-group
presheaves. It separates lifting after Picard pullback from lifting the
pullback kernel. Neither condition asserts representability. -/

open _root_.CategoryTheory Opposite

universe u v w

variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)
  {P Q R : Cᵒᵖ ⥤ CommGrpCat.{w}} (f : P ⟶ Q) (g : Q ⟶ R)

/-- Local lifts after a second map, together with local lifts of its
kernel, give local lifts of every section. -/
theorem locallySurjective_of_composite_and_kernel
    [Presheaf.IsLocallySurjective J (f ≫ g)]
    (hkernel : ∀ (T : C) (x : Q.obj (op T)), g.app (op T) x = 1 →
      Presheaf.imageSieve f x ∈ J T) : Presheaf.IsLocallySurjective J f := by
  constructor
  intro T y
  apply J.transitive (Presheaf.imageSieve_mem J (f ≫ g) (g.app (op T) y))
  intro U a ha
  let x := Presheaf.localPreimage (f ≫ g) (g.app (op T) y) a ha
  have hx : g.app (op U) (f.app (op U) x) = R.map a.op (g.app (op T) y) :=
    Presheaf.app_localPreimage (f ≫ g) (g.app (op T) y) a ha
  let d := Q.map a.op y * (f.app (op U) x)⁻¹
  have hd : g.app (op U) d = 1 := by
    change g.app (op U) (Q.map a.op y * (f.app (op U) x)⁻¹) = 1
    rw [map_mul, map_inv, g.naturality_apply, hx, mul_inv_cancel]
  apply J.superset_covering _ (hkernel U d hd)
  intro V b hb
  obtain ⟨z, hz⟩ := hb
  refine ⟨z * P.map b.op x, ?_⟩
  change f.app (op V) (z * P.map b.op x) = Q.map (b ≫ a).op y
  rw [map_mul, hz, f.naturality_apply, op_comp, Q.map_comp]
  change Q.map b.op d * Q.map b.op (f.app (op U) x) = Q.map b.op (Q.map a.op y)
  dsimp only [d]
  rw [map_mul, map_inv, inv_mul_cancel_right]

end OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Picard.LocalSurjectivity.Construction
