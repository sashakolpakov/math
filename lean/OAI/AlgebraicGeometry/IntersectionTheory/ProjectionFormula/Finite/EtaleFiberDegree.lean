import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Finite.EtaleDegree
import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Affine.FiberDegree
import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Affine.GenericDegree
import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Smooth.GenericField
import Mathlib.AlgebraicGeometry.Morphisms.Finite
import Mathlib.AlgebraicGeometry.Morphisms.Etale

/-! # Etale Fiber Degree -/

namespace OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Finite.EtaleFiberDegree

noncomputable section

/-! On a finite etale morphism of integral schemes, the sum of
native residue degrees in every fiber equals the generic degree. -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open _root_.CategoryTheory _root_.AlgebraicGeometry

theorem sum {X Y : Scheme.{0}} [IsIntegral X] [IsIntegral Y] (f : X ⟶ Y) [IsFinite f] [Etale f]
    (y : Y) [Fintype (f ⁻¹' ({y} : Set Y))] :
    ∑ x : f ⁻¹' ({y} : Set Y), f.residueDegree x.val = f.residueDegree (genericPoint X) := by
  obtain ⟨U, hU, hy, _⟩ := exists_isAffineOpen_mem_and_subset (show y ∈ (⊤ : Y.Opens) from trivial)
  let : Nonempty U := ⟨⟨y, hy⟩⟩
  have hη := Smooth.GenericField.genericPoint_image f
  have hηU : genericPoint Y ∈ U := (genericPoint_specializes y).mem_open U.isOpen hy
  let : Nonempty (f ⁻¹ᵁ U) := ⟨⟨genericPoint X, by change f (genericPoint X) ∈ U; rwa [hη]⟩⟩
  have hV : IsAffineOpen (f ⁻¹ᵁ U) := hU.preimage f
  let R := Γ(Y, U)
  let S := Γ(X, f ⁻¹ᵁ U)
  let : Algebra R S := (f.app U).hom.toAlgebra
  let : Module.Finite R S := f.finite_app U hU
  let : Algebra.Etale R S := by
    change (f.app U).hom.Etale
    rw [Scheme.Hom.app_eq_appLE]
    exact f.etale_appLE hU hV le_rfl
  let p := Affine.FiberDegree.prime U hU y hy
  let : Fintype (p.asIdeal.primesOver S) := Fintype.ofEquiv (f ⁻¹' ({y} : Set Y))
    (Affine.FiberDegree.equiv f U hU hV y hy).symm
  calc
    _ = ∑ q : p.asIdeal.primesOver S, q.val.inertiaDeg R := Affine.FiberDegree.sum f U hU hV y hy
    _ = Module.finrank R S := EtaleDegree.algebra_sum R S p.asIdeal
    _ = _ := Affine.GenericDegree.rank f hη U hU hV

end

end OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Finite.EtaleFiberDegree
