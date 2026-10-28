import OAI.NumberTheory.ArithmeticGroups.Lattices.UniformExteriorLine
import OAI.NumberTheory.ArithmeticGroups.Lattices.BoundedRepresentation

/-! # Uniform Exterior Line -/

namespace OAI.NumberTheory.ArithmeticGroups.Lattices.Finite.UniformExteriorLine.Construction

noncomputable section

/-! The uniform exterior line lies in the exterior power of a fixed
finite-dimensional bounded-degree polynomial representation. -/

open scoped Classical TensorProduct
open _root_.MvPolynomial

theorem exterior_line_equality_iff_injective_map
    {k V W : Type*} [Field k] [AddCommGroup V] [Module k V]
    [AddCommGroup W] [Module k W] {r : ℕ}
    (f : V →ₗ[k] W) (hf : Function.Injective f) (v w : Fin r → V) (c : k) :
    ExteriorAlgebra.ιMulti k r (f ∘ v) = c • ExteriorAlgebra.ιMulti k r (f ∘ w) ↔
      exteriorPower.ιMulti k r v = c • exteriorPower.ιMulti k r w := by
  constructor
  · intro h
    apply exteriorPower.map_injective_field (n := r) hf
    rw [map_smul, exteriorPower.map_apply_ιMulti, exteriorPower.map_apply_ιMulti]
    exact Subtype.ext h
  · intro h
    have he := congrArg (exteriorPower.map r f) h
    rw [map_smul, exteriorPower.map_apply_ιMulti, exteriorPower.map_apply_ιMulti] at he
    exact congrArg Subtype.val he

def boundedCoefficientMap
    {k K : Type} [Field k] [Field K] [Algebra k K] {n d : ℕ}
    (p : BoundedRepresentation.Construction.BoundedPolynomials k n d) : BoundedRepresentation.Construction.BoundedPolynomials K n d :=
  ⟨MvPolynomial.map (algebraMap k K) p.val,
    (mem_restrictTotalDegree _ _ _).mpr ((UniformPolynomialStabilizer.Construction.coefficient_map_totalDegree_le _ _).trans
      ((mem_restrictTotalDegree _ _ _).mp p.property))⟩

theorem exists_finite_uniform_exterior_line_stabilizer
    {k : Type} [Field k] [CharZero k] {n : ℕ}
    (G : Algebraic.MatrixAlgebraicGroup k n) (hG : G.IsGeometricallyConnected) :
    ∃ d r : ℕ, ∃ p : Fin r → BoundedRepresentation.Construction.BoundedPolynomials k n d,
      ∀ (K : Type) [Field K] [Algebra k K],
        LinearIndependent K (fun i => boundedCoefficientMap (K := K) (p i)) ∧
        ∀ g : Algebraic.SL n K, g ∈ G.subgroup K (algebraMap k K) ↔
          ∃ c : K, c ≠ 0 ∧
            exteriorPower.map r (BoundedRepresentation.Construction.boundedPolynomialRepresentation d g).toLinearMap
              (exteriorPower.ιMulti K r (fun i => boundedCoefficientMap (K := K) (p i))) =
                c • exteriorPower.ιMulti K r (fun i => boundedCoefficientMap (K := K) (p i)) := by
  obtain ⟨d, r, p, hp, hline⟩ := UniformExteriorLine.Construction.exists_uniform_exterior_line_stabilizer G hG
  let q : Fin r → BoundedRepresentation.Construction.BoundedPolynomials k n d := fun i =>
    ⟨p i, (mem_restrictTotalDegree _ _ _).mpr (hp i)⟩
  refine ⟨d, r, q, fun K _ _ => ?_⟩
  obtain ⟨hlin, hg⟩ := hline K
  let f := (BoundedRepresentation.Construction.BoundedPolynomials K n d).subtype
  let qK : Fin r → BoundedRepresentation.Construction.BoundedPolynomials K n d := fun i => boundedCoefficientMap (K := K) (q i)
  refine ⟨LinearIndependent.of_comp f hlin, fun g => ?_⟩
  rw [hg g]
  apply exists_congr
  intro c
  apply and_congr_right
  intro _
  rw [exteriorPower.map_apply_ιMulti]
  exact exterior_line_equality_iff_injective_map f Subtype.val_injective
    (BoundedRepresentation.Construction.boundedPolynomialRepresentation d g ∘ qK) qK c

end

end OAI.NumberTheory.ArithmeticGroups.Lattices.Finite.UniformExteriorLine.Construction
