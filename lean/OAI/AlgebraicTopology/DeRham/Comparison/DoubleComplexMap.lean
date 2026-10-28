import OAI.AlgebraicTopology.DeRham.Comparison.DoubleComplexMapNormalization
import OAI.AlgebraicTopology.DeRham.Comparison.DoubleComplexQuasiIso

/-! # Double Complex Map -/

namespace OAI.AlgebraicTopology.DeRham.Comparison.DoubleComplexMap.DoubleComplex

noncomputable section

/-!
# Columnwise quasi-isomorphisms induce a quasi-isomorphism on total complexes

The proof uses the explicit finite relative-cycle elimination theorem. No
spectral-sequence comparison or presumed total quasi-isomorphism is used.
-/

open _root_.CategoryTheory

universe u v

variable {R : Type u} [Ring R]
  {K L : HomologicalComplex₂ (ModuleCat.{v} R)
    (ComplexShape.up ℕ) (ComplexShape.up ℕ)} (φ : K ⟶ L)

/-- A morphism of first-quadrant double complexes which is a quasi-isomorphism
in every column induces a quasi-isomorphism of the native total complexes. -/
theorem total_map_quasiIso_of_columns (hφ : ∀ p : ℕ, QuasiIso (φ.f p)) :
    QuasiIso (HomologicalComplex₂.total.map φ (ComplexShape.up ℕ)) := by
  apply DoubleComplexQuasiIso.DoubleComplex.quasiIso_of_cycle_lift_and_boundary_reflection
  · intro n
    have hp : (ComplexShape.up ℕ).prev n = n.pred := by
      cases n <;> simp
    let P (i j : ℕ) : Prop :=
      ∀ y : (L.total (ComplexShape.up ℕ)).X n,
        (L.total (ComplexShape.up ℕ)).d n j y = 0 →
        ∃ x : (K.total (ComplexShape.up ℕ)).X n,
          (K.total (ComplexShape.up ℕ)).d n j x = 0 ∧
            ∃ z : (L.total (ComplexShape.up ℕ)).X i,
              (L.total (ComplexShape.up ℕ)).d i n z =
                (HomologicalComplex₂.total.map φ (ComplexShape.up ℕ)).f n x - y
    have hP : P n.pred (n + 1) := by
      intro y hy
      obtain ⟨a, b, ha, hb⟩ := DoubleComplexMapNormalization.DoubleComplex.total_relative_primitive_succ φ hφ n 0 y
        (map_zero _) (by rw [map_zero, hy])
      refine ⟨a, ha.symm, b, ?_⟩
      rw [hb]
      abel
    exact (congrArg₂ P hp (CochainComplex.next ℕ n)).mpr hP
  · intro n
    have hp : (ComplexShape.up ℕ).prev n = n.pred := by
      cases n <;> simp
    let P (i j : ℕ) : Prop :=
      ∀ x : (K.total (ComplexShape.up ℕ)).X n,
        (K.total (ComplexShape.up ℕ)).d n j x = 0 →
        (∃ y : (L.total (ComplexShape.up ℕ)).X i,
          (L.total (ComplexShape.up ℕ)).d i n y =
            (HomologicalComplex₂.total.map φ (ComplexShape.up ℕ)).f n x) →
        ∃ z : (K.total (ComplexShape.up ℕ)).X i,
          (K.total (ComplexShape.up ℕ)).d i n z = x
    have hP : P n.pred (n + 1) := by
      intro x hx hy
      cases n with
      | zero =>
        obtain ⟨y, hy⟩ := hy
        have hshape : (L.total (ComplexShape.up ℕ)).d 0 0 = 0 :=
          (L.total (ComplexShape.up ℕ)).shape 0 0 (by decide)
        have hfzero : (HomologicalComplex₂.total.map φ (ComplexShape.up ℕ)).f 0 x = 0 := by
          change (L.total (ComplexShape.up ℕ)).d 0 0 y =
            (HomologicalComplex₂.total.map φ (ComplexShape.up ℕ)).f 0 x at hy
          rw [hshape] at hy
          exact hy.symm
        have hxzero := DoubleComplexMapReduction.DoubleComplex.total_relative_cycle_zero φ hφ x hx hfzero
        exact ⟨0, by simpa only [map_zero] using hxzero.symm⟩
      | succ n =>
        obtain ⟨y, hy⟩ := hy
        obtain ⟨a, _, ha, _⟩ := DoubleComplexMapNormalization.DoubleComplex.total_relative_primitive_succ φ hφ n x y hx hy.symm
        exact ⟨a, ha.symm⟩
    exact (congrArg₂ P hp (CochainComplex.next ℕ n)).mpr hP

end

end OAI.AlgebraicTopology.DeRham.Comparison.DoubleComplexMap.DoubleComplex
