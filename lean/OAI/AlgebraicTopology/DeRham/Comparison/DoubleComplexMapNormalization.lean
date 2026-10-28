import OAI.AlgebraicTopology.DeRham.Comparison.DoubleComplexMapReduction

/-! # Double Complex Map Normalization -/

namespace OAI.AlgebraicTopology.DeRham.Comparison.DoubleComplexMapNormalization.DoubleComplex

noncomputable section

/-!
# Finite elimination of relative cycles of total-complex maps

The induction removes the leftmost occupied horizontal column of a pair
`(x,y)` satisfying `d x = 0` and `φ x = d y`. Only the native total
complexes and their actual cochain map occur in the statement.
-/

open _root_.CategoryTheory

universe u v

variable {R : Type u} [Ring R]
  {K L : HomologicalComplex₂ (ModuleCat.{v} R)
    (ComplexShape.up ℕ) (ComplexShape.up ℕ)} (φ : K ⟶ L)

/-- A relative cycle for the total map has an actual relative primitive
whenever each column map is a quasi-isomorphism. -/
theorem total_relative_primitive_succ (hφ : ∀ p : ℕ, QuasiIso (φ.f p))
    (n : ℕ) (x : (K.total (ComplexShape.up ℕ)).X (n + 1))
    (y : (L.total (ComplexShape.up ℕ)).X n)
    (hx : (K.total (ComplexShape.up ℕ)).d (n + 1) (n + 2) x = 0)
    (hxy : (HomologicalComplex₂.total.map φ (ComplexShape.up ℕ)).f (n + 1) x =
      (L.total (ComplexShape.up ℕ)).d n (n + 1) y) :
    ∃ a : (K.total (ComplexShape.up ℕ)).X n,
      ∃ b : (L.total (ComplexShape.up ℕ)).X n.pred,
        x = (K.total (ComplexShape.up ℕ)).d n (n + 1) a ∧
          y = (HomologicalComplex₂.total.map φ (ComplexShape.up ℕ)).f n a -
            (L.total (ComplexShape.up ℕ)).d n.pred n b := by
  have aux : ∀ r m : ℕ, r + m = n + 1 →
      ∀ (x : (K.total (ComplexShape.up ℕ)).X (n + 1))
        (y : (L.total (ComplexShape.up ℕ)).X n),
        DoubleComplexLowerSupport.DoubleComplex.SupportedFrom K (n + 1) m x → DoubleComplexLowerSupport.DoubleComplex.SupportedFrom L n m y →
        (K.total (ComplexShape.up ℕ)).d (n + 1) (n + 2) x = 0 →
        (HomologicalComplex₂.total.map φ (ComplexShape.up ℕ)).f (n + 1) x =
          (L.total (ComplexShape.up ℕ)).d n (n + 1) y →
        ∃ a : (K.total (ComplexShape.up ℕ)).X n,
          ∃ b : (L.total (ComplexShape.up ℕ)).X n.pred,
            x = (K.total (ComplexShape.up ℕ)).d n (n + 1) a ∧
              y = (HomologicalComplex₂.total.map φ (ComplexShape.up ℕ)).f n a -
                (L.total (ComplexShape.up ℕ)).d n.pred n b := by
    intro r
    induction r with
    | zero =>
      intro m hm x y hxs hys hx hxy
      have hm' : m = n + 1 := by omega
      subst m
      obtain ⟨hx0, hy0⟩ := DoubleComplexMapReduction.DoubleComplex.relative_supported_last_zero φ hφ n x y hxs hys hx hxy
      refine ⟨0, 0, ?_, ?_⟩
      · simpa only [map_zero] using hx0
      · simpa only [map_zero, sub_zero] using hy0
    | succ r ih =>
      intro m hm x y hxs hys hx hxy
      have hmr : m + r = n := by omega
      obtain ⟨a, b, hxs', hys'⟩ := DoubleComplexMapReduction.DoubleComplex.raise_relative_support φ hφ n m r hmr x y hxs hys hx hxy
      have hi := DoubleComplexRelativeBoundary.DoubleComplex.relative_cycle_sub_boundary
        (HomologicalComplex₂.total.map φ (ComplexShape.up ℕ)) n x y a b hx hxy
      obtain ⟨a', b', hx', hy'⟩ := ih (m + 1) (by omega)
        (x - (K.total (ComplexShape.up ℕ)).d n (n + 1) a)
        (y - (HomologicalComplex₂.total.map φ (ComplexShape.up ℕ)).f n a +
          (L.total (ComplexShape.up ℕ)).d n.pred n b) hxs' hys' hi.1 hi.2
      exact ⟨a' + a, b' + b, DoubleComplexRelativeBoundary.DoubleComplex.relative_boundary_add
        (HomologicalComplex₂.total.map φ (ComplexShape.up ℕ)) n x y a a' b b' hx' hy'⟩
  exact aux (n + 1) 0 (by omega) x y
    (DoubleComplexLowerSupport.DoubleComplex.supportedFrom_zero_degree K (n + 1) x) (DoubleComplexLowerSupport.DoubleComplex.supportedFrom_zero_degree L n y) hx hxy

end

end OAI.AlgebraicTopology.DeRham.Comparison.DoubleComplexMapNormalization.DoubleComplex
