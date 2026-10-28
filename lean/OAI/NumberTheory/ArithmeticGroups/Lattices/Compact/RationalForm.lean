import OAI.NumberTheory.ArithmeticGroups.Lattices.Positive.FormDescent
import OAI.NumberTheory.ArithmeticGroups.Lattices.InvariantFormDerivative
import OAI.NumberTheory.ArithmeticGroups.Lattices.Infinitesimal.TangentExtension

/-! # Rational Form -/

namespace OAI.NumberTheory.ArithmeticGroups.Lattices.Compact.RationalForm.Construction

noncomputable section

/-! A compact real place supplies a positive bilinear form defined over
the original field and invariant under its infinitesimal matrix group. -/

open scoped Classical _root_.Matrix.Norms.Elementwise
open _root_.Matrix

attribute [local instance] LieRing.ofAssociativeRing

def bilinearFormInfinitesimalMap {k : Type} [Field k] {n : ℕ}
    (Q : Matrix (Fin n) (Fin n) k) :
    Matrix (Fin n) (Fin n) k →ₗ[k] Matrix (Fin n) (Fin n) k where
  toFun A := A.transpose * Q + Q * A
  map_add' A B := by simp only [Matrix.transpose_add, Matrix.add_mul, Matrix.mul_add]; abel
  map_smul' c A := by
    simp only [Matrix.transpose_smul, Matrix.smul_mul, Matrix.mul_smul, smul_add, RingHom.id_apply]

theorem bilinear_form_invariant_of_basis
    {k ι : Type} [Field k] {n : ℕ}
    (W : Submodule k (Matrix (Fin n) (Fin n) k)) (b : Module.Basis ι k W)
    (Q : Matrix (Fin n) (Fin n) k)
    (hb : ∀ i, Bilinear.InvariantSystem.Construction.bilinearLieVariation (b i).val Q = 0) :
    ∀ A ∈ W, A.transpose * Q + Q * A = 0 := by
  have hz : (bilinearFormInfinitesimalMap Q).comp W.subtype = 0 := by
    apply b.ext
    intro i
    exact hb i
  intro A hA
  exact LinearMap.congr_fun hz ⟨A, hA⟩

theorem compact_real_place_positive_infinitesimal_form
    {k : Type} [Field k] [CharZero k] (G : Algebraic.ConnectedSemisimpleKGroup k)
    (v : k →+* ℝ) (hv : Algebraic.IsCompactAtRealPlace G v) :
    ∃ q : Matrix (Fin G.dimension) (Fin G.dimension) k,
      (∀ A ∈ Infinitesimal.Action.Construction.infinitesimalStabilizer G.matrixGroup, A.transpose * q + q * A = 0) ∧
      ∀ x : Fin G.dimension → ℝ, x ≠ 0 → 0 < dotProduct x ((q.map v).mulVec x) := by
  let : Algebra k ℝ := v.toAlgebra
  obtain ⟨Q, hpos, hQ⟩ := InvariantGram.Construction.compact_real_place_invariant_positive_matrix G v hv
  let H := BaseChange.Construction.matrixGroupBaseChange G.matrixGroup (algebraMap k ℝ)
  have hHQ : ∀ g : H.RationalPoints,
      (g.val : Matrix (Fin G.dimension) (Fin G.dimension) ℝ).transpose * Q *
        (g.val : Matrix (Fin G.dimension) (Fin G.dimension) ℝ) = Q := by
    intro g
    apply hQ ⟨g.val, ?_⟩
    have hg := g.property
    change g.val ∈ G.matrixGroup.subgroup ℝ ((RingHom.id ℝ).comp v) at hg
    simpa only [RingHom.id_comp] using hg
  let W := (Infinitesimal.Action.Construction.infinitesimalStabilizer G.matrixGroup).toSubmodule
  let b := Module.finBasis k W
  have hb (i : Fin (Module.finrank k W)) :
      Bilinear.InvariantSystem.Construction.bilinearLieVariation (((b i).val).map (algebraMap k ℝ)) Q = 0 := by
    exact InvariantFormDerivative.Construction.invariant_form_infinitesimal H Q hHQ
      ⟨((b i).val).map (algebraMap k ℝ),
        CharZeroTangent.Construction.infinitesimalStabilizer_coefficient_map G.matrixGroup G.connected (b i).property⟩
  obtain ⟨q, hq, hqpos⟩ := Positive.FormDescent.Construction.positive_bilinear_system_solution_descends (fun i => (b i).val) Q hb hpos
  exact ⟨q, bilinear_form_invariant_of_basis W b q hq, hqpos⟩

end

end OAI.NumberTheory.ArithmeticGroups.Lattices.Compact.RationalForm.Construction
