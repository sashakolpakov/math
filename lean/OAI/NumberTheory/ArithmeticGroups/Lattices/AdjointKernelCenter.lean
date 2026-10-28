import OAI.NumberTheory.ArithmeticGroups.Lattices.ConnectedLieCentralizer
import OAI.NumberTheory.ArithmeticGroups.Lattices.ExponentialNormal
import OAI.NumberTheory.ArithmeticGroups.Lattices.SemisimpleCenter

/-! # Adjoint Kernel Center -/

namespace OAI.NumberTheory.ArithmeticGroups.Lattices.AdjointKernelCenter.Construction

noncomputable section

/-! The kernel of the adjoint action of a connected group is central;
the geometric adjoint kernel of an Lattices semisimple group is finite. -/

open scoped Classical

theorem adjoint_trivial_mem_center
    {k : Type} [Field k] [CharZero k] {n : ℕ}
    (G : Algebraic.MatrixAlgebraicGroup k n) (hG : G.IsGeometricallyConnected)
    (g : G.RationalPoints)
    (hg : ∀ A : Infinitesimal.Action.Construction.infinitesimalStabilizer G, ExponentialNormal.Construction.infinitesimalAdjoint G g A = A) :
    g ∈ Subgroup.center G.RationalPoints := by
  have hc : ∀ A ∈ Infinitesimal.Action.Construction.infinitesimalStabilizer G,
      A * (g.val : Matrix (Fin n) (Fin n) k) = (g.val : Matrix (Fin n) (Fin n) k) * A := by
    intro A hA
    have he := congrArg (fun B : Infinitesimal.Action.Construction.infinitesimalStabilizer G => B.val) (hg ⟨A, hA⟩)
    rw [ExponentialNormal.Construction.infinitesimalAdjoint_apply] at he
    have hm := congrArg (fun B : Matrix (Fin n) (Fin n) k =>
      B * (g.val : Matrix (Fin n) (Fin n) k)) he
    simpa only [Matrix.mul_assoc, ← Matrix.SpecialLinearGroup.coe_mul,
      inv_mul_cancel, Matrix.SpecialLinearGroup.coe_one, Matrix.mul_one] using hm.symm
  apply Subgroup.mem_center_iff.mpr
  intro h
  apply Subtype.ext
  apply Matrix.SpecialLinearGroup.ext
  intro i j
  have he := ConnectedLieCentralizer.Construction.group_commutes_of_infinitesimal_commuting G hG
    (g.val : Matrix (Fin n) (Fin n) k) hc (RingHom.id k) h
  have hm : (g.val : Matrix (Fin n) (Fin n) k).map (RingHom.id k) =
      (g.val : Matrix (Fin n) (Fin n) k) := by ext i j; rfl
  rw [hm] at he
  exact congrArg (fun M => M i j) he

theorem semisimple_geometric_adjoint_kernel_finite
    {k : Type} [Field k] [CharZero k] {n : ℕ}
    (G : Algebraic.MatrixAlgebraicGroup k n) (hG : G.IsGeometricallyConnected)
    (hsemi : G.IsSemisimple) :
    Set.Finite {g : G.GeometricPoints |
      ∀ A : Infinitesimal.Action.Construction.infinitesimalStabilizer (BaseChange.Construction.matrixGroupBaseChange G (algebraMap k (AlgebraicClosure k))),
        (g.val : Matrix (Fin n) (Fin n) (AlgebraicClosure k)) * A.val *
          ((g.val⁻¹ : Algebraic.SL n (AlgebraicClosure k)) : Matrix (Fin n) (Fin n) (AlgebraicClosure k)) = A.val} := by
  let K := AlgebraicClosure k
  let H := BaseChange.Construction.matrixGroupBaseChange G (algebraMap k K)
  have hpoints : H.subgroup K (RingHom.id K) = G.subgroup K (algebraMap k K) := by
    change G.subgroup K ((RingHom.id K).comp (algebraMap k K)) = _
    rw [RingHom.id_comp]
  let e : H.RationalPoints ≃* G.GeometricPoints := MulEquiv.subgroupCongr hpoints
  let : Finite (Subgroup.center G.GeometricPoints) := SemisimpleCenter.Construction.semisimple_geometric_center_finite G hsemi
  apply (Set.toFinite (Subgroup.center G.GeometricPoints : Set G.GeometricPoints)).subset
  intro g hg
  have hh : e.symm g ∈ Subgroup.center H.RationalPoints := by
    apply adjoint_trivial_mem_center H (ConnectedBaseChange.Construction.geometrically_connected_baseChange G hG) (e.symm g)
    intro A
    apply Subtype.ext
    rw [ExponentialNormal.Construction.infinitesimalAdjoint_apply]
    exact hg A
  apply Subgroup.mem_center_iff.mpr
  intro x
  have he := congrArg e ((Subgroup.mem_center_iff.mp hh) (e.symm x))
  simpa only [map_mul, MulEquiv.apply_symm_apply] using he

end

end OAI.NumberTheory.ArithmeticGroups.Lattices.AdjointKernelCenter.Construction
