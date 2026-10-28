import OAI.NumberTheory.ArithmeticGroups.Lattices.MatrixInvariantExponential
import OAI.NumberTheory.ArithmeticGroups.Lattices.Infinitesimal.Action

/-! # Exponential Normal -/

namespace OAI.NumberTheory.ArithmeticGroups.Lattices.ExponentialNormal.Construction

noncomputable section

section

/-! Conjugation-stable matrix Lie subalgebras generate normal exponential
subgroups. -/

open scoped Classical _root_.Matrix.Norms.Operator
open NormedSpace Set

attribute [local instance] LieRing.ofAssociativeRing

theorem sl_inverse_matrix {k : Type} [Field k] {n : ℕ} (g : Algebraic.SL n k) :
    ((g⁻¹ : Algebraic.SL n k) : Matrix (Fin n) (Fin n) k) = (g : Matrix (Fin n) (Fin n) k)⁻¹ := by
  rw [Matrix.inv_def, g.property, Ring.inverse_one, one_smul]
  rfl

theorem infinitesimalExponential_conjugation {n : ℕ}
    (G : Algebraic.MatrixAlgebraicGroup ℂ n) (g : G.RationalPoints) (A : Infinitesimal.Action.Construction.infinitesimalStabilizer G) :
    ExponentialIntegration.Construction.infinitesimalExponential G
      ⟨(g.val : Matrix (Fin n) (Fin n) ℂ) * A.val * (g.val⁻¹ : Algebraic.SL n ℂ),
        Infinitesimal.Action.Construction.infinitesimalStabilizer_conjugation G g A.property⟩ 1 =
      g * ExponentialIntegration.Construction.infinitesimalExponential G A 1 * g⁻¹ := by
  apply Subtype.ext
  apply Subtype.ext
  change exp ((1 : ℂ) • ((g.val : Matrix (Fin n) (Fin n) ℂ) * A.val * (g.val⁻¹ : Algebraic.SL n ℂ))) =
    (g.val : Matrix (Fin n) (Fin n) ℂ) * exp ((1 : ℂ) • A.val) * (g.val⁻¹ : Algebraic.SL n ℂ)
  simp only [one_smul, sl_inverse_matrix]
  apply Matrix.exp_conj
  exact (Matrix.isUnit_iff_isUnit_det _).mpr (by rw [g.val.property]; exact isUnit_one)

theorem exponentialGeneratedSubgroup_normal {n : ℕ}
    (G : Algebraic.MatrixAlgebraicGroup ℂ n)
    (S : LieSubalgebra ℂ (Matrix (Fin n) (Fin n) ℂ)) (hS : S ≤ Infinitesimal.Action.Construction.infinitesimalStabilizer G)
    (hconj : ∀ g : G.RationalPoints, ∀ A ∈ S,
      (g.val : Matrix (Fin n) (Fin n) ℂ) * A * (g.val⁻¹ : Algebraic.SL n ℂ) ∈ S) :
    (MatrixInvariantExponential.Construction.exponentialGeneratedSubgroup G S hS).Normal := by
  let H := MatrixInvariantExponential.Construction.exponentialGeneratedSubgroup G S hS
  have hle : H ≤ H.normalCore := by
    change Subgroup.closure _ ≤ _
    rw [Subgroup.closure_le]
    rintro _ ⟨A, rfl⟩ g
    let B : S := ⟨(g.val : Matrix (Fin n) (Fin n) ℂ) * A.val * (g.val⁻¹ : Algebraic.SL n ℂ),
      hconj g A.val A.property⟩
    have hb : ExponentialIntegration.Construction.infinitesimalExponential G ⟨B.val, hS B.property⟩ 1 ∈ H :=
      Subgroup.subset_closure ⟨B, rfl⟩
    rw [← infinitesimalExponential_conjugation G g ⟨A.val, hS A.property⟩]
    exact hb
  have heq : H = H.normalCore := le_antisymm hle H.normalCore_le
  change H.Normal
  rw [heq]
  infer_instance

end

/-! Invariance of the solvable radical and the group's adjoint action on
its infinitesimal stabilizer. -/

open scoped Classical

theorem LieEquiv_preserves_radical
    {R L : Type*} [CommRing R] [LieRing L] [LieAlgebra R L] [IsNoetherian R L]
    (e : L ≃ₗ⁅R⁆ L) {x : L} (hx : x ∈ LieAlgebra.radical R L) :
    e x ∈ LieAlgebra.radical R L := by
  let I := LieAlgebra.radical R L
  let J := LieIdeal.comap e.symm.toLieHom I
  let f : J →ₗ⁅R⁆ I :=
    { toFun := fun y => ⟨e.symm y.val, y.property⟩
      map_add' := fun a b => Subtype.ext (e.symm.map_add a.val b.val)
      map_smul' := fun c a => Subtype.ext (e.symm.map_smul c a.val)
      map_lie' := fun {a b} => Subtype.ext (e.symm.map_lie a.val b.val) }
  have hf : Function.Injective f := by
    intro a b h
    exact Subtype.ext (e.symm.injective (congrArg Subtype.val h))
  let : LieAlgebra.IsSolvable J := hf.lieAlgebra_isSolvable
  have hle : J ≤ I := (LieAlgebra.LieIdeal.solvable_iff_le_radical R L J).mp inferInstance
  apply hle
  change e.symm (e x) ∈ I
  simpa only [e.symm_apply_apply] using hx

attribute [local instance] LieRing.ofAssociativeRing

def infinitesimalAdjoint {k : Type} [Field k] {n : ℕ}
    (G : Algebraic.MatrixAlgebraicGroup k n) (g : G.RationalPoints) :
    Infinitesimal.Action.Construction.infinitesimalStabilizer G ≃ₗ⁅k⁆ Infinitesimal.Action.Construction.infinitesimalStabilizer G := by
  let M : Matrix (Fin n) (Fin n) k := g.val
  let Mi : Matrix (Fin n) (Fin n) k := (g.val⁻¹ : Algebraic.SL n k)
  let hM : Invertible M :=
    { invOf := Mi
      invOf_mul_self := by
        change ((g.val⁻¹ * g.val : Algebraic.SL n k) : Matrix (Fin n) (Fin n) k) = 1
        rw [inv_mul_cancel]
        rfl
      mul_invOf_self := by
        change ((g.val * g.val⁻¹ : Algebraic.SL n k) : Matrix (Fin n) (Fin n) k) = 1
        rw [mul_inv_cancel]
        rfl }
  let e := Matrix.lieConj M hM
  have he (A : Matrix (Fin n) (Fin n) k) : e A = M * A * Mi := by
    rw [Matrix.lieConj_apply, ← sl_inverse_matrix g.val]
  have hmap : (Infinitesimal.Action.Construction.infinitesimalStabilizer G).map e.toLieHom = Infinitesimal.Action.Construction.infinitesimalStabilizer G := by
    apply LieSubalgebra.toSubmodule_injective
    apply Submodule.eq_of_le_of_finrank_eq
    · rintro _ ⟨A, hA, rfl⟩
      change e A ∈ Infinitesimal.Action.Construction.infinitesimalStabilizer G
      rw [he]
      exact Infinitesimal.Action.Construction.infinitesimalStabilizer_conjugation G g hA
    · exact LinearEquiv.finrank_map_eq e.toLinearEquiv _
  exact e.ofSubalgebras _ _ hmap

theorem infinitesimalAdjoint_apply {k : Type} [Field k] {n : ℕ}
    (G : Algebraic.MatrixAlgebraicGroup k n) (g : G.RationalPoints) (A : Infinitesimal.Action.Construction.infinitesimalStabilizer G) :
    (infinitesimalAdjoint G g A).val =
      (g.val : Matrix (Fin n) (Fin n) k) * A.val * (g.val⁻¹ : Algebraic.SL n k) := by
  simp only [infinitesimalAdjoint, LieEquiv.ofSubalgebras_apply, Matrix.lieConj_apply,
    sl_inverse_matrix]

end

end OAI.NumberTheory.ArithmeticGroups.Lattices.ExponentialNormal.Construction
