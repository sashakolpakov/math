import Mathlib.Algebra.Lie.Semisimple.Basic

/-! # Lie Scalar Simplicity -/

namespace OAI.NumberTheory.Quaternion.Arithmetic.LieScalarSimplicity

noncomputable section

/-! Simplicity is retained when changing the scalar field of a Lie
algebra with the same bracket. The scalar-stable part of any ideal
contains its brackets with the whole Lie algebra. -/

variable {κ K L : Type*} [CommRing κ] [CommRing K] [LieRing L]
variable [LieAlgebra κ L] [LieAlgebra K L]

def scalarIdealCore (I : LieIdeal κ L) : LieIdeal K L where
  carrier := {x | ∀ a : K, a • x ∈ I}
  zero_mem' := by intro a; rw [smul_zero]; exact I.zero_mem
  add_mem' hx hy a := by rw [smul_add]; exact I.add_mem (hx a) (hy a)
  smul_mem' b x hx a := by simpa only [smul_smul] using hx (a * b)
  lie_mem := by
    intro x y hy a
    rw [← lie_smul]
    exact I.lie_mem (hy a)

theorem scalarIdealCore_mem (I : LieIdeal κ L) {x : L} (hx : x ∈ scalarIdealCore (K := K) I) :
    x ∈ I := by
  simpa only [one_smul] using hx (1 : K)

theorem lie_mem_scalarIdealCore (I : LieIdeal κ L) (x : L) {y : L} (hy : y ∈ I) :
    ⁅x, y⁆ ∈ scalarIdealCore (K := K) I := by
  intro a
  rw [← smul_lie]
  exact I.lie_mem hy

theorem isSimple_of_simple_coefficients [LieAlgebra.IsSimple K L] :
    LieAlgebra.IsSimple κ L where
  non_abelian := LieAlgebra.IsSimple.non_abelian K
  eq_bot_or_eq_top I := by
    rcases LieAlgebra.IsSimple.eq_bot_or_eq_top (scalarIdealCore (K := K) I) with hJ | hJ
    · left
      have hcenter : LieAlgebra.center K L = ⊥ := by
        apply (LieAlgebra.IsSimple.eq_bot_or_eq_top (LieAlgebra.center K L)).resolve_right
        intro hc
        exact LieAlgebra.IsSimple.non_abelian K
          ((LieAlgebra.isLieAbelian_iff_center_eq_top K L).mpr hc)
      apply le_antisymm _ bot_le
      intro y hy
      have hc : y ∈ LieAlgebra.center K L := by
        apply (LieModule.mem_maxTrivSubmodule K L L y).mpr
        intro x
        have hm := lie_mem_scalarIdealCore (K := K) I x hy
        rwa [hJ, LieSubmodule.mem_bot] at hm
      rwa [hcenter] at hc
    · right
      apply le_antisymm le_top
      intro x _
      apply scalarIdealCore_mem (K := K) I
      rw [hJ]
      trivial

theorem nonzero_invariant_subalgebra_eq
    (J B : LieSubalgebra κ L) [LieAlgebra.IsSimple κ B]
    (hJB : J ≤ B) (hJ : J ≠ ⊥)
    (hbracket : ∀ x y : L, x ∈ B → y ∈ J → ⁅x, y⁆ ∈ J) : J = B := by
  obtain ⟨I, hI⟩ := (LieSubalgebra.exists_nested_lieIdeal_coe_eq_iff κ J hJB).mpr hbracket
  rcases LieAlgebra.IsSimple.eq_bot_or_eq_top I with hbot | htop
  · exfalso
    apply hJ
    apply le_antisymm _ bot_le
    intro x hx
    let y : B := ⟨x, hJB hx⟩
    have hy : y ∈ I := by
      change y ∈ I.toLieSubalgebra
      rw [hI, LieSubalgebra.mem_ofLe]
      exact hx
    rw [hbot, LieSubmodule.mem_bot] at hy
    exact congrArg Subtype.val hy
  · apply le_antisymm hJB
    intro x hx
    let y : B := ⟨x, hx⟩
    have hy : y ∈ I := by rw [htop]; trivial
    change y ∈ I.toLieSubalgebra at hy
    rw [hI, LieSubalgebra.mem_ofLe] at hy
    exact hy

end

end OAI.NumberTheory.Quaternion.Arithmetic.LieScalarSimplicity
