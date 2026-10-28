import OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.DenseScalarCharacter
import Mathlib.LinearAlgebra.GeneralLinearGroup.Basic
import Mathlib.Algebra.Module.Torsion.Field

/-! # Eigenline Character -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.EigenlineCharacter.TestTransport

noncomputable section

/-! An invariant nonzero line gives a scalar character. Density in a
perfect group removes that scalar once an open active level fixes the
same vector exactly. -/

open scoped Classical

variable {Γ K V : Type*} [Group Γ] [Field K] [AddCommGroup V] [Module K V]
  (ρ : Γ →* (V ≃ₗ[K] V)) (v : V) (hv : v ≠ 0)
  (hline : ∀ γ, ∃ c : Kˣ, ρ γ v = (c : K) • v)

def eigenlineScalar (γ : Γ) : Kˣ := (hline γ).choose

theorem eigenlineScalar_spec (γ : Γ) : ρ γ v = (eigenlineScalar ρ v hline γ : K) • v :=
  (hline γ).choose_spec

include hv in
theorem eigenlineScalar_one : eigenlineScalar ρ v hline 1 = 1 := by
  apply Units.ext
  apply (smul_left_injective K hv)
  exact (eigenlineScalar_spec ρ v hline 1).symm.trans (by simp)

include hv in
theorem eigenlineScalar_mul (a b : Γ) :
    eigenlineScalar ρ v hline (a * b) = eigenlineScalar ρ v hline a * eigenlineScalar ρ v hline b := by
  apply Units.ext
  apply (smul_left_injective K hv)
  dsimp only
  rw [Units.val_mul, ← smul_smul, ← eigenlineScalar_spec]
  rw [← eigenlineScalar_spec, map_mul]
  change ρ a (ρ b v) = _
  rw [eigenlineScalar_spec ρ v hline b, map_smul, eigenlineScalar_spec ρ v hline a,
    smul_smul, smul_smul, mul_comm]

def eigenlineCharacter : Γ →* Kˣ where
  toFun := eigenlineScalar ρ v hline
  map_one' := eigenlineScalar_one ρ v hv hline
  map_mul' := eigenlineScalar_mul ρ v hv hline

theorem eigenlineCharacter_spec (γ : Γ) : ρ γ v = (eigenlineCharacter ρ v hv hline γ : K) • v :=
  eigenlineScalar_spec ρ v hline γ

include hv hline in
theorem dense_invariant_line_fixed
    {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    (f : Γ →* G) (hf : DenseRange f) (hperfect : commutator G = ⊤)
    (U : OpenSubgroup G) (hU : ∀ γ, f γ ∈ U → ρ γ v = v) : ∀ γ, ρ γ v = v := by
  have hχ := DenseScalarCharacter.TestTransport.dense_scalar_character_trivial f hf (eigenlineCharacter ρ v hv hline) hperfect U
    (fun γ hγ => by
      apply Units.ext
      apply (smul_left_injective K hv)
      exact (eigenlineCharacter_spec ρ v hv hline γ).symm.trans
        ((hU γ hγ).trans (one_smul K v).symm))
  intro γ
  rw [eigenlineCharacter_spec ρ v hv hline, hχ γ, Units.val_one, one_smul]

end

end OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.EigenlineCharacter.TestTransport
