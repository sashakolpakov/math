import Mathlib.LinearAlgebra.Dimension.Localization
import Mathlib.LinearAlgebra.FreeModule.PID
import Mathlib.RingTheory.TensorProduct.IsBaseChangeHom

/-! # Lattice Subspace Eq -/

namespace OAI.NumberTheory.PadicHodge.GeometricComparison.LatticeSubspaceEq.LatticeSubspace

noncomputable section

/-! Intersections with rational subspaces preserve full lattices and have torsion-free quotients. -/

open scoped nonZeroDivisors

variable {R K M V : Type*} [CommRing R] [IsDomain R] [Field K]
  [Algebra R K] [IsFractionRing R K]
  [AddCommGroup M] [Module R M] [AddCommGroup V] [Module R V]
  [Module K V] [IsScalarTower R K V]

def integralPart (f : M →ₗ[R] V) (S : Submodule K V) : Submodule R M :=
  (S.restrictScalars R).comap f

def inclusion (f : M →ₗ[R] V) (S : Submodule K V) : integralPart f S →ₗ[R] S where
  toFun x := ⟨f x, x.property⟩
  map_add' x y := Subtype.ext (f.map_add x y)
  map_smul' r x := Subtype.ext (f.map_smul r x)

theorem quotient_torsionFree (f : M →ₗ[R] V) (S : Submodule K V) :
    Module.IsTorsionFree R (M ⧸ integralPart f S) := by
  apply Module.IsTorsionFree.of_smul_eq_zero
  intro r x hx
  by_cases hr : r = 0
  · exact Or.inl hr
  right
  obtain ⟨m, rfl⟩ := (integralPart f S).mkQ_surjective x
  apply (Submodule.Quotient.mk_eq_zero (integralPart f S)).mpr
  have hm : r • f m ∈ S := by
    have h := (Submodule.Quotient.mk_eq_zero (integralPart f S)).mp
      (show (integralPart f S).mkQ (r • m) = 0 by simpa only [map_smul] using hx)
    exact (f.map_smul r m) ▸ h
  have hrK : algebraMap R K r ≠ 0 := by
    intro h
    apply hr
    apply IsFractionRing.injective R K
    simpa only [map_zero] using h
  exact (S.smul_mem_iff hrK).mp (by simpa only [IsScalarTower.algebraMap_smul] using hm)

instance localized (f : M →ₗ[R] V) [IsLocalizedModule R⁰ f] (S : Submodule K V) :
    IsLocalizedModule R⁰ (inclusion f S) where
  map_units s := (isLocalizedModule_id R⁰ S K).map_units s
  surj x := by
    obtain ⟨⟨m, s⟩, hs⟩ := IsLocalizedModule.surj R⁰ f (x : V)
    have hm : m ∈ integralPart f S := by
      change f m ∈ S
      rw [← hs]
      exact (S.restrictScalars R).smul_mem (s : R) x.property
    exact ⟨(⟨m, hm⟩, s), Subtype.ext hs⟩
  exists_of_eq h := by
    obtain ⟨s, hs⟩ := IsLocalizedModule.exists_of_eq (S := R⁰) (f := f)
      (congrArg Subtype.val h)
    exact ⟨s, Subtype.ext hs⟩

omit [IsDomain R] in
theorem finrank_eq (f : M →ₗ[R] V) [IsLocalizedModule R⁰ f] (S : Submodule K V) :
    Module.finrank R (integralPart f S) = Module.finrank K S := by
  rw [IsFractionRing.finrank_right_eq R K S]
  exact (IsLocalizedModule.finrank_eq R⁰ (inclusion f S) le_rfl).symm

end

end OAI.NumberTheory.PadicHodge.GeometricComparison.LatticeSubspaceEq.LatticeSubspace
