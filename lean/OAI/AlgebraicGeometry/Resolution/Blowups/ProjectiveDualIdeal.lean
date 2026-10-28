import Mathlib.RingTheory.Finiteness.Projective
import Mathlib.LinearAlgebra.Pi
import Mathlib.RingTheory.Ideal.Maps

/-! # Projective Dual Ideal -/

namespace OAI.AlgebraicGeometry.Resolution.Blowups.ProjectiveDualIdeal.Construction

noncomputable section

/-! Ideal membership detected by the dual of a finite projective module. -/

variable {R S M : Type*} [CommRing R] [CommRing S] [Algebra R S]
  [AddCommGroup M] [Module R M] [Module.Finite R M] [Module.Projective R M]

/-- If every base-valued linear functional takes a module element into an
ideal, every scalar-extended linear functional takes it into the extended ideal. -/
theorem projective_linearMap_mem_ideal_map (I : Ideal R) (x : M)
    (hx : ∀ l : M →ₗ[R] R, l x ∈ I) (F : M →ₗ[R] S) :
    F x ∈ I.map (algebraMap R S) := by
  classical
  obtain ⟨n, f, g, _, _, hfg⟩ := Module.Finite.exists_comp_eq_id_of_projective R M
  have hfx : f (g x) = x := LinearMap.congr_fun hfg x
  rw [← hfx, ← Finset.univ_sum_single (g x), map_sum, map_sum]
  apply Submodule.sum_mem
  intro i _
  have hcoord : g x i ∈ I := hx ((LinearMap.proj i).comp g)
  have hsingle : Pi.single i (g x i) = (g x i) • Pi.single i (1 : R) := by
    ext j
    by_cases hij : i = j
    · subst j
      simp
    · simp [Ne.symm hij]
  rw [hsingle, map_smul, map_smul, Algebra.smul_def]
  exact Ideal.mul_mem_right _ _ (Ideal.mem_map_of_mem _ hcoord)

end

end OAI.AlgebraicGeometry.Resolution.Blowups.ProjectiveDualIdeal.Construction
