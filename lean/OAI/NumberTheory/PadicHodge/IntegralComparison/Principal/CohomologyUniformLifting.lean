import OAI.NumberTheory.PadicHodge.GeometricComparison.CochainQuotientCohomology

/-! # Cohomology Uniform Lifting -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Principal.CohomologyUniformLifting

noncomputable section

/-! A single power of the coefficient makes every finite-level
cohomology class lift whenever the next integral cohomology is Noetherian. -/

open _root_.CategoryTheory

universe u v
variable (R : Type u) [CommRing R]
  (C : CochainComplex (ModuleCat.{v} R) ℕ) (r : R)
  (hreg : ∀ a, IsSMulRegular (C.X a) r) (i : ℕ)
  [IsNoetherian R (C.homology (i+1))]

include hreg in
theorem exists_power : ∃ c : ℕ, ∀ (n : ℕ)
    (x : (GeometricComparison.PrincipalCochainExact.PrincipalCochainQuotient.quotient R C r n).homology i),
    ∃ y : C.homology i,
      GeometricComparison.CochainQuotientCohomology.PrincipalCochainQuotient.reduction R C r n i y = r^c • x := by
  obtain ⟨c, hc⟩ := GeometricComparison.Finite.PowerTorsion.FinitePowerTorsion.bounded (M := C.homology (i+1)) r
  refine ⟨c, fun n x => ?_⟩
  have hz : r^c • x ∈ (GeometricComparison.PrincipalCochainExact.PrincipalCochainQuotient.connecting R C r hreg n i).ker := by
    change GeometricComparison.PrincipalCochainExact.PrincipalCochainQuotient.connecting R C r hreg n i (r^c • x) = 0
    rw [map_smul]
    exact hc _ ⟨n, GeometricComparison.PrincipalCochainExact.PrincipalCochainQuotient.connecting_torsion R C r hreg n i x⟩
  rw [GeometricComparison.CochainQuotientCohomology.PrincipalCochainQuotient.connecting_ker R C r hreg n i] at hz
  obtain ⟨y, hy⟩ := hz
  obtain ⟨z, rfl⟩ := (PowerModuleSequence.submodule R (C.homology i) r n).mkQ_surjective y
  exact ⟨z, hy⟩

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Principal.CohomologyUniformLifting
