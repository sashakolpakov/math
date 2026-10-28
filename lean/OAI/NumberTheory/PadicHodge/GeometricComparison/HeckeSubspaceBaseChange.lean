import OAI.NumberTheory.PadicHodge.GeometricComparison.SubspaceBaseI

/-! # Hecke Subspace Base Change -/

namespace OAI.NumberTheory.PadicHodge.GeometricComparison.HeckeSubspaceBaseChange.SubspaceBaseChange

noncomputable section

/-! Generalized Hecke subspaces and all their filtered dimensions commute with field extension. -/

open scoped TensorProduct

variable {K L V I : Type*} [Field K] [Field L] [Algebra K L]
  [AddCommGroup V] [Module K V] [FiniteDimensional K V]

omit [FiniteDimensional K V] in
theorem shifted_power (T : Module.End K V) (μ : K) (n : ℕ) :
    ((T - μ • 1) ^ n).baseChange L =
      (T.baseChange L - algebraMap K L μ • 1) ^ n := by
  change (Module.End.baseChangeHom K L V) ((T - μ • 1) ^ n) = _
  rw [map_pow, map_sub, map_smul, map_one, IsScalarTower.algebraMap_smul]
  rfl

theorem maxGenEigenspace (T : Module.End K V) (μ : K) :
    (T.maxGenEigenspace μ).baseChange L =
      Module.End.maxGenEigenspace (T.baseChange L) (algebraMap K L μ) := by
  rw [Module.End.maxGenEigenspace_eq_genEigenspace_finrank,
    Module.End.maxGenEigenspace_eq_genEigenspace_finrank, Module.finrank_baseChange,
    Module.End.genEigenspace_nat, Module.End.genEigenspace_nat, SubspaceBaseI.SubspaceBaseChange.kernel, shifted_power]

theorem generalizedHeckeSummand (T : I → Module.End K V) (χ : I → K) :
    (Linear.generalizedHeckeSummand T χ).baseChange L =
      Linear.generalizedHeckeSummand (fun i => (T i).baseChange L) (fun i => algebraMap K L (χ i)) := by
  change (⨅ i, (T i).maxGenEigenspace (χ i)).baseChange L = _
  rw [SubspaceBaseI.SubspaceBaseChange.iInf]
  exact iInf_congr (fun i => SubspaceBaseChange.maxGenEigenspace (T i) (χ i))

theorem filtered_finrank (T : I → Module.End K V) (χ : I → K) (F : Submodule K V) :
    Module.finrank L
        (Linear.generalizedHeckeSummand (fun i => (T i).baseChange L) (fun i => algebraMap K L (χ i)) ⊓
          F.baseChange L : Submodule L (L ⊗[K] V)) =
      Module.finrank K (Linear.generalizedHeckeSummand T χ ⊓ F : Submodule K V) := by
  rw [← generalizedHeckeSummand, ← SubspaceBaseI.SubspaceBaseChange.inf, SubspaceBaseI.SubspaceBaseChange.finrank]

end

end OAI.NumberTheory.PadicHodge.GeometricComparison.HeckeSubspaceBaseChange.SubspaceBaseChange
