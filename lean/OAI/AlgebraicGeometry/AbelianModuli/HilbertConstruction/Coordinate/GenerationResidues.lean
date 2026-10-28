import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Finite.SubmoduleResidueDetection
import Mathlib.Algebra.Module.FinitePresentation

/-! # Generation Residues -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Coordinate.GenerationResidues

noncomputable section

/-! Residue-field generation tests are equivalent to actual finite coordinate relation generation. -/

universe u

theorem coordinateRelations_finite {R : Type u} [CommRing R] {μ : Type u} [Fintype μ]
    (K : Submodule R (μ → R)) [Module.Projective R ((μ → R) ⧸ K)] : Module.Finite R K := by
  have : Module.FinitePresentation R ((μ → R) ⧸ K) := Module.finitePresentation_of_projective _ _
  have h := Module.FinitePresentation.fg_ker K.mkQ K.mkQ_surjective
  rw [Submodule.ker_mkQ] at h
  exact Module.Finite.of_fg h

variable {R A : Type u} [CommRing R] [CommRing A] {ν μ α : Type u}
variable [Fintype ν] [DecidableEq ν]

theorem coordinate_generation_baseChange (φ : R →+* A)
    (N : Submodule R (ν → R)) (K : Submodule R (μ → R)) (F : α → Matrix μ ν R)
    (h : K = ⨆ t, N.map (Matrix.toLin' (F t))) :
    HilbertScheme.Presentations.Normalized.KernelBaseChange.Grassmannian.coordinateSubmoduleExtension φ K =
      ⨆ t, (HilbertScheme.Presentations.Normalized.KernelBaseChange.Grassmannian.coordinateSubmoduleExtension φ N).map (Matrix.toLin' ((F t).map φ)) := by
  rw [h, GenerationBaseChange.coordinateSubmoduleExtension_iSup]
  exact congrArg iSup (funext (fun t => GenerationBaseChange.coordinateSubmoduleExtension_linearImage φ N (F t)))

variable [Fintype μ] [DecidableEq μ]

theorem coordinate_generation_iff_residueFields (N : Submodule R (ν → R))
    (K : Submodule R (μ → R)) [Module.Projective R ((μ → R) ⧸ K)]
    (F : α → Matrix μ ν R) (hF : ∀ t, N ≤ K.comap (Matrix.toLin' (F t))) :
    K = ⨆ t, N.map (Matrix.toLin' (F t)) ↔
      ∀ p : PrimeSpectrum R, HilbertScheme.Presentations.Normalized.KernelBaseChange.Grassmannian.coordinateSubmoduleExtension (algebraMap R p.asIdeal.ResidueField) K =
        ⨆ t, (HilbertScheme.Presentations.Normalized.KernelBaseChange.Grassmannian.coordinateSubmoduleExtension (algebraMap R p.asIdeal.ResidueField) N).map
          (Matrix.toLin' ((F t).map (algebraMap R p.asIdeal.ResidueField))) := by
  have : Module.Finite R K := coordinateRelations_finite K
  constructor
  · intro h p
    exact coordinate_generation_baseChange _ N K F h
  · exact HilbertConstruction.Finite.SubmoduleResidueDetection.coordinate_generation_of_residueFields N K F hF

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Coordinate.GenerationResidues
