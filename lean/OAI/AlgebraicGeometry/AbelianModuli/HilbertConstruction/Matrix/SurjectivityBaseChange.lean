import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Coordinate.GenerationBaseChange
import OAI.AlgebraicGeometry.HilbertScheme.Presentations.Coordinate.GrassmannianBaseChange
import OAI.AlgebraicGeometry.HilbertScheme.Presentations.ResidueFieldDetection

/-! # Surjectivity Base Change -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Matrix.SurjectivityBaseChange

noncomputable section

/-! Matrix surjectivity is preserved by coefficient extension and detected by residue-field fibers. -/

open OAI.AlgebraicGeometry.HilbertScheme.Presentations.Coordinate.GrassmannianBaseChange.Grassmannian

universe u

variable {R A : Type u} [CommRing R] [CommRing A]
variable {ι ν : Type u} [Fintype ι] [Fintype ν] [DecidableEq ι] [DecidableEq ν]

theorem coordinateSubmoduleExtension_top (φ : R →+* A) :
    HilbertScheme.Presentations.Normalized.KernelBaseChange.Grassmannian.coordinateSubmoduleExtension (ν := ν) φ ⊤ = ⊤ := by
  apply top_unique
  rw [← (Pi.basisFun A ν).span_eq]
  apply Submodule.span_le.mpr
  rintro _ ⟨i, rfl⟩
  have he : φ ∘ Pi.single i (1 : R) = Pi.single i (1 : A) := by
    ext j
    by_cases h : j = i
    · simp [Function.comp_apply, h]
    · simp [Function.comp_apply, h]
  rw [Pi.basisFun_apply]
  rw [← he]
  exact Submodule.subset_span ⟨Pi.single i (1 : R), Submodule.mem_top, rfl⟩

omit [Fintype ι] [DecidableEq ι] in
theorem coordinateSubmoduleExtension_matrixRange (φ : R →+* A) (F : Matrix ι ν R) :
    HilbertScheme.Presentations.Normalized.KernelBaseChange.Grassmannian.coordinateSubmoduleExtension φ (Matrix.toLin' F).range = (Matrix.toLin' (F.map φ)).range := by
  rw [← Submodule.map_top (Matrix.toLin' F), Coordinate.GenerationBaseChange.coordinateSubmoduleExtension_linearImage,
    coordinateSubmoduleExtension_top, Submodule.map_top]

theorem matrix_surjective_baseChange (φ : R →+* A) (F : Matrix ι ν R)
    (hF : Function.Surjective (Matrix.toLin' F)) : Function.Surjective (Matrix.toLin' (F.map φ)) := by
  apply LinearMap.range_eq_top.mp
  rw [← coordinateSubmoduleExtension_matrixRange, LinearMap.range_eq_top.mpr hF,
    coordinateSubmoduleExtension_top]

theorem matrix_surjective_of_residueFields (F : Matrix ι ν R)
    (hF : ∀ p : PrimeSpectrum R,
      Function.Surjective (Matrix.toLin' (F.map (algebraMap R p.asIdeal.ResidueField)))) :
    Function.Surjective (Matrix.toLin' F) := by
  let N := (Matrix.toLin' F).range
  have hz : Subsingleton ((ι → R) ⧸ N) :=
    HilbertScheme.Presentations.ResidueFieldDetection.finiteModule_subsingleton_of_residueFields R _ (fun p => by
      let e := HilbertScheme.Presentations.Coordinate.GrassmannianBaseChange.Grassmannian.coordinateBaseChangeQuotientEquiv (S := p.asIdeal.ResidueField) N
      have hN : HilbertScheme.Presentations.Normalized.KernelBaseChange.Grassmannian.coordinateSubmoduleExtension (algebraMap R p.asIdeal.ResidueField) N = ⊤ :=
        (coordinateSubmoduleExtension_matrixRange _ F).trans (LinearMap.range_eq_top.mpr (hF p))
      have : Subsingleton ((ι → p.asIdeal.ResidueField) ⧸
          HilbertScheme.Presentations.Normalized.KernelBaseChange.Grassmannian.coordinateSubmoduleExtension (algebraMap R p.asIdeal.ResidueField) N) := by
        rw [hN]
        infer_instance
      exact e.symm.subsingleton)
  let := hz
  intro y
  have hy : N.mkQ y = 0 := Subsingleton.elim _ _
  exact (Submodule.Quotient.mk_eq_zero N).mp hy

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Matrix.SurjectivityBaseChange
