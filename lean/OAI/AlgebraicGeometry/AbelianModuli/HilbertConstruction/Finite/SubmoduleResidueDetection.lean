import OAI.AlgebraicGeometry.HilbertScheme.Presentations.ResidueFieldDetection
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Coordinate.GenerationBaseChange
import OAI.AlgebraicGeometry.HilbertScheme.Presentations.Coordinate.GrassmannianBaseChange
import Mathlib.RingTheory.Flat.Equalizer

/-! # Submodule Residue Detection -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Finite.SubmoduleResidueDetection

noncomputable section

/-! Finite relation modules and their generation are detected by residue-field fibers over arbitrary coefficient rings. -/

open TensorProduct OAI.AlgebraicGeometry.HilbertScheme.Presentations.Coordinate.GrassmannianBaseChange.Grassmannian

universe u v

theorem finite_submodule_eq_of_residue_baseChange {R : Type u} [CommRing R]
    {M : Type v} [AddCommGroup M] [Module R M]
    (p q : Submodule R M) (hpq : p ≤ q) [Module.Finite R q] [Module.Flat R (M ⧸ q)]
    (h : ∀ r : PrimeSpectrum R, p.baseChange r.asIdeal.ResidueField = q.baseChange r.asIdeal.ResidueField) :
    p = q := by
  have hsurj : Function.Surjective (Submodule.inclusion hpq) := by
    apply HilbertScheme.Presentations.ResidueFieldDetection.surjective_of_residueFields_of_finite_cokernel R (Submodule.inclusion hpq)
    intro r y
    let K := r.asIdeal.ResidueField
    have hy : q.subtype.lTensor K y ∈ p.baseChange K := by
      rw [h r]
      exact (q.toBaseChange K y).property
    obtain ⟨x, hx⟩ := p.toBaseChange_surjective' K hy
    refine ⟨x, ?_⟩
    apply LinearMap.lTensor_injective_of_exact_of_flat q.mkQ q.mkQ_surjective q.subtype
      q.subtype_injective (LinearMap.exact_subtype_mkQ q) K
    have he : q.subtype.comp (Submodule.inclusion hpq) = p.subtype := rfl
    rw [← LinearMap.lTensor_comp_apply, he]
    exact hx
  apply le_antisymm hpq
  intro x hx
  obtain ⟨y, hy⟩ := hsurj ⟨x, hx⟩
  have he : y.val = x := congrArg Subtype.val hy
  exact he ▸ y.property

variable {R : Type u} [CommRing R] {ν μ α : Type u}
variable [Fintype ν] [Fintype μ] [DecidableEq ν] [DecidableEq μ]

theorem coordinate_generation_of_residueFields (N : Submodule R (ν → R))
    (K : Submodule R (μ → R)) [Module.Finite R K] [Module.Flat R ((μ → R) ⧸ K)]
    (F : α → Matrix μ ν R) (hF : ∀ i, N ≤ K.comap (Matrix.toLin' (F i)))
    (h : ∀ p : PrimeSpectrum R, HilbertScheme.Presentations.Normalized.KernelBaseChange.Grassmannian.coordinateSubmoduleExtension (algebraMap R p.asIdeal.ResidueField) K =
      ⨆ i, (HilbertScheme.Presentations.Normalized.KernelBaseChange.Grassmannian.coordinateSubmoduleExtension (algebraMap R p.asIdeal.ResidueField) N).map
        (Matrix.toLin' ((F i).map (algebraMap R p.asIdeal.ResidueField)))) :
    K = ⨆ i, N.map (Matrix.toLin' (F i)) := by
  symm
  apply finite_submodule_eq_of_residue_baseChange _ K
    (iSup_le (fun i => Submodule.map_le_iff_le_comap.mpr (hF i)))
  intro p
  apply Submodule.map_injective_of_injective
    (TensorProduct.piScalarRight R p.asIdeal.ResidueField p.asIdeal.ResidueField μ).injective
  rw [← HilbertScheme.Presentations.Coordinate.GrassmannianBaseChange.Grassmannian.coordinateSubmoduleExtension_eq_baseChange, ← HilbertScheme.Presentations.Coordinate.GrassmannianBaseChange.Grassmannian.coordinateSubmoduleExtension_eq_baseChange,
    Coordinate.GenerationBaseChange.coordinateSubmoduleExtension_iSup]
  simp_rw [Coordinate.GenerationBaseChange.coordinateSubmoduleExtension_linearImage]
  exact (h p).symm

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Finite.SubmoduleResidueDetection
