import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Matrix.SurjectivityBaseChange
import OAI.AlgebraicGeometry.HilbertScheme.Presentations.Local.MatrixMinors
import OAI.AlgebraicGeometry.HilbertScheme.Presentations.Normalized.Quotients

/-! # Surjectivity Minors -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Matrix.SurjectivityMinors

noncomputable section

/-! Matrix surjectivity is equivalent to maximal minors generating the unit ideal locally at every prime. -/

universe u

variable {R : Type u} [CommRing R]
variable {ι ν : Type u} [Fintype ι] [Fintype ν] [DecidableEq ι] [DecidableEq ν]

theorem matrix_surjective_of_unit_minor (F : Matrix ι ν R) (a : ι → ν)
    (h : IsUnit (F.submatrix id a).det) : Function.Surjective (Matrix.toLin' F) := by
  have hs : Function.Surjective (Matrix.toLin' (HilbertScheme.Presentations.Normalized.Matrices.Grassmannian.selectedColumns a F)) :=
    Matrix.mulVec_surjective_iff_isUnit.mpr ((HilbertScheme.Presentations.Normalized.Matrices.Grassmannian.selectedColumns a F).isUnit_iff_isUnit_det.mpr h)
  intro y
  obtain ⟨x, hx⟩ := hs y
  refine ⟨HilbertScheme.Presentations.Normalized.Quotients.Grassmannian.selectedBasisMap a x, ?_⟩
  exact (LinearMap.congr_fun (HilbertScheme.Presentations.Normalized.Quotients.Grassmannian.matrix_comp_selectedBasisMap a F) x).trans hx

theorem matrix_surjective_iff_prime_minors (F : Matrix ι ν R) :
    Function.Surjective (Matrix.toLin' F) ↔
      ∀ p : PrimeSpectrum R, ∃ a : ι → ν, (F.submatrix id a).det ∉ p.asIdeal := by
  constructor
  · intro h p
    let K := p.asIdeal.ResidueField
    let φ := algebraMap R K
    obtain ⟨a, _, ha⟩ := HilbertScheme.Presentations.Local.MatrixMinors.Grassmannian.local_surjective_matrix_unit_minor (F.map φ)
      (SurjectivityBaseChange.matrix_surjective_baseChange φ F h)
    refine ⟨a, ?_⟩
    intro hp
    have hz : φ (F.submatrix id a).det = 0 := by
      apply RingHom.mem_ker.mp
      rw [Ideal.ker_algebraMap_residueField]
      exact hp
    have he : φ (F.submatrix id a).det = ((F.map φ).submatrix id a).det :=
      φ.map_det (F.submatrix id a)
    exact ha.ne_zero (he.symm.trans hz)
  · intro h
    apply SurjectivityBaseChange.matrix_surjective_of_residueFields F
    intro p
    obtain ⟨a, ha⟩ := h p
    let φ := algebraMap R p.asIdeal.ResidueField
    apply matrix_surjective_of_unit_minor _ a
    apply isUnit_iff_ne_zero.mpr
    intro hz
    apply ha
    have he : φ (F.submatrix id a).det = ((F.map φ).submatrix id a).det :=
      φ.map_det (F.submatrix id a)
    have hk : (F.submatrix id a).det ∈ RingHom.ker φ := RingHom.mem_ker.mpr (he.trans hz)
    rwa [Ideal.ker_algebraMap_residueField] at hk

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Matrix.SurjectivityMinors
