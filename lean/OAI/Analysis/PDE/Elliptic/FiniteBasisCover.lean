import OAI.Analysis.PDE.Elliptic.FrameDecomposition
import Mathlib.Analysis.InnerProductSpace.Spectrum

open Set InnerProductSpace
noncomputable section
namespace OAI.Analysis.PDE.Elliptic

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

def frameNeighborhood (b : OrthonormalBasis (Fin (Module.finrank ℝ E)) ℝ E)
    (eps : ℝ) : Set (E →L[ℝ] E) :=
  {A | ∀ i j, i ≠ j → |inner ℝ (b i) (A (b j))| < eps}

omit [FiniteDimensional ℝ E] in
theorem isOpen_frameNeighborhood (b : OrthonormalBasis (Fin (Module.finrank ℝ E)) ℝ E)
    (eps : ℝ) : IsOpen (frameNeighborhood b eps) := by
  have heq : frameNeighborhood b eps =
      ⋂ i, ⋂ j, {A : E →L[ℝ] E | i ≠ j → |inner ℝ (b i) (A (b j))| < eps} := by
    ext A
    simp [frameNeighborhood]
  rw [heq]
  apply isOpen_iInter_of_finite
  intro i
  apply isOpen_iInter_of_finite
  intro j
  by_cases hij : i = j
  · simp [hij]
  · have hc : Continuous (fun A : E →L[ℝ] E ↦ inner ℝ (b i) (A (b j))) :=
      continuous_const.inner (continuous_id.clm_apply continuous_const)
    simpa only [ne_eq, hij, not_false_eq_true, true_implies] using
      isOpen_lt hc.abs (continuous_const : Continuous (fun _ : E →L[ℝ] E ↦ eps))

theorem exists_frameNeighborhood (A : E →L[ℝ] E) (hA : A.toLinearMap.IsSymmetric)
    {eps : ℝ} (heps : 0 < eps) :
    ∃ b : OrthonormalBasis (Fin (Module.finrank ℝ E)) ℝ E, A ∈ frameNeighborhood b eps := by
  let b := hA.eigenvectorBasis rfl
  refine ⟨b, ?_⟩
  intro i j hij
  change |inner ℝ (b i) (A.toLinearMap (b j))| < eps
  have he : A.toLinearMap (b j) = (hA.eigenvalues rfl j : ℝ) • b j :=
    hA.apply_eigenvectorBasis rfl j
  rw [he, inner_smul_right, b.orthonormal.inner_eq_zero hij, mul_zero, abs_zero]
  exact heps

/-- Compact families of symmetric operators admit finitely many fixed
orthonormal bases in which all off-diagonal entries are uniformly small. -/
theorem finite_basis_cover {K : Set (E →L[ℝ] E)} (hK : IsCompact K)
    (hself : ∀ A ∈ K, A.toLinearMap.IsSymmetric) {eps : ℝ} (heps : 0 < eps) :
    ∃ bs : Finset (OrthonormalBasis (Fin (Module.finrank ℝ E)) ℝ E),
      ∀ A ∈ K, ∃ b ∈ bs, A ∈ frameNeighborhood b eps := by
  classical
  obtain ⟨bs, hbs⟩ := hK.elim_finite_subcover (fun b ↦ frameNeighborhood b eps)
    (fun b ↦ isOpen_frameNeighborhood b eps) (by
      intro A hAK
      obtain ⟨b, hb⟩ := exists_frameNeighborhood A (hself A hAK) heps
      exact mem_iUnion.mpr ⟨b, hb⟩)
  refine ⟨bs, ?_⟩
  intro A hAK
  obtain ⟨b, hb⟩ := mem_iUnion.mp (hbs hAK)
  obtain ⟨hb, hAb⟩ := mem_iUnion.mp hb
  exact ⟨b, hb, hAb⟩

end OAI.Analysis.PDE.Elliptic
