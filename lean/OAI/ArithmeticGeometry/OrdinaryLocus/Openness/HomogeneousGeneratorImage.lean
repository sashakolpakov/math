import OAI.ArithmeticGeometry.OrdinaryLocus.Openness.HomogeneousFilteredImage
import OAI.ArithmeticGeometry.OrdinaryLocus.Openness.FilteredModuleFg

/-! # Homogeneous Generator Image -/

namespace OAI.ArithmeticGeometry.OrdinaryLocus.Openness.HomogeneousGeneratorImage.Construction

noncomputable section

section

/-! A homogeneous polynomial column has the expected filtered-module image. -/

open _root_.MvPolynomial

variable {K B σ M : Type*} [Field K] [CommRing B] [Algebra K B]
    [AddCommGroup M] [Module K M] [Module B M] [IsScalarTower K B M]

theorem homogeneous_generator_range (v : σ → B) (j : σ) (hj : v j = 1)
    (n : ℕ) (w : M) (f : homogeneousSubmodule σ K n →ₗ[K] M)
    (hf : ∀ p : homogeneousSubmodule σ K n, f p = aeval v p.val • w) :
    f.range = FilteredModuleFg.Construction.polynomialFilteredModule v (Submodule.span K {w}) n := by
  apply le_antisymm
  · rintro _ ⟨p, rfl⟩
    rw [hf]
    apply Submodule.smul_mem_smul
    · exact (PolynomialFilteredAlgebra.Construction.mem_polynomialFilteredPiece v n _).mpr
        ⟨p.val, ((mem_homogeneousSubmodule _ _).mp p.property).totalDegree_le, rfl⟩
    · exact Submodule.subset_span (Set.mem_singleton w)
  · apply Submodule.smul_le.mpr
    intro a ha x hx
    have ha' : a ∈ (homogeneousSubmodule σ K n).map (aeval v).toLinearMap := by
      rw [HomogeneousFilteredImage.Construction.homogeneous_image_eq_polynomialFilteredPiece v j hj n]
      exact ha
    obtain ⟨p, hp, hpa⟩ := ha'
    obtain ⟨r, rfl⟩ := Submodule.mem_span_singleton.mp hx
    have hmem : a • w ∈ f.range := ⟨⟨p, hp⟩, (hf ⟨p, hp⟩).trans
      (congrArg (fun b => b • w) hpa)⟩
    have hcomm : a • (r • w) = r • (a • w) := by
      rw [← IsScalarTower.algebraMap_smul B r w, smul_smul,
        mul_comm a, ← smul_smul, IsScalarTower.algebraMap_smul]
    rw [hcomm]
    exact f.range.smul_mem r hmem

end

/-! Fixed shifts on finitely many generators change the module filtration by one bounded shift. -/

variable {K B σ M ι : Type*} [Field K] [CommRing B] [Algebra K B]
    [AddCommGroup M] [Module K M] [Module B M] [IsScalarTower K B M]

theorem polynomialFilteredModule_span_range (v : σ → B) (w : ι → M) (n : ℕ) :
    FilteredModuleFg.Construction.polynomialFilteredModule v (Submodule.span K (Set.range w)) n =
      ⨆ i, FilteredModuleFg.Construction.polynomialFilteredModule v (Submodule.span K {w i}) n := by
  unfold FilteredModuleFg.Construction.polynomialFilteredModule
  rw [Submodule.span_range_eq_iSup, Submodule.smul_iSup]

def weightedPolynomialModulePiece (v : σ → B) (w : ι → M) (d : ι → ℕ) (n : ℕ) : Submodule K M :=
  ⨆ i, FilteredModuleFg.Construction.polynomialFilteredModule v (Submodule.span K {w i}) (n - d i)

theorem weightedPolynomialModulePiece_le (v : σ → B) (w : ι → M) (d : ι → ℕ) (n : ℕ) :
    weightedPolynomialModulePiece v w d n ≤ FilteredModuleFg.Construction.polynomialFilteredModule v (Submodule.span K (Set.range w)) n := by
  rw [polynomialFilteredModule_span_range]
  apply iSup_mono
  intro i
  exact FilteredModuleFg.Construction.polynomialFilteredModule_mono v _ (Nat.sub_le n (d i))

theorem polynomialFilteredModule_le_weighted_shift (v : σ → B) (w : ι → M)
    (d : ι → ℕ) (c : ℕ) (hc : ∀ i, d i ≤ c) (n : ℕ) :
    FilteredModuleFg.Construction.polynomialFilteredModule v (Submodule.span K (Set.range w)) n ≤
      weightedPolynomialModulePiece v w d (n + c) := by
  rw [polynomialFilteredModule_span_range]
  apply iSup_mono
  intro i
  apply FilteredModuleFg.Construction.polynomialFilteredModule_mono
  have hi := hc i
  omega

theorem weightedPolynomialModulePiece_comparable [Fintype ι]
    (v : σ → B) (w : ι → M) (d : ι → ℕ) :
    ∃ c : ℕ, (∀ n, FilteredModuleFg.Construction.polynomialFilteredModule v (Submodule.span K (Set.range w)) n ≤
      weightedPolynomialModulePiece v w d (n + c)) ∧
      (∀ n, weightedPolynomialModulePiece v w d n ≤
        FilteredModuleFg.Construction.polynomialFilteredModule v (Submodule.span K (Set.range w)) n) := by
  classical
  exact ⟨Finset.univ.sup d,
    polynomialFilteredModule_le_weighted_shift v w d _
      (fun i => Finset.le_sup (f := d) (Finset.mem_univ i)),
    weightedPolynomialModulePiece_le v w d⟩

end

end OAI.ArithmeticGeometry.OrdinaryLocus.Openness.HomogeneousGeneratorImage.Construction
