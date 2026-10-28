import OAI.NumberTheory.ArithmeticGroups.Lattices.StandardSiegelMatrix
import OAI.NumberTheory.ArithmeticGroups.Lattices.LatticeFrameAction

/-! # Standard Siegel Representatives -/

namespace OAI.NumberTheory.ArithmeticGroups.Lattices.StandardSiegelRepresentatives.Construction

noncomputable section

/-! Every invertible real matrix has an integral lattice change of
basis placing it in the fixed standard Siegel matrix region. -/

open _root_.Module
open scoped Classical

theorem standard_siegel_lattice_representatives
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    {n : ℕ} (Λ : Submodule ℤ E) [DiscreteTopology Λ] [IsZLattice ℝ Λ]
    (b : Basis (Fin n) ℤ Λ) (b₀ : OrthonormalBasis (Fin n) ℝ E)
    (hb : ∀ i, (b i).val = b₀ i) (g : Matrix.GeneralLinearGroup (Fin n) ℝ) :
    ∃ γ ∈ SubmoduleOrbit.Construction.submoduleImageStabilizer (LatticeFrameAction.Construction.matrixFrameIntegralAction b₀.toBasis) Λ,
      StandardSiegelMatrix.Construction.IsStandardSiegelMatrix (g * γ).val := by
  let ρ := LatticeFrameAction.Construction.matrixFrameIntegralAction b₀.toBasis
  let e := (LatticeFrameAction.Construction.matrixFrameAction b₀.toBasis g).toContinuousLinearEquiv
  let Ω := ZLattice.comap ℝ Λ e.symm.toLinearMap
  have hdim : finrank ℝ E = n := by simpa using Module.finrank_eq_card_basis b₀.toBasis
  obtain ⟨d⟩ := ReducedLatticeBasisExistence.Construction.exists_reduced_lattice_basis n Ω hdim (IsZLattice.span_top (K := ℝ) (L := Ω))
  let B := d.latticeBasis
  let Bℝ := B.ofZLatticeBasis ℝ
  have hframe : LinearIndependent ℝ (fun i => (B i).val) ∧
      Submodule.span ℝ (Set.range (fun i => (B i).val)) = ⊤ := by
    have he : (fun i => (B i).val) = Bℝ := funext (fun i => (B.ofZLatticeBasis_apply ℝ Ω i).symm)
    rw [he]
    exact ⟨Bℝ.linearIndependent, Bℝ.span_eq⟩
  let M := FrameMatrices.Construction.matrixOfFrame b₀.toBasis (fun i => (B i).val) hframe
  have hMact (i : Fin n) : LatticeFrameAction.Construction.matrixFrameAction b₀.toBasis M (b i).val = (B i).val := by
    rw [hb]
    exact LatticeFrameAction.Construction.matrixFrameAction_ofFrame b₀.toBasis _ hframe i
  have hMmap : Λ.map (ρ M).toLinearMap = Ω :=
    LatticeFrameAction.Construction.map_lattice_of_basis_images Λ Ω b B (LatticeFrameAction.Construction.matrixFrameAction b₀.toBasis M).toLinearMap hMact
  have hgmap : Λ.map (ρ g).toLinearMap = Ω := by
    ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      change e.symm (e x) ∈ Λ
      rw [e.symm_apply_apply]
      exact hx
    · intro hy
      exact ⟨e.symm y, hy, e.apply_symm_apply y⟩
  have hgcomp : (ρ g⁻¹).toLinearMap.comp (ρ g).toLinearMap = LinearMap.id := by
    rw [map_inv]
    ext x
    exact (ρ g).symm_apply_apply x
  have hinvmap : Ω.map (ρ g⁻¹).toLinearMap = Λ := by
    rw [← hgmap, ← Submodule.map_comp, hgcomp, Submodule.map_id]
  refine ⟨g⁻¹ * M, ?_, ?_⟩
  · change Λ.map (ρ (g⁻¹ * M)).toLinearMap = Λ
    rw [map_mul]
    change Λ.map ((ρ g⁻¹).toLinearMap.comp (ρ M).toLinearMap) = Λ
    rw [Submodule.map_comp, hMmap, hinvmap]
  · rw [← mul_assoc, mul_inv_cancel, one_mul]
    exact d.isStandardSiegelMatrix b₀

end

end OAI.NumberTheory.ArithmeticGroups.Lattices.StandardSiegelRepresentatives.Construction
