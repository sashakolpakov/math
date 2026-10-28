import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.AdelicContainment

/-! # Neighborhood Depth -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.PEL.NeighborhoodDepth.Approximation

noncomputable section

/-! Original PEL principal levels form an identity-neighborhood basis.
This is the same matrix-column argument as the open-subgroup containment
lemma, stated for an arbitrary identity neighborhood. -/

open scoped Classical _root_.Topology

open OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.AdelicContainment

variable {E : Type*} [Field E] [NumberField E] [Algebra ℚ E]
  [NumberField.IsCMField E] {s : ℕ} (P : AbelianModuli.ReferenceFamily.Datum.RankThreePELDatum E s)

theorem pel_principal_neighborhood_depth
    (hfg : P.lattice.FG)
    (hspan : Submodule.span ℚ (P.lattice : Set (NumberTheory.ArithmeticGroups.Data.CongruenceLevel.VE E)) = ⊤)
    (H : Set P.FiniteSpecialUnitary) (hH : H ∈ 𝓝 (1 : P.FiniteSpecialUnitary)) :
    ∃ D : ℕ, 0 < D ∧ ∀ N : ℕ, D ∣ N →
      (P.adelicPrincipalLevel N : Set P.FiniteSpecialUnitary) ⊆ H := by
  rw [(AbelianModuli.ReferenceFamily.AdelicContainment.finiteGroupMatrixCoordinates_inducing P).nhds_eq_comap] at hH
  obtain ⟨U, hU, hUH⟩ := Filter.mem_comap.mp hH
  let ψ : (Fin 3 → NumberTheory.ArithmeticGroups.Data.CongruenceLevel.VE (AbelianModuli.ReferenceFamily.AdelicData.FiniteCoefficients E)) →
      (Fin 3 → Fin 3 → AbelianModuli.ReferenceFamily.AdelicData.FiniteCoefficients E) :=
    fun c i j => (Pi.single j (1 : AbelianModuli.ReferenceFamily.AdelicData.FiniteCoefficients E) : Fin 3 → AbelianModuli.ReferenceFamily.AdelicData.FiniteCoefficients E) i + c j i
  have hψ : Continuous ψ := by
    apply continuous_pi
    intro i
    apply continuous_pi
    intro j
    exact continuous_const.add ((continuous_apply i).comp (continuous_apply j))
  have hψ0 : ψ 0 = AbelianModuli.ReferenceFamily.AdelicContainment.finiteGroupMatrixCoordinates P 1 := by
    funext i j
    exact add_zero _
  have hpre : ψ ⁻¹' U ∈ 𝓝 (0 : Fin 3 → NumberTheory.ArithmeticGroups.Data.CongruenceLevel.VE (AbelianModuli.ReferenceFamily.AdelicData.FiniteCoefficients E)) :=
    hψ.continuousAt.preimage_mem_nhds (hψ0.symm ▸ hU)
  rw [nhds_pi] at hpre
  obtain ⟨J, W, hW, hsub⟩ := Filter.mem_pi'.mp hpre
  choose n hn hsmall using fun j =>
    AbelianModuli.ReferenceFamily.AdelicLatticeNeighborhoods.completed_lattice_integer_multiple_small P.completedLattice (AbelianModuli.ReferenceFamily.Lattice.completedLattice_fg P hfg) (W j) (hW j)
  let m := ∏ j : Fin 3, n j
  have hm : m ≠ 0 := Finset.prod_ne_zero_iff.mpr (fun j _ => hn j)
  obtain ⟨d, hd, hb⟩ := AbelianModuli.ReferenceFamily.Lattice.integer_multiple_standard_basis_in_completedLattice P hspan
  refine ⟨(d * m).natAbs, Int.natAbs_pos.mpr (mul_ne_zero hd hm), ?_⟩
  intro N hN g hg
  have hdiv : d * m ∣ (N : ℤ) := Int.natAbs_dvd_natAbs.mp (by
    simpa only [Int.natAbs_natCast] using hN)
  obtain ⟨k, hk⟩ := hdiv
  have hcol : (fun j => g.val (Pi.single j 1) - Pi.single j 1) ∈
      Set.pi (J : Set (Fin 3)) W := by
    intro j _
    obtain ⟨y, hy, he⟩ := AbelianModuli.ReferenceFamily.AdelicContainment.adelic_basis_difference P d m k hd hb N hk g hg j
    change g.val (Pi.single j 1) - Pi.single j 1 ∈ W j
    rw [he]
    obtain ⟨c, hc⟩ := Finset.dvd_prod_of_mem n (Finset.mem_univ j)
    rw [show m = n j * c from hc, mul_smul]
    exact hsmall j (c • y) (P.completedLattice.toAddSubgroup.zsmul_mem hy c)
  apply hUH
  have he : ψ (fun j => g.val (Pi.single j 1) - Pi.single j 1) = AbelianModuli.ReferenceFamily.AdelicContainment.finiteGroupMatrixCoordinates P g := by
    funext i j
    change (Pi.single j 1 : Fin 3 → AbelianModuli.ReferenceFamily.AdelicData.FiniteCoefficients E) i +
      (g.val (Pi.single j 1) i - (Pi.single j 1 : Fin 3 → AbelianModuli.ReferenceFamily.AdelicData.FiniteCoefficients E) i) = _
    abel
  have hmem : ψ (fun j => g.val (Pi.single j 1) - Pi.single j 1) ∈ U := hsub hcol
  change AbelianModuli.ReferenceFamily.AdelicContainment.finiteGroupMatrixCoordinates P g ∈ U
  exact he ▸ hmem

end

end OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.PEL.NeighborhoodDepth.Approximation
