import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.AdelicLatticeNeighborhoods
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Lattice

/-! # Adelic Containment -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.AdelicContainment

noncomputable section

/-! Principal levels of the actual completed lattice eventually lie
inside every open subgroup of the specified finite special-unitary
group, in its prescribed matrix-coordinate topology. -/

open scoped Classical _root_.Topology

variable {E : Type*} [Field E] [NumberField E] [Algebra ℚ E]
  [NumberField.IsCMField E] {s : ℕ} (P : Datum.RankThreePELDatum E s)

theorem adelic_basis_difference (d m k : ℤ) (hd : d ≠ 0)
    (hb : ∀ j : Fin 3, d • (Pi.single j (1 : AdelicData.FiniteCoefficients E)) ∈ P.completedLattice)
    (N : ℕ) (hN : (N : ℤ) = d * m * k)
    (g : P.FiniteSpecialUnitary) (hg : g ∈ P.adelicPrincipalLevel N) (j : Fin 3) :
    ∃ y ∈ P.completedLattice, g.val (Pi.single j 1) - Pi.single j 1 = m • y := by
  obtain ⟨y, hy, he⟩ := hg.2 (d • Pi.single j 1) (hb j)
  change g.val (d • Pi.single j 1) - d • Pi.single j 1 = N • y at he
  have hmap : g.val (d • Pi.single j 1) = d • g.val (Pi.single j 1) :=
    (g.val.toLinearMap.restrictScalars ℤ).map_smul d _
  refine ⟨k • y, P.completedLattice.toAddSubgroup.zsmul_mem hy k, ?_⟩
  apply smul_right_injective (NumberTheory.ArithmeticGroups.Data.CongruenceLevel.VE (AdelicData.FiniteCoefficients E))
    (show (d : ℚ) ≠ 0 from Int.cast_ne_zero.mpr hd)
  simp only [Int.cast_smul_eq_zsmul]
  rw [smul_sub, ← hmap, he, ← natCast_zsmul, hN, mul_smul, mul_smul]

def finiteGroupMatrixCoordinates (g : P.FiniteSpecialUnitary) :
    Fin 3 → Fin 3 → AdelicData.FiniteCoefficients E :=
  fun i j => g.val (Pi.single j 1) i

theorem finiteGroupMatrixCoordinates_inducing :
    Topology.IsInducing (finiteGroupMatrixCoordinates P) := ⟨rfl⟩

theorem exists_adelic_principal_containment_depth
    (hfg : P.lattice.FG)
    (hspan : Submodule.span ℚ (P.lattice : Set (NumberTheory.ArithmeticGroups.Data.CongruenceLevel.VE E)) = ⊤)
    (H : OpenSubgroup P.FiniteSpecialUnitary) :
    ∃ D : ℕ, 0 < D ∧ ∀ N : ℕ, D ∣ N → P.adelicPrincipalLevel N ≤ H.toSubgroup := by
  have hH : (H : Set P.FiniteSpecialUnitary) ∈ 𝓝 (1 : P.FiniteSpecialUnitary) :=
    H.isOpen.mem_nhds H.one_mem
  rw [(finiteGroupMatrixCoordinates_inducing P).nhds_eq_comap] at hH
  obtain ⟨U, hU, hUH⟩ := Filter.mem_comap.mp hH
  let ψ : (Fin 3 → NumberTheory.ArithmeticGroups.Data.CongruenceLevel.VE (AdelicData.FiniteCoefficients E)) →
      (Fin 3 → Fin 3 → AdelicData.FiniteCoefficients E) :=
    fun c i j => (Pi.single j (1 : AdelicData.FiniteCoefficients E) : Fin 3 → AdelicData.FiniteCoefficients E) i + c j i
  have hψ : Continuous ψ := by
    apply continuous_pi
    intro i
    apply continuous_pi
    intro j
    exact continuous_const.add ((continuous_apply i).comp (continuous_apply j))
  have hψ0 : ψ 0 = finiteGroupMatrixCoordinates P 1 := by
    funext i j
    exact add_zero _
  have hpre : ψ ⁻¹' U ∈ 𝓝 (0 : Fin 3 → NumberTheory.ArithmeticGroups.Data.CongruenceLevel.VE (AdelicData.FiniteCoefficients E)) :=
    hψ.continuousAt.preimage_mem_nhds (hψ0.symm ▸ hU)
  rw [nhds_pi] at hpre
  obtain ⟨J, W, hW, hsub⟩ := Filter.mem_pi'.mp hpre
  choose n hn hsmall using fun j =>
    AdelicLatticeNeighborhoods.completed_lattice_integer_multiple_small P.completedLattice (Lattice.completedLattice_fg P hfg) (W j) (hW j)
  let m := ∏ j : Fin 3, n j
  have hm : m ≠ 0 := Finset.prod_ne_zero_iff.mpr (fun j _ => hn j)
  obtain ⟨d, hd, hb⟩ := Lattice.integer_multiple_standard_basis_in_completedLattice P hspan
  refine ⟨(d * m).natAbs, Int.natAbs_pos.mpr (mul_ne_zero hd hm), ?_⟩
  intro N hN g hg
  have hdiv : d * m ∣ (N : ℤ) := Int.natAbs_dvd_natAbs.mp (by
    simpa only [Int.natAbs_natCast] using hN)
  obtain ⟨k, hk⟩ := hdiv
  have hcol : (fun j => g.val (Pi.single j 1) - Pi.single j 1) ∈
      Set.pi (J : Set (Fin 3)) W := by
    intro j _
    obtain ⟨y, hy, he⟩ := adelic_basis_difference P d m k hd hb N hk g hg j
    change g.val (Pi.single j 1) - Pi.single j 1 ∈ W j
    rw [he]
    obtain ⟨c, hc⟩ := Finset.dvd_prod_of_mem n (Finset.mem_univ j)
    rw [show m = n j * c from hc, mul_smul]
    exact hsmall j (c • y) (P.completedLattice.toAddSubgroup.zsmul_mem hy c)
  apply hUH
  have he : ψ (fun j => g.val (Pi.single j 1) - Pi.single j 1) = finiteGroupMatrixCoordinates P g := by
    funext i j
    change (Pi.single j 1 : Fin 3 → AdelicData.FiniteCoefficients E) i +
      (g.val (Pi.single j 1) i - (Pi.single j 1 : Fin 3 → AdelicData.FiniteCoefficients E) i) = _
    abel
  have hmem : ψ (fun j => g.val (Pi.single j 1) - Pi.single j 1) ∈ U := hsub hcol
  change finiteGroupMatrixCoordinates P g ∈ U
  exact he ▸ hmem

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.AdelicContainment
