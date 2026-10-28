import OAI.RepresentationTheory.Weil.AdelicSplitting.RealCharacters

/-! # Lattice Dual Coordinates -/

namespace OAI.RepresentationTheory.Weil.AdelicSplitting.LatticeDualCoordinates.LocalAnalysis

noncomputable section

section

/-! Explicit linear coordinates for a nondegenerate real bilinear pairing.
The dual coordinates evaluate the pairing against the lattice basis. -/

open scoped Classical

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {ι : Type*} [Fintype ι] (b : Module.Basis ι ℝ E)
  (B : LinearMap.BilinForm ℝ E)

def latticeDualMap : E →ₗ[ℝ] (ι → ℝ) :=
  LinearMap.pi (fun i => B.flip (b i))

theorem latticeDualMap_injective (hB : B.SeparatingLeft) :
    Function.Injective (latticeDualMap b B) := by
  intro x y h
  apply sub_eq_zero.mp
  apply hB
  intro z
  rw [← b.sum_repr z, map_sum]
  apply Finset.sum_eq_zero
  intro i _
  have hi : B (x - y) (b i) = 0 := by
    rw [map_sub, LinearMap.sub_apply]
    exact sub_eq_zero.mpr (congrFun h i)
  rw [map_smul, hi, smul_zero]

def latticeDualCoordinates (hB : B.SeparatingLeft) : E ≃L[ℝ] (ι → ℝ) := by
  let T := latticeDualMap b B
  have hi : Function.Injective T := latticeDualMap_injective b B hB
  let U : (ι → ℝ) →ₗ[ℝ] (ι → ℝ) := T.comp b.equivFun.symm.toLinearMap
  have hiU : Function.Injective U := hi.comp b.equivFun.symm.injective
  have hs : Function.Surjective T := by
    intro y
    obtain ⟨z, hz⟩ := LinearMap.surjective_of_injective hiU y
    exact ⟨b.equivFun.symm z, hz⟩
  let : FiniteDimensional ℝ E := b.finiteDimensional_of_finite
  exact (LinearEquiv.ofBijective T ⟨hi, hs⟩).toContinuousLinearEquiv

theorem latticeDualCoordinates_apply (hB : B.SeparatingLeft) (x : E) (i : ι) :
    latticeDualCoordinates b B hB x i = B x (b i) := rfl

theorem latticeDualCoordinates_pairing (hB : B.SeparatingLeft)
    (ξ y : ι → ℝ) :
    B ((latticeDualCoordinates b B hB).symm ξ) (b.equivFun.symm y) =
      ∑ i, ξ i * y i := by
  rw [← b.sum_repr (b.equivFun.symm y), map_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [map_smul]
  have h := congrFun ((latticeDualCoordinates b B hB).apply_symm_apply ξ) i
  change B ((latticeDualCoordinates b B hB).symm ξ) (b i) = ξ i at h
  rw [h]
  have hy : b.repr (b.equivFun.symm y) i = y i := congrFun (b.equivFun.apply_symm_apply y) i
  rw [hy, smul_eq_mul, mul_comm]

end

/-! Integer dual coordinates are exactly the characters trivial on the
integer span of the primal basis. -/

open scoped Classical

variable {E ι : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [Fintype ι]
variable (b : Module.Basis ι ℝ E) (B : LinearMap.BilinForm ℝ E) (hB : B.SeparatingLeft)

theorem latticeDualInteger_injective :
    Function.Injective (fun n : ι → ℤ => (latticeDualCoordinates b B hB).symm (fun i => (n i : ℝ))) := by
  intro n m h
  have hh := (latticeDualCoordinates b B hB).symm.injective h
  funext i
  exact_mod_cast congrFun hh i

theorem latticeDualInteger_iff (x : E) :
    (∃ n : ι → ℤ, (latticeDualCoordinates b B hB).symm (fun i => (n i : ℝ)) = x) ↔
      ∀ m : ι → ℤ, RealCharacters.LocalAnalysis.realCharacter 1 (B x (b.equivFun.symm (fun i => (m i : ℝ)))) = 1 := by
  constructor
  · rintro ⟨n, rfl⟩ m
    rw [latticeDualCoordinates_pairing]
    apply (RealCharacters.LocalAnalysis.realCharacter_one_eq_one_iff _).mpr
    exact ⟨∑ i, n i * m i, by push_cast; rfl⟩
  · intro hx
    have hi (i : ι) : ∃ z : ℤ, (z : ℝ) = B x (b i) := by
      apply (RealCharacters.LocalAnalysis.realCharacter_one_eq_one_iff _).mp
      have hh := hx (Pi.single i 1)
      have he : b.equivFun.symm (fun j => ((Pi.single i 1 : ι → ℤ) j : ℝ)) = b i := by
        rw [Module.Basis.equivFun_symm_apply]
        simp [Pi.single_apply]
      rw [he] at hh
      exact hh
    choose n hn using hi
    refine ⟨n, ?_⟩
    apply (latticeDualCoordinates b B hB).injective
    rw [(latticeDualCoordinates b B hB).apply_symm_apply]
    funext i
    exact hn i

end

end OAI.RepresentationTheory.Weil.AdelicSplitting.LatticeDualCoordinates.LocalAnalysis
