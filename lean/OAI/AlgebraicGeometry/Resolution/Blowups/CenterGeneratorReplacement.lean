import OAI.AlgebraicGeometry.Resolution.Blowups.Boundary.CenterPivot

/-! # Center Generator Replacement -/

namespace OAI.AlgebraicGeometry.Resolution.Blowups.CenterGeneratorReplacement.Construction

noncomputable section

/-! Exact replacement of one center generator by a selected boundary equation. -/

universe u

variable {R ι : Type u} [CommRing R]

def centerReplacementFamily (g : ι → R) (i : ι) (z : R) : Option {j : ι // i ≠ j} → R :=
  AdaptedEtaleFrame.Construction.transverseExtendedCoordinates (fun j : {j : ι // i ≠ j} => g j.val) z

variable [Fintype ι] [DecidableEq ι]

/-- Replacing a generator by a linear combination with a unit coefficient
preserves the actual center ideal and every complementary generator. -/
theorem centerReplacementFamily_span (g c : ι → R) (i : ι) (z : R)
    (hc : (∑ j, c j * g j) = z) (hu : IsUnit (c i)) :
    Ideal.span (Set.range (centerReplacementFamily g i z)) = Ideal.span (Set.range g) := by
  let K := Ideal.span (Set.range (centerReplacementFamily g i z))
  have hzK : z ∈ K := Ideal.subset_span ⟨none, rfl⟩
  have hgK (j : ι) (hij : i ≠ j) : g j ∈ K := Ideal.subset_span ⟨some ⟨j, hij⟩, rfl⟩
  have hrest : (∑ j ∈ Finset.univ.erase i, c j * g j) ∈ K := by
    apply K.sum_mem
    intro j hj
    exact K.mul_mem_left _ (hgK j (Ne.symm (Finset.mem_erase.mp hj).1))
  have hsum : (∑ j, c j * g j) ∈ K := hc.symm ▸ hzK
  have hterm : c i * g i ∈ K := by
    have h := K.sub_mem hsum hrest
    rw [← Finset.add_sum_erase Finset.univ (fun j => c j * g j) (Finset.mem_univ i),
      add_sub_cancel_right] at h
    exact h
  have hgi : g i ∈ K := (K.unit_mul_mem_iff_mem hu).mp hterm
  apply le_antisymm
  · apply Ideal.span_le.mpr
    rintro x ⟨j, rfl⟩
    cases j with
    | none =>
        change z ∈ Ideal.span (Set.range g)
        rw [← hc]
        exact Ideal.sum_mem _ (fun j _ => Ideal.mul_mem_left _ _ (Ideal.subset_span ⟨j, rfl⟩))
    | some j => exact Ideal.subset_span ⟨j.val, rfl⟩
  · apply Ideal.span_le.mpr
    rintro x ⟨j, rfl⟩
    by_cases hij : i = j
    · exact hij ▸ hgi
    · exact hgK j hij

end

end OAI.AlgebraicGeometry.Resolution.Blowups.CenterGeneratorReplacement.Construction
