import OAI.AlgebraicGeometry.Resolution.Blowups.Boundary.CenterReplacementFrame

/-! # Boundary Center Replacement -/

namespace OAI.AlgebraicGeometry.Resolution.Blowups.Pointed.BoundaryCenterReplacement.Construction

noncomputable section

/-! Actual principal-open center replacement preserving already retained boundary generators. -/

universe u

variable {k R ι : Type u} [CommRing k] [CommRing R] [Algebra k R]
  [Fintype ι] [DecidableEq ι]

/-- Around the original prime, a boundary equation can replace a center
generator outside the retained index set. The actual center ideal and a
full dual frame are preserved on the explicitly constructed principal open. -/
theorem exists_pointed_boundary_center_replacement
    (g : ι → R) (D : ι → Derivation k R R)
    (hD : ∀ i j, D i (g j) = if i = j then 1 else 0)
    (z : R) (hz : z ∈ Ideal.span (Set.range g))
    (E : Derivation k R R) (q : Ideal R) [q.IsPrime]
    (hg : ∀ i, g i ∈ q) (hEz : E z ∉ q)
    (B : Finset ι) (hEB : ∀ i ∈ B, E (g i) = 0) :
    ∃ s ∉ q, ∃ i ∉ B, ∃ F : Option {j : ι // i ≠ j} →
        Derivation k (Localization.Away s) (Localization.Away s),
      Ideal.span (Set.range (CenterGeneratorReplacement.Construction.centerReplacementFamily
          (fun j => algebraMap R (Localization.Away s) (g j)) i (algebraMap R (Localization.Away s) z))) =
        (Ideal.span (Set.range g)).map (algebraMap R (Localization.Away s)) ∧
      ∀ p t, F p (CenterGeneratorReplacement.Construction.centerReplacementFamily (fun j => algebraMap R (Localization.Away s) (g j)) i
        (algebraMap R (Localization.Away s) z) t) = if p = t then 1 else 0 := by
  obtain ⟨c, i, hiB, hc, hci, hDiz⟩ := Boundary.CenterPivot.Construction.exists_boundary_center_pivot_outside g D hD z hz E q hg hEz B hEB
  let s := c i * D i z
  have hs : s ∉ q := q.primeCompl.mul_mem hci hDiz
  let A := Localization.Away s
  let : Algebra.FormallyEtale R A := Algebra.FormallyEtale.of_isLocalization (Submonoid.powers s)
  let g' : ι → A := fun j => algebraMap R A (g j)
  let D' : ι → Derivation k A A := fun j => Etale.Derivation.Construction.extendEtaleRingDerivation (S := A) (D j)
  have hD' : ∀ p t, D' p (g' t) = if p = t then 1 else 0 := by
    intro p t
    change Etale.Derivation.Construction.extendEtaleRingDerivation (S := A) (D p) (algebraMap R A (g t)) = _
    rw [Etale.Derivation.Construction.extendEtaleRingDerivation_algebraMap, hD]
    split_ifs <;> simp
  have hu : IsUnit (algebraMap R A (c i) * algebraMap R A (D i z)) := by
    rw [← map_mul]
    exact IsLocalization.Away.algebraMap_isUnit s
  have huc := isUnit_of_mul_isUnit_left hu
  have huD := isUnit_of_mul_isUnit_right hu
  have hunit : IsUnit (D' i (algebraMap R A z)) := by
    change IsUnit (Etale.Derivation.Construction.extendEtaleRingDerivation (S := A) (D i) (algebraMap R A z))
    rw [Etale.Derivation.Construction.extendEtaleRingDerivation_algebraMap]
    exact huD
  obtain ⟨F, hF⟩ := Boundary.CenterReplacementFrame.Construction.exists_centerReplacement_dual_frame g' D' hD' i (algebraMap R A z) hunit
  refine ⟨s, hs, i, hiB, F, ?_, hF⟩
  have hc' : (∑ j, algebraMap R A (c j) * g' j) = algebraMap R A z := by
    simpa only [map_sum, map_mul] using congrArg (algebraMap R A) hc
  have hgen := CenterGeneratorReplacement.Construction.centerReplacementFamily_span g' (fun j => algebraMap R A (c j)) i (algebraMap R A z) hc' huc
  rw [Ideal.map_span, ← Set.range_comp]
  exact hgen

end

end OAI.AlgebraicGeometry.Resolution.Blowups.Pointed.BoundaryCenterReplacement.Construction
