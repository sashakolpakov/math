import OAI.AlgebraicGeometry.Comparison.Betti.HomogeneousLaurent

/-! # Cone Coordinates -/

namespace OAI.AlgebraicGeometry.Comparison.Betti.Laurent.ConeCoordinates.Dolbeault

noncomputable section

/-! Normalization of homogeneous coordinate cones at a chosen nonzero coordinate. -/

open _root_.TopologicalSpace Set

variable {ι : Type} [Fintype ι] [DecidableEq ι]

def laurentAffineDomain (s : Finset ι) (i : ι) : Opens ({j : ι // j ≠ i} → ℂ) :=
  DivisorClass.Chern.Complex.CoordinateSplit.coordinatePolydisc (fun j => SectorTo.Dolbeault.laurentCoordinateOpens s j.val)

theorem mem_laurentAffineDomain (s : Finset ι) (i : ι) (z : {j : ι // j ≠ i} → ℂ) :
    z ∈ laurentAffineDomain s i ↔ ∀ j : {j : ι // j ≠ i}, j.val ∈ s → z j ≠ 0 := by
  rw [laurentAffineDomain, DivisorClass.Chern.Complex.CoordinateSplit.mem_coordinatePolydisc]
  apply forall_congr'
  intro j
  by_cases hj : j.val ∈ s <;>
    simp [SectorTo.Dolbeault.laurentCoordinateOpens, hj, PuncturedCauchy.Dolbeault.puncturedComplexOpen]

def laurentConeRatios (i : ι) (x : ι → ℂ) : {j : ι // j ≠ i} → ℂ :=
  fun j => x j.val / x i

theorem laurentConeRatios_mapsTo (s : Finset ι) (i : ι) (hi : i ∈ s) :
    MapsTo (laurentConeRatios i) (SectorTo.Dolbeault.laurentCoordinateDomain s) (laurentAffineDomain s i) := by
  intro x hx
  apply (mem_laurentAffineDomain s i _).mpr
  intro j hj
  exact div_ne_zero ((SectorTo.Dolbeault.mem_laurentCoordinateDomain s x).mp hx j.val hj)
    ((SectorTo.Dolbeault.mem_laurentCoordinateDomain s x).mp hx i hi)

def laurentConeNormalize (s : Finset ι) (i : ι) (hi : i ∈ s)
    (x : SectorTo.Dolbeault.laurentCoordinateDomain s) : laurentAffineDomain s i :=
  ⟨laurentConeRatios i x.val, laurentConeRatios_mapsTo s i hi x.property⟩

def laurentConeAffineLift (i : ι) (z : {j : ι // j ≠ i} → ℂ) : ι → ℂ :=
  (DivisorClass.Chern.Complex.CoordinateSplit.splitComplexCoordinate i).symm (z, 1)

theorem laurentConeAffineLift_same (i : ι) (z : {j : ι // j ≠ i} → ℂ) :
    laurentConeAffineLift i z i = 1 := DivisorClass.Chern.Complex.CoordinateSplit.splitComplexCoordinate_symm_same i _

theorem laurentConeAffineLift_other (i : ι) (z : {j : ι // j ≠ i} → ℂ) (j : ι) (hj : j ≠ i) :
    laurentConeAffineLift i z j = z ⟨j, hj⟩ := DivisorClass.Chern.Complex.CoordinateSplit.splitComplexCoordinate_symm_other i _ j hj

theorem laurentConeAffineLift_mapsTo (s : Finset ι) (i : ι) :
    MapsTo (laurentConeAffineLift i) (laurentAffineDomain s i) (SectorTo.Dolbeault.laurentCoordinateDomain s) := by
  intro z hz
  apply (SectorTo.Dolbeault.mem_laurentCoordinateDomain s _).mpr
  intro j hj
  by_cases hji : j = i
  · subst j
    rw [laurentConeAffineLift_same]
    exact one_ne_zero
  · rw [laurentConeAffineLift_other i z j hji]
    exact (mem_laurentAffineDomain s i z).mp hz ⟨j, hji⟩ hj

def laurentConeAffinePoint (s : Finset ι) (i : ι) (z : laurentAffineDomain s i) :
    SectorTo.Dolbeault.laurentCoordinateDomain s :=
  ⟨laurentConeAffineLift i z.val, laurentConeAffineLift_mapsTo s i z.property⟩

theorem laurentConeNormalize_affinePoint (s : Finset ι) (i : ι) (hi : i ∈ s)
    (z : laurentAffineDomain s i) :
    laurentConeNormalize s i hi (laurentConeAffinePoint s i z) = z := by
  apply Subtype.ext
  funext j
  change laurentConeAffineLift i z.val j.val / laurentConeAffineLift i z.val i = z.val j
  rw [laurentConeAffineLift_same, laurentConeAffineLift_other i z.val j.val j.property, div_one]

theorem laurentConeAffinePoint_normalize (s : Finset ι) (i : ι) (hi : i ∈ s)
    (x : SectorTo.Dolbeault.laurentCoordinateDomain s) :
    (laurentConeAffinePoint s i (laurentConeNormalize s i hi x)).val =
      FiniteUniqueness.Dolbeault.laurentUniformScale (x.val i)⁻¹ x.val := by
  funext j
  by_cases hji : j = i
  · subst j
    change laurentConeAffineLift i _ i = (x.val i)⁻¹ * x.val i
    rw [laurentConeAffineLift_same, inv_mul_cancel₀ ((SectorTo.Dolbeault.mem_laurentCoordinateDomain s x.val).mp x.property i hi)]
  · change laurentConeAffineLift i _ j = (x.val i)⁻¹ * x.val j
    rw [laurentConeAffineLift_other i _ j hji]
    exact div_eq_inv_mul _ _

end

end OAI.AlgebraicGeometry.Comparison.Betti.Laurent.ConeCoordinates.Dolbeault
