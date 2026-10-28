import OAI.AlgebraicGeometry.Comparison.Betti.Laurent.SectorCochainProduct
import OAI.AlgebraicGeometry.Comparison.Betti.SupportedCochainContraction

/-! # Sector Proper Support Contraction -/

namespace OAI.AlgebraicGeometry.Comparison.Betti.SectorProperSupportContraction.Dolbeault

noncomputable section

/-! A simultaneous contraction of every proper Laurent support, with its fixed holomorphic coefficients. -/

open OAI.AlgebraicGeometry.Comparison.Betti.SupportedCochainContraction.Cech

variable {ι : Type} [Fintype ι] [DecidableEq ι]

local instance supportCochains_addZeroClass (V : Type) [AddCommGroup V]
    (J : Finset ι) (q : ℕ) : AddZeroClass (SupportedCochains.Cech.supportedCechCochains V J q) := by
  infer_instance

local instance properSupportCoefficients_addCommGroup (J : Finset ι) (d : ℤ) :
    AddCommGroup ↥(HomogeneousSectorSingle.Dolbeault.homogeneousSectorCoefficients J d) := Submodule.addCommGroup _

local instance properSupportCochains_addCommGroup (d : ℤ) (q : ℕ) (J : Finset ι) :
    AddCommGroup (Laurent.SectorCochainProduct.Dolbeault.homogeneousSectorSupportedCochains d q J) := AddSubgroup.toAddCommGroup _

omit [DecidableEq ι] in
theorem properSupport_exists_index (J : Finset ι) (hJ : J ≠ Finset.univ) : ∃ i, i ∉ J := by
  by_contra h
  apply hJ
  apply Finset.ext
  intro i
  constructor
  · intro _
    exact Finset.mem_univ i
  · intro _
    by_contra hi
    exact h ⟨i, hi⟩

def properSupportAnchor (J : Finset ι) (hJ : J ≠ Finset.univ) : ι :=
  Classical.choose (properSupport_exists_index J hJ)

omit [DecidableEq ι] in
theorem properSupportAnchor_not_mem (J : Finset ι) (hJ : J ≠ Finset.univ) :
    properSupportAnchor J hJ ∉ J := Classical.choose_spec (properSupport_exists_index J hJ)

def sectorProperSupportPrimitive (d : ℤ) (q : ℕ)
    (z : ∀ J : Finset ι, Laurent.SectorCochainProduct.Dolbeault.homogeneousSectorSupportedCochains d (q + 1) J) :
    ∀ J : Finset ι, Laurent.SectorCochainProduct.Dolbeault.homogeneousSectorSupportedCochains d q J := fun J =>
  if hJ : J = Finset.univ then 0 else
    SupportedCochainContraction.Cech.supportedCechContraction J (properSupportAnchor J hJ) (properSupportAnchor_not_mem J hJ) q (z J)

def sectorFullSupportPart (d : ℤ) (q : ℕ)
    (z : ∀ J : Finset ι, Laurent.SectorCochainProduct.Dolbeault.homogeneousSectorSupportedCochains d q J) :
    ∀ J : Finset ι, Laurent.SectorCochainProduct.Dolbeault.homogeneousSectorSupportedCochains d q J := fun J =>
  if J = Finset.univ then z J else 0

theorem sectorProperSupportPrimitive_homotopy (d : ℤ) (q : ℕ)
    (z : ∀ J : Finset ι, Laurent.SectorCochainProduct.Dolbeault.homogeneousSectorSupportedCochains d (q + 1) J) (J : Finset ι) :
    SupportedCochains.Cech.supportedCechDifferential J q (sectorProperSupportPrimitive d q z J) +
      sectorProperSupportPrimitive d (q + 1)
        (fun K => SupportedCochains.Cech.supportedCechDifferential K (q + 1) (z K)) J =
      z J - sectorFullSupportPart d (q + 1) z J := by
  by_cases hJ : J = Finset.univ
  · simp only [sectorProperSupportPrimitive, sectorFullSupportPart, dite_eq_left hJ, ite_eq_left hJ,
      map_zero, add_zero, sub_self]
  · simp only [sectorProperSupportPrimitive, sectorFullSupportPart, dite_eq_right hJ, ite_eq_right hJ, sub_zero]
    exact SupportedCochainContraction.Cech.supportedCechContraction_homotopy J (properSupportAnchor J hJ)
      (properSupportAnchor_not_mem J hJ) q (z J)

theorem sectorProperSupportPrimitive_cycle (d : ℤ) (q : ℕ)
    (z : ∀ J : Finset ι, Laurent.SectorCochainProduct.Dolbeault.homogeneousSectorSupportedCochains d (q + 1) J)
    (hz : ∀ J, SupportedCochains.Cech.supportedCechDifferential J (q + 1) (z J) = 0) (J : Finset ι) :
    SupportedCochains.Cech.supportedCechDifferential J q (sectorProperSupportPrimitive d q z J) +
      sectorFullSupportPart d (q + 1) z J = z J := by
  by_cases hJ : J = Finset.univ
  · simp only [sectorProperSupportPrimitive, sectorFullSupportPart, dite_eq_left hJ, ite_eq_left hJ,
      map_zero, zero_add]
  · simpa only [sectorProperSupportPrimitive, sectorFullSupportPart, dite_eq_right hJ, ite_eq_right hJ,
      add_zero] using (SupportedCochainContraction.Cech.supportedCechContraction_cycle
        (V := ↥(HomogeneousSectorSingle.Dolbeault.homogeneousSectorCoefficients J d)) J (properSupportAnchor J hJ)
        (properSupportAnchor_not_mem J hJ) q (z J) (hz J))

end

end OAI.AlgebraicGeometry.Comparison.Betti.SectorProperSupportContraction.Dolbeault
