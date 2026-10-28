import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.HeckeKernel
import Mathlib.Data.Finsupp.Indicator

/-! # Hecke -/

namespace OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Hecke.Construction

noncomputable section

/-!
Construct the unnormalized double-coset operator when its right-coset
support is finite. The inverse representative is the superlattice
convention already fixed by TateComparison. Every supporting coset has coefficient one.
-/

open scoped Classical

variable {G : Type*} [Group G] (U : Subgroup G)

def rawRightCosetSupport (g : G) : Set (G ⧸ U) :=
  MulAction.orbit U (QuotientGroup.mk g⁻¹)

theorem rawRightCosetSupport_smul_iff (g : G) (u : U) (x : G ⧸ U) :
    (u : G) • x ∈ rawRightCosetSupport U g ↔ x ∈ rawRightCosetSupport U g := by
  constructor
  · intro h
    have h' := MulAction.mem_orbit_of_mem_orbit u⁻¹ h
    change u⁻¹ • (u • x) ∈ rawRightCosetSupport U g at h'
    simpa only [inv_smul_smul] using h'
  · intro h
    exact MulAction.mem_orbit_of_mem_orbit u h

/-- The orbit of the inverse representative is exactly Ug⁻¹U/U. -/
theorem rawRightCosetSupport_mk_iff (g x : G) :
    QuotientGroup.mk x ∈ rawRightCosetSupport U g ↔
      ∃ k l : U, x = (k : G) * g⁻¹ * (l : G) := by
  constructor
  · intro h
    obtain ⟨k, hk⟩ := MulAction.mem_orbit_iff.mp h
    change QuotientGroup.mk ((k : G) * g⁻¹) = QuotientGroup.mk x at hk
    let l : U := ⟨((k : G) * g⁻¹)⁻¹ * x,
      QuotientGroup.leftRel_apply.mp (Quotient.exact hk)⟩
    refine ⟨k, l, ?_⟩
    change x = ((k : G) * g⁻¹) * (((k : G) * g⁻¹)⁻¹ * x)
    simp only [mul_inv_cancel_left]
  · rintro ⟨k, l, rfl⟩
    apply MulAction.mem_orbit_iff.mpr
    refine ⟨k, ?_⟩
    change QuotientGroup.mk ((k : G) * g⁻¹) = QuotientGroup.mk ((k : G) * g⁻¹ * (l : G))
    apply Quotient.sound
    apply QuotientGroup.leftRel_apply.mpr
    simpa only [inv_mul_cancel_left] using l.property

def rawDoubleCosetKernel (g : G) (hfinite : (rawRightCosetSupport U g).Finite) : TateComparison.HeckeKernel.CosetModule U :=
  Finsupp.indicator hfinite.toFinset (fun _ _ => 1)

theorem rawDoubleCosetKernel_apply (g : G) (hfinite : (rawRightCosetSupport U g).Finite)
    (x : G ⧸ U) :
    rawDoubleCosetKernel U g hfinite x = if x ∈ rawRightCosetSupport U g then 1 else 0 := by
  simp [rawDoubleCosetKernel, Finsupp.indicator_apply]

/-- The raw column is invariant under the integral level. -/
theorem rawDoubleCosetKernel_invariant (g : G) (hfinite : (rawRightCosetSupport U g).Finite)
    (u : U) :
    TateComparison.HeckeKernel.translate U (u : G) (rawDoubleCosetKernel U g hfinite) = rawDoubleCosetKernel U g hfinite := by
  ext x
  obtain ⟨y, rfl⟩ := (MulAction.bijective (u : G)).surjective x
  change Finsupp.mapDomain (fun z : G ⧸ U => (u : G) • z)
    (rawDoubleCosetKernel U g hfinite) ((u : G) • y) = _
  rw [Finsupp.mapDomain_apply_of_injective (MulAction.injective (u : G)), rawDoubleCosetKernel_apply,
    rawDoubleCosetKernel_apply, rawRightCosetSupport_smul_iff]

/-- The finite right-coset orbit gives a genuine spherical Hecke operator. -/
def rawDoubleCosetOperator (g : G) (hfinite : (rawRightCosetSupport U g).Finite) : TateComparison.HeckeKernel.SphericalHecke U :=
  HeckeKernel.Construction.sphericalHeckeFromKernel U (rawDoubleCosetKernel U g hfinite)
    (rawDoubleCosetKernel_invariant U g hfinite)

/-- Its kernel is exactly the raw characteristic function in TateComparison's
inverse-lattice convention, with integral-level volume one. -/
theorem rawDoubleCosetOperator_spec (g : G) (hfinite : (rawRightCosetSupport U g).Finite) :
    TateComparison.HeckeKernel.IsRawDoubleCoset U g (rawDoubleCosetOperator U g hfinite) := by
  intro x
  change TateComparison.HeckeKernel.kernel U (HeckeKernel.Construction.sphericalHeckeFromKernel U _ _) (QuotientGroup.mk x) = _
  rw [HeckeKernel.Construction.sphericalHeckeFromKernel_kernel, rawDoubleCosetKernel_apply, rawRightCosetSupport_mk_iff]

end

end OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Hecke.Construction
