import OAI.AlgebraicGeometry.PELModuli.CMPoints.ScalarQuotientMk
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.TorsionCongruence
import Mathlib.LinearAlgebra.Isomorphisms

/-! # Lattice Division -/

namespace OAI.AlgebraicGeometry.PELModuli.CMPoints.LatticeDivision

noncomputable section

/-! Division by N identifies an actual lattice modulo N with the
N-torsion in its ambient rational-vector-space quotient. The equivalence
retains every commuting coefficient action. -/

variable {R V : Type*} [CommRing R] [AddCommGroup V] [Module R V]
  [Module ℚ V]
  (Λ : Submodule R V) (N : ℕ) [NeZero N]

def moduleTorsion : Submodule R (V ⧸ Λ) :=
  LinearMap.ker (N • (LinearMap.id : (V ⧸ Λ) →ₗ[R] V ⧸ Λ))

def latticeDivisionMap : Λ →ₗ[R] moduleTorsion Λ N where
  toFun x := ⟨Λ.mkQ ((N : ℚ)⁻¹ • x.val), by
    change N • Λ.mkQ ((N : ℚ)⁻¹ • x.val) = 0
    rw [← map_nsmul, AbelianModuli.ReferenceFamily.TorsionCongruence.TorusTorsion.nat_smul_inverse]
    exact (Submodule.Quotient.mk_eq_zero _).mpr x.property⟩
  map_add' x y := by
    apply Subtype.ext
    exact (congrArg Λ.mkQ (smul_add (N : ℚ)⁻¹ x.val y.val)).trans (Λ.mkQ.map_add _ _)
  map_smul' a x := by
    apply Subtype.ext
    exact (congrArg Λ.mkQ (smul_comm (N : ℚ)⁻¹ a x.val)).trans (Λ.mkQ.map_smul a _)

theorem latticeDivisionMap_surjective : Function.Surjective (latticeDivisionMap Λ N) := by
  intro x
  obtain ⟨v, hv⟩ := Λ.mkQ_surjective x.val
  have hNv : N • v ∈ Λ := by
    apply (Submodule.Quotient.mk_eq_zero _).mp
    change Λ.mkQ (N • v) = 0
    rw [map_nsmul, hv]
    exact x.property
  refine ⟨⟨N • v, hNv⟩, Subtype.ext ?_⟩
  change Λ.mkQ ((N : ℚ)⁻¹ • (N • v)) = x.val
  rw [AbelianModuli.ReferenceFamily.TorsionCongruence.TorusTorsion.inverse_smul_nat, hv]

theorem latticeDivisionMap_ker :
    (latticeDivisionMap Λ N).ker = ScalarQuotientMk.scalarMultiples (M := Λ) (N : R) := by
  ext x
  constructor
  · intro hx
    have hx' : (N : ℚ)⁻¹ • x.val ∈ Λ :=
      (Submodule.Quotient.mk_eq_zero _).mp (congrArg Subtype.val hx)
    refine ⟨⟨(N : ℚ)⁻¹ • x.val, hx'⟩, Subtype.ext ?_⟩
    change (N : R) • ((N : ℚ)⁻¹ • x.val) = x.val
    rw [Nat.cast_smul_eq_nsmul]
    exact AbelianModuli.ReferenceFamily.TorsionCongruence.TorusTorsion.nat_smul_inverse N x.val
  · rintro ⟨y, rfl⟩
    apply Subtype.ext
    change Λ.mkQ ((N : ℚ)⁻¹ • ((N : R) • y.val)) = 0
    rw [Nat.cast_smul_eq_nsmul, AbelianModuli.ReferenceFamily.TorsionCongruence.TorusTorsion.inverse_smul_nat]
    exact (Submodule.Quotient.mk_eq_zero _).mpr y.property

def latticeDivisionEquiv : ScalarQuotientMk.ScalarQuotient R Λ (N : R) ≃ₗ[R] moduleTorsion Λ N :=
  (Submodule.quotEquivOfEq _ _ (latticeDivisionMap_ker Λ N).symm).trans
    ((latticeDivisionMap Λ N).quotKerEquivOfSurjective (latticeDivisionMap_surjective Λ N))

theorem latticeDivisionEquiv_mk (x : Λ) :
    (latticeDivisionEquiv Λ N (Submodule.Quotient.mk x)).val =
      Λ.mkQ ((N : ℚ)⁻¹ • x.val) := rfl

end

end OAI.AlgebraicGeometry.PELModuli.CMPoints.LatticeDivision
