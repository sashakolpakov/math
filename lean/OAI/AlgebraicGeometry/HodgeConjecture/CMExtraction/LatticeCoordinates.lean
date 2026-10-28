import OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.CoefficientVectorCoordinates
import Mathlib.Algebra.Module.Lattice

/-! # Lattice Coordinates -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.LatticeCoordinates.TestTransport

noncomputable section

section

/-! Extend the specified integral lattice basis to rational coordinates.
The same coordinates characterize the original lattice exactly. -/

open scoped Classical

open _root_.Module

variable {V J : Type*} [AddCommGroup V] [Module ℚ V]
  [Fintype J] (L : Submodule ℤ V) [Submodule.IsLattice ℚ L] (b : Basis J ℤ L)

theorem latticeBasis_rational_coordinates (x : L) :
    (b.extendOfIsLattice ℚ).equivFun x.val = fun j => (b.equivFun x j : ℚ) := by
  apply (b.extendOfIsLattice ℚ).equivFun.symm.injective
  rw [LinearEquiv.symm_apply_apply, Basis.equivFun_symm_apply]
  have h := congrArg (fun y : L => y.val) (b.sum_equivFun x)
  simpa only [Basis.extendOfIsLattice_apply, Submodule.coe_sum, Submodule.coe_smul,
    Int.cast_smul_eq_zsmul] using h.symm

theorem lattice_mem_iff_integer_coordinates (x : V) :
    x ∈ L ↔ ∀ j, ∃ z : ℤ, (z : ℚ) = (b.extendOfIsLattice ℚ).equivFun x j := by
  constructor
  · intro hx j
    exact ⟨b.equivFun ⟨x, hx⟩ j, (congr_fun (latticeBasis_rational_coordinates L b ⟨x, hx⟩) j).symm⟩
  · intro hx
    choose z hz using hx
    let y := b.equivFun.symm z
    have hy : y.val = x := by
      apply (b.extendOfIsLattice ℚ).equivFun.injective
      rw [latticeBasis_rational_coordinates]
      funext j
      change (b.equivFun (b.equivFun.symm z) j : ℚ) = _
      rw [LinearEquiv.apply_symm_apply]
      exact hz j
    exact hy ▸ y.property

end

/-! The completion of the original integral lattice is exactly the
integral finite-adele lattice in the extended basis coordinates. -/

open scoped Classical

open _root_.Module

variable (E : Type) [Field E] [NumberField E]
  {I J : Type*} [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]
  (L : Submodule ℤ (I → E)) [Submodule.IsLattice ℚ L] (b : Basis J ℤ L)

def completedVectorLattice : Submodule AbelianModuli.ReferenceFamily.AdelicData.integralFiniteAdeles (I → AbelianModuli.ReferenceFamily.AdelicData.FiniteCoefficients E) :=
  Submodule.span AbelianModuli.ReferenceFamily.AdelicData.integralFiniteAdeles
    ((fun x : I → E => fun i => AbelianModuli.ReferenceFamily.AdelicData.finiteCoefficientEmbedding E (x i)) '' (L : Set (I → E)))

theorem coefficientVectorCoordinates_lattice_basis (j : J) :
    CoefficientVectorCoordinates.TestTransport.coefficientVectorCoordinates E (b.extendOfIsLattice ℚ).equivFun
      (fun i => AbelianModuli.ReferenceFamily.AdelicData.finiteCoefficientEmbedding E ((b j).val i)) = Pi.single j 1 := by
  rw [CoefficientVectorCoordinates.TestTransport.coefficientVectorCoordinates_rational]
  funext k
  have h := (b.extendOfIsLattice ℚ).equivFun_self j k
  rw [Basis.extendOfIsLattice_apply] at h
  rw [h]
  by_cases hjk : j = k
  · subst k
    simp
  · simp [hjk, Ne.symm hjk]

theorem completedVectorLattice_coordinates (x : I → AbelianModuli.ReferenceFamily.AdelicData.FiniteCoefficients E) :
    x ∈ completedVectorLattice E L ↔
      ∀ j, CoefficientVectorCoordinates.TestTransport.coefficientVectorCoordinates E (b.extendOfIsLattice ℚ).equivFun x j ∈ AbelianModuli.ReferenceFamily.AdelicData.integralFiniteAdeles := by
  let e := CoefficientVectorCoordinates.TestTransport.coefficientVectorCoordinates E (b.extendOfIsLattice ℚ).equivFun
  change x ∈ completedVectorLattice E L ↔ ∀ j, e x j ∈ AbelianModuli.ReferenceFamily.AdelicData.integralFiniteAdeles
  constructor
  · intro hx
    induction hx using Submodule.span_induction with
    | mem y hy =>
        obtain ⟨z, hz, rfl⟩ := hy
        intro j
        change CoefficientVectorCoordinates.TestTransport.coefficientVectorCoordinates E (b.extendOfIsLattice ℚ).equivFun
          (fun i => AbelianModuli.ReferenceFamily.AdelicData.finiteCoefficientEmbedding E (z i)) j ∈ AbelianModuli.ReferenceFamily.AdelicData.integralFiniteAdeles
        rw [CoefficientVectorCoordinates.TestTransport.coefficientVectorCoordinates_rational]
        change algebraMap ℚ AbelianModuli.ReferenceFamily.AdelicData.RationalFiniteAdeles ((b.extendOfIsLattice ℚ).equivFun z j) ∈ AbelianModuli.ReferenceFamily.AdelicData.integralFiniteAdeles
        obtain ⟨a, ha⟩ := (lattice_mem_iff_integer_coordinates L b z).mp hz j
        rw [← ha]
        simpa only [map_intCast] using intCast_mem AbelianModuli.ReferenceFamily.AdelicData.integralFiniteAdeles a
    | zero => intro j; simpa only [map_zero, Pi.zero_apply] using AbelianModuli.ReferenceFamily.AdelicData.integralFiniteAdeles.zero_mem
    | add y z _ _ hy hz =>
        intro j
        rw [map_add, Pi.add_apply]
        exact AbelianModuli.ReferenceFamily.AdelicData.integralFiniteAdeles.add_mem (hy j) (hz j)
    | smul c y _ hy =>
        intro j
        change e ((c : AbelianModuli.ReferenceFamily.AdelicData.RationalFiniteAdeles) • y) j ∈ AbelianModuli.ReferenceFamily.AdelicData.integralFiniteAdeles
        rw [map_smul, Pi.smul_apply, smul_eq_mul]
        exact AbelianModuli.ReferenceFamily.AdelicData.integralFiniteAdeles.mul_mem c.property (hy j)
  · intro hx
    let c : J → AbelianModuli.ReferenceFamily.AdelicData.integralFiniteAdeles := fun j => ⟨e x j, hx j⟩
    have hgen (j : J) : (fun i => AbelianModuli.ReferenceFamily.AdelicData.finiteCoefficientEmbedding E ((b j).val i)) ∈
        completedVectorLattice E L :=
      Submodule.subset_span ⟨(b j).val, (b j).property, rfl⟩
    have he : (∑ j, c j • (fun i => AbelianModuli.ReferenceFamily.AdelicData.finiteCoefficientEmbedding E ((b j).val i))) = x := by
      apply e.injective
      rw [map_sum]
      have hmap (j : J) : e (c j • (fun i => AbelianModuli.ReferenceFamily.AdelicData.finiteCoefficientEmbedding E ((b j).val i))) =
          (c j : AbelianModuli.ReferenceFamily.AdelicData.RationalFiniteAdeles) • Pi.single j 1 := by
        change e ((c j : AbelianModuli.ReferenceFamily.AdelicData.RationalFiniteAdeles) • (fun i => AbelianModuli.ReferenceFamily.AdelicData.finiteCoefficientEmbedding E ((b j).val i))) = _
        rw [map_smul]
        exact congrArg (fun y => (c j : AbelianModuli.ReferenceFamily.AdelicData.RationalFiniteAdeles) • y)
          (coefficientVectorCoordinates_lattice_basis E L b j)
      simp_rw [hmap]
      funext j
      simp [Pi.single_apply, c]
    rw [← he]
    exact Submodule.sum_mem _ (fun j _ => (completedVectorLattice E L).smul_mem (c j) (hgen j))

end

end OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.LatticeCoordinates.TestTransport
