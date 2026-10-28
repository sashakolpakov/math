import Mathlib.RingTheory.Algebraic.LinearIndependent
import Mathlib.FieldTheory.IsAlgClosed.Basic
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.TensorProduct.Basis
import Mathlib.RingTheory.TensorProduct.Basic

/-! # Rank Points -/

namespace OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Countable.RankPoints.Construction

noncomputable section

/-! Countable vector-space dimension over an uncountable algebraically
closed field forces every maximal residue field to be the base field.
This applies to scalar extensions of countable coefficient fields. -/

open scoped Cardinal TensorProduct

theorem field_isAlgebraic_of_countable_rank
    {C L : Type} [Field C] [Uncountable C] [Field L] [Algebra C L]
    (h : Module.rank C L ≤ Cardinal.aleph0) : Algebra.IsAlgebraic C L := by
  constructor
  intro x
  by_contra hx
  have hc : Cardinal.mk C ≤ Module.rank C L := by
    simpa only [Cardinal.lift_id] using
      (show Transcendental C x from hx).linearIndependent_sub_inv.cardinal_lift_le_rank
  exact (not_le_of_gt (Cardinal.aleph0_lt_mk (α := C))) (hc.trans h)

set_option backward.isDefEq.respectTransparency false in
theorem algHom_to_base_of_countable_rank
    (C R : Type) [Field C] [Uncountable C] [IsAlgClosed C]
    [CommRing R] [Nontrivial R] [Algebra C R]
    (h : Module.rank C R ≤ Cardinal.aleph0) : Nonempty (R →ₐ[C] C) := by
  obtain ⟨I, hI⟩ := Ideal.exists_maximal R
  let : I.IsMaximal := hI
  let L := R ⧸ I
  let : Field L := Ideal.Quotient.field I
  have hr : Module.rank C L ≤ Module.rank C R :=
    (Ideal.Quotient.mkₐ C I).toLinearMap.rank_le_of_surjective (Ideal.Quotient.mk_surjective)
  have : Algebra.IsAlgebraic C L := field_isAlgebraic_of_countable_rank (C := C) (L := L) (hr.trans h)
  let e : C ≃ₐ[C] L := AlgEquiv.ofBijective (Algebra.ofId C L)
    (IsAlgClosed.algebraMap_bijective_of_isIntegral (k := C))
  exact ⟨e.symm.toAlgHom.comp (Ideal.Quotient.mkₐ C I)⟩

theorem scalarExtension_rank_countable
    (K C F : Type) [Field K] [Field C] [Algebra K C]
    [AddCommGroup F] [Module K F] [Countable F] :
    Module.rank C (C ⊗[K] F) ≤ Cardinal.aleph0 := by
  let b := Module.Free.chooseBasis K F
  rw [← (b.baseChange C).mk_eq_rank'', b.mk_eq_rank'']
  exact (rank_le_card K F).trans Cardinal.mk_le_aleph0

end

end OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Countable.RankPoints.Construction
