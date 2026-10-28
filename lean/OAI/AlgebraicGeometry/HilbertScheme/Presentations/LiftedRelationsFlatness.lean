import OAI.AlgebraicGeometry.HilbertScheme.Presentations.FiberwiseExactness

/-! # Lifted Relations Flatness -/

namespace OAI.AlgebraicGeometry.HilbertScheme.Presentations.LiftedRelationsFlatness

noncomputable section

/-! A finite presentation over a local ring has free cokernel when every relation in the residue field lifts to a relation over the ring. -/

open TensorProduct

universe u v w z

variable {R : Type u} [CommRing R]
variable {M : Type v} [AddCommGroup M] [Module R M]
variable {N : Type w} [AddCommGroup N] [Module R N]

theorem range_subtype_lTensor_injective_of_lifted_relations
    (f : M →ₗ[R] N) (Q : Type z) [AddCommGroup Q] [Module R Q]
    (h : Function.Exact (f.ker.subtype.lTensor Q) (f.lTensor Q)) :
    Function.Injective (f.range.subtype.lTensor Q) := by
  have hcomp : f.range.subtype.comp f.rangeRestrict = f := by
    apply LinearMap.ext
    intro x
    rfl
  have hzero : f.rangeRestrict.comp f.ker.subtype = 0 := by
    apply LinearMap.ext
    intro x
    exact Subtype.ext x.property
  intro x y hxy
  apply sub_eq_zero.mp
  have hz : f.range.subtype.lTensor Q (x - y) = 0 := by rw [map_sub, hxy, sub_self]
  obtain ⟨a, ha⟩ := LinearMap.lTensor_surjective Q f.surjective_rangeRestrict (x - y)
  have hfa : f.lTensor Q a = 0 := by
    rw [← hcomp, LinearMap.lTensor_comp, LinearMap.comp_apply, ha]
    exact hz
  obtain ⟨b, rfl⟩ := (h a).mp hfa
  rw [← ha, ← LinearMap.lTensor_comp_apply, hzero, LinearMap.lTensor_zero, LinearMap.zero_apply]

theorem cokernel_free_of_lifted_residue_relations [IsLocalRing R]
    [Module.Finite R M] [Module.Finite R N] [Module.Free R N]
    (f : M →ₗ[R] N)
    (h : Function.Exact (f.ker.subtype.lTensor (IsLocalRing.ResidueField R))
      (f.lTensor (IsLocalRing.ResidueField R))) :
    Module.Free R (N ⧸ f.range) := by
  let : Module.Finite R f.range := Module.Finite.range f
  exact Module.free_of_lTensor_residueField_injective f.range.subtype f.range.mkQ
    f.range.mkQ_surjective (LinearMap.exact_subtype_mkQ f.range)
    (range_subtype_lTensor_injective_of_lifted_relations f (IsLocalRing.ResidueField R) h)

theorem lTensor_relations_exact_of_flat_cokernel
    (f : M →ₗ[R] N) [Module.Flat R (N ⧸ f.range)]
    (Q : Type z) [AddCommGroup Q] [Module R Q] :
    Function.Exact (f.ker.subtype.lTensor Q) (f.lTensor Q) := by
  have hinj := LinearMap.lTensor_injective_of_exact_of_flat f.range.mkQ f.range.mkQ_surjective
    f.range.subtype f.range.subtype_injective (LinearMap.exact_subtype_mkQ f.range) Q
  have hex := lTensor_exact Q (FiberwiseExactness.exact_kernel_rangeRestrict R f) f.surjective_rangeRestrict
  have hcomp : f.range.subtype.comp f.rangeRestrict = f := by
    apply LinearMap.ext
    intro x
    rfl
  intro x
  have he : f.lTensor Q x = 0 ↔ f.rangeRestrict.lTensor Q x = 0 := by
    rw [← hcomp, LinearMap.lTensor_comp, LinearMap.comp_apply]
    exact (map_eq_zero_iff (f.range.subtype.lTensor Q) hinj)
  exact he.trans (hex x)

end

end OAI.AlgebraicGeometry.HilbertScheme.Presentations.LiftedRelationsFlatness
