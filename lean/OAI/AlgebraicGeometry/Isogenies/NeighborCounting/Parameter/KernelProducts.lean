import OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Parameter.ImageComparison

/-! # Kernel Products -/

namespace OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Parameter.KernelProducts

noncomputable section

/-! Passage to the original parameter scheme preserves the identity,
products, and the complete finite tuple of subgroup families. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj

attribute [local instance] AbelianScheme.FrobeniusKernel.BaseChange.Construction.pulledBackGroup AbelianScheme.IsogenyQuotient.PairingBaseChange.Construction.pulledbackGroup_commutative

universe u

theorem subgroupProduct_comap_equiv {V W : Type*} [CommGroup V] [CommGroup W]
    (e : V ≃* W) (F G : Subgroup W) :
    (AbelianScheme.IsogenyQuotient.Kernel.Product.Construction.subgroupProduct F G).comap e.toMonoidHom =
      AbelianScheme.IsogenyQuotient.Kernel.Product.Construction.subgroupProduct (F.comap e.toMonoidHom) (G.comap e.toMonoidHom) := by
  ext z
  constructor
  · rintro ⟨x, hx, y, hy, h⟩
    change e z = x * y at h
    refine ⟨e.symm x, ?_, e.symm y, ?_, ?_⟩
    · change e (e.symm x) ∈ F
      simpa only [e.apply_symm_apply] using hx
    · change e (e.symm y) ∈ G
      simpa only [e.apply_symm_apply] using hy
    · apply e.injective
      simpa only [map_mul, e.apply_symm_apply] using h
  · rintro ⟨x, hx, y, hy, rfl⟩
    exact ⟨e x, hx, e y, hy, map_mul e x y⟩

variable {S : Scheme.{u}} (A : Grp (Over S)) [IsCommMonObj A.X] (P : Over S)

theorem relativeParameter_trivial :
    AbelianScheme.IsogenyQuotient.Relative.ParameterBaseChange.Construction.relativeSubgroupOverParameter A P AbelianScheme.IsogenyQuotient.Kernel.Tuples.Construction.trivialRelativeSubgroup = AbelianScheme.IsogenyQuotient.Kernel.Tuples.Construction.trivialRelativeSubgroup := by
  ext U t z
  change (AbelianScheme.CartierDuality.CharacterBaseChange.Construction.Schemes.pullbackPointMulEquiv P.hom A U).symm z = 1 ↔ z = 1
  exact (AbelianScheme.CartierDuality.CharacterBaseChange.Construction.Schemes.pullbackPointMulEquiv P.hom A U).symm.map_eq_one_iff

theorem relativeParameter_product (F G : AbelianScheme.TorsionQuotient.SubgroupFunctor.RelativeSubgroup A.X P) :
    AbelianScheme.IsogenyQuotient.Relative.ParameterBaseChange.Construction.relativeSubgroupOverParameter A P (AbelianScheme.IsogenyQuotient.Kernel.Product.Construction.relativeKernelProduct F G) =
      AbelianScheme.IsogenyQuotient.Kernel.Product.Construction.relativeKernelProduct (AbelianScheme.IsogenyQuotient.Relative.ParameterBaseChange.Construction.relativeSubgroupOverParameter A P F)
        (AbelianScheme.IsogenyQuotient.Relative.ParameterBaseChange.Construction.relativeSubgroupOverParameter A P G) := by
  ext U t z
  exact SetLike.ext_iff.mp (subgroupProduct_comap_equiv
    (AbelianScheme.CartierDuality.CharacterBaseChange.Construction.Schemes.pullbackPointMulEquiv P.hom A U).symm
    (F.points ((Over.map P.hom).obj U) (AbelianScheme.IsogenyQuotient.Relative.ParameterBaseChange.Construction.parameterBasePoint P U))
    (G.points ((Over.map P.hom).obj U) (AbelianScheme.IsogenyQuotient.Relative.ParameterBaseChange.Construction.parameterBasePoint P U))) z

theorem relativeParameter_tuple (s : ℕ) (F : Fin s → AbelianScheme.TorsionQuotient.SubgroupFunctor.RelativeSubgroup A.X P) :
    AbelianScheme.IsogenyQuotient.Relative.ParameterBaseChange.Construction.relativeSubgroupOverParameter A P (AbelianScheme.IsogenyQuotient.Kernel.Tuples.Construction.tupleKernel s F) =
      AbelianScheme.IsogenyQuotient.Kernel.Tuples.Construction.tupleKernel s (fun i => AbelianScheme.IsogenyQuotient.Relative.ParameterBaseChange.Construction.relativeSubgroupOverParameter A P (F i)) := by
  induction s with
  | zero => exact relativeParameter_trivial A P
  | succ s ih =>
    change AbelianScheme.IsogenyQuotient.Relative.ParameterBaseChange.Construction.relativeSubgroupOverParameter A P
      (AbelianScheme.IsogenyQuotient.Kernel.Product.Construction.relativeKernelProduct (F 0) (AbelianScheme.IsogenyQuotient.Kernel.Tuples.Construction.tupleKernel s (fun i => F i.succ))) = _
    rw [relativeParameter_product, ih]
    rfl

end

end OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Parameter.KernelProducts
