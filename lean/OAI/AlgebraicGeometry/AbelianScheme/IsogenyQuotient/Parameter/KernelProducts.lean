import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Parameter.SubgroupChoice
import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Kernel.Tuples

/-! # Kernel Products -/

namespace OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Parameter.KernelProducts.Construction

noncomputable section

/-! Actual parameter pullback preserves the products used to assemble
the full kernel. All equalities retain every test-scheme section. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj

attribute [local instance] PairingBaseChange.Construction.pulledbackGroup_commutative

theorem subgroupProduct_comap_mulEquiv {G H : Type*} [CommGroup G] [CommGroup H]
    (e : G ≃* H) (F J : Subgroup H) :
    (Kernel.Product.Construction.subgroupProduct F J).comap e.toMonoidHom =
      Kernel.Product.Construction.subgroupProduct (F.comap e.toMonoidHom) (J.comap e.toMonoidHom) := by
  ext x
  constructor
  · rintro ⟨a, ha, b, hb, hx⟩
    refine ⟨e.symm a, ?_, e.symm b, ?_, ?_⟩
    · change e (e.symm a) ∈ F
      exact (e.apply_symm_apply a).symm ▸ ha
    · change e (e.symm b) ∈ J
      exact (e.apply_symm_apply b).symm ▸ hb
    · apply e.injective
      rw [e.map_mul, e.apply_symm_apply, e.apply_symm_apply]
      exact hx
  · rintro ⟨a, ha, b, hb, rfl⟩
    exact ⟨e a, ha, e b, hb, e.map_mul a b⟩

variable {S : Scheme.{0}} (G : Grp (Over S)) (P : Over S) [IsCommMonObj G.X]

theorem relativeSubgroupOverParameter_trivial :
    Relative.ParameterBaseChange.Construction.relativeSubgroupOverParameter G P Kernel.Tuples.Construction.trivialRelativeSubgroup = Kernel.Tuples.Construction.trivialRelativeSubgroup := by
  ext U t x
  let e := (CartierDuality.CharacterBaseChange.Construction.Schemes.pullbackPointMulEquiv P.hom G U).symm
  change e x = 1 ↔ x = 1
  constructor
  · intro hx
    exact e.injective (hx.trans e.map_one.symm)
  · intro hx
    exact (congrArg e hx).trans e.map_one

set_option backward.isDefEq.respectTransparency false in
theorem relativeSubgroupOverParameter_product (F J : TorsionQuotient.SubgroupFunctor.RelativeSubgroup G.X P) :
    Relative.ParameterBaseChange.Construction.relativeSubgroupOverParameter G P (Kernel.Product.Construction.relativeKernelProduct F J) =
      Kernel.Product.Construction.relativeKernelProduct (Relative.ParameterBaseChange.Construction.relativeSubgroupOverParameter G P F) (Relative.ParameterBaseChange.Construction.relativeSubgroupOverParameter G P J) := by
  apply TorsionQuotient.SubgroupFunctor.RelativeSubgroup.ext
  funext U t
  let : IsCommMonObj ((Over.pullback P.hom).obj G.X) := PairingBaseChange.Construction.pulledbackGroup_commutative P.hom G
  exact subgroupProduct_comap_mulEquiv (CartierDuality.CharacterBaseChange.Construction.Schemes.pullbackPointMulEquiv P.hom G U).symm
    (F.points ((Over.map P.hom).obj U) (Relative.ParameterBaseChange.Construction.parameterBasePoint P U))
    (J.points ((Over.map P.hom).obj U) (Relative.ParameterBaseChange.Construction.parameterBasePoint P U))

theorem relativeSubgroupOverParameter_tuple (s : ℕ) (F : Fin s → TorsionQuotient.SubgroupFunctor.RelativeSubgroup G.X P) :
    Relative.ParameterBaseChange.Construction.relativeSubgroupOverParameter G P (Kernel.Tuples.Construction.tupleKernel s F) =
      Kernel.Tuples.Construction.tupleKernel s (fun i => Relative.ParameterBaseChange.Construction.relativeSubgroupOverParameter G P (F i)) := by
  induction s with
  | zero => exact relativeSubgroupOverParameter_trivial G P
  | succ s ih =>
      simp only [Kernel.Tuples.Construction.tupleKernel, relativeSubgroupOverParameter_product, ih]

end

end OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Parameter.KernelProducts.Construction
