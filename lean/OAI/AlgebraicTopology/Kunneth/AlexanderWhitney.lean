import OAI.AlgebraicTopology.Products.CapBoundary
import OAI.AlgebraicTopology.Kunneth.CohomologyTensorNe

/-! # Alexander Whitney -/

namespace OAI.AlgebraicTopology.Kunneth.AlexanderWhitney

noncomputable section

/-! The front/back Alexander–Whitney components and their boundary law. -/

set_option backward.isDefEq.respectTransparency false

open _root_.CategoryTheory _root_.CategoryTheory.MonoidalCategory
open OAI.AlgebraicTopology.Products.CapBoundary
open scoped Simplicial TensorProduct

namespace Construction.AlexanderWhitneyComponents

variable {k : Type} [Field k]

/-- Split a simplex into its front p-face and its back q-face. -/
def component (K : SSet.{0}) (p q : ℕ) :
    (Cohomology.Singular.ChainDual.simplicialScalarChains (R := k) K).X (p + q) →ₗ[k]
      ((Cohomology.Singular.ChainDual.simplicialScalarChains (R := k) K).X p ⊗[k]
        (Cohomology.Singular.ChainDual.simplicialScalarChains (R := k) K).X q) :=
  Cohomology.Singular.ChainDual.chainFunctionalOfFunction K
    (ModuleCat.of k ((Cohomology.Singular.ChainDual.simplicialScalarChains (R := k) K).X p ⊗[k]
      (Cohomology.Singular.ChainDual.simplicialScalarChains (R := k) K).X q)) (p + q)
    (fun s => Cohomology.Singular.ChainDual.simplexChain (R := k) K (Products.SimplexFaceIdentities.frontFace K p q s) ⊗ₜ[k]
      Cohomology.Singular.ChainDual.simplexChain (R := k) K (Products.SimplexFaceIdentities.backFace K p q s))

@[simp]
theorem component_simplex (K : SSet.{0}) (p q : ℕ) (s : K _⦋p + q⦌) :
    component (k := k) K p q (Cohomology.Singular.ChainDual.simplexChain (R := k) K s) =
      Cohomology.Singular.ChainDual.simplexChain (R := k) K (Products.SimplexFaceIdentities.frontFace K p q s) ⊗ₜ[k]
        Cohomology.Singular.ChainDual.simplexChain (R := k) K (Products.SimplexFaceIdentities.backFace K p q s) :=
  Cohomology.Singular.ChainDual.chainFunctionalOfFunction_simplex K _ (p + q) _ s

/-- The front/back chain map is adjoint to the actual cup product. -/
theorem cup_tensor_pairing (K : SSet.{0}) {M N : ModuleCat.{0} k} {p q : ℕ}
    (c : (Cohomology.Singular.Basic.simplicialCochains K M).X p) (d : (Cohomology.Singular.Basic.simplicialCochains K N).X q)
    (z : (Cohomology.Singular.ChainDual.simplicialScalarChains (R := k) K).X (p + q)) :
    Cohomology.Singular.ChainDual.degreewiseChainDualEquiv K (ModuleCat.of k (M ⊗[k] N)) (p + q)
      (Products.Cup.cupWith K (TensorProduct.mk k M N) c d) z =
      TensorProduct.map (Cohomology.Singular.ChainDual.degreewiseChainDualEquiv K M p c)
        (Cohomology.Singular.ChainDual.degreewiseChainDualEquiv K N q d) (component K p q z) := by
  have h : Cohomology.Singular.ChainDual.degreewiseChainDualEquiv K (ModuleCat.of k (M ⊗[k] N)) (p + q)
      (Products.Cup.cupWith K (TensorProduct.mk k M N) c d) =
      (TensorProduct.map (Cohomology.Singular.ChainDual.degreewiseChainDualEquiv K M p c)
        (Cohomology.Singular.ChainDual.degreewiseChainDualEquiv K N q d)).comp (component K p q) := by
    apply Cohomology.Singular.ChainDual.chainFunctional_ext K (ModuleCat.of k (M ⊗[k] N))
    intro s
    erw [Cohomology.Singular.ChainDual.degreewiseChainDualEquiv_simplex K (ModuleCat.of k (M ⊗[k] N))
      (Products.Cup.cupWith K (TensorProduct.mk k M N) c d) s,
      Products.Cup.evaluation_cupWith K (L := ModuleCat.of k (M ⊗[k] N))
        (TensorProduct.mk k M N) c d s]
    simp only [LinearMap.comp_apply, component_simplex, TensorProduct.map_tmul,
      Cohomology.Singular.ChainDual.degreewiseChainDualEquiv_simplex, TensorProduct.mk_apply]
  exact LinearMap.congr_fun h z

/-- The component boundary law follows from the proved cup-product Leibniz rule. -/
theorem component_boundary (K : SSet.{0}) (p q : ℕ)
    (z : (Cohomology.Singular.ChainDual.simplicialScalarChains (R := k) K).X (p + q + 1)) :
    component K p q ((Cohomology.Singular.ChainDual.simplicialScalarChains (R := k) K).d (p + q + 1) (p + q) z) =
      TensorProduct.map ((Cohomology.Singular.ChainDual.simplicialScalarChains (R := k) K).d (p + 1) p).hom LinearMap.id
        (component K (p + 1) q (Products.Cap.chainCast K (by omega : p + q + 1 = (p + 1) + q) z)) +
      (-1 : ℤ) ^ p •
        TensorProduct.map LinearMap.id ((Cohomology.Singular.ChainDual.simplicialScalarChains (R := k) K).d (q + 1) q).hom
          (component K p (q + 1) z) := by
  have h := congrArg
    (fun u : (Cohomology.Singular.Basic.simplicialCochains K
        (ModuleCat.of k ((Cohomology.Singular.ChainDual.simplicialScalarChains (R := k) K).X p ⊗[k]
          (Cohomology.Singular.ChainDual.simplicialScalarChains (R := k) K).X q))).X (p + q + 1) =>
      Cohomology.Singular.ChainDual.degreewiseChainDualEquiv K _ (p + q + 1) u z)
    (Products.Cup.cupWith_coboundary K
      (TensorProduct.mk k ((Cohomology.Singular.ChainDual.simplicialScalarChains (R := k) K).X p)
        ((Cohomology.Singular.ChainDual.simplicialScalarChains (R := k) K).X q))
      (Products.Cap.simplexCochain K p) (Products.Cap.simplexCochain K q))
  rw [Cohomology.Singular.ChainDual.chainCochainPairing_coboundary] at h
  simp only [map_add, map_zsmul, LinearMap.add_apply, LinearMap.smul_apply] at h
  have hcast := Products.CapBoundary.degreewiseChainDualEquiv_cochainCast_apply K
    (ModuleCat.of k ((Cohomology.Singular.ChainDual.simplicialScalarChains (R := k) K).X p ⊗[k]
      (Cohomology.Singular.ChainDual.simplicialScalarChains (R := k) K).X q))
    (by omega : (p + 1) + q = p + q + 1)
    (Products.Cup.cupWith K (TensorProduct.mk k ((Cohomology.Singular.ChainDual.simplicialScalarChains (R := k) K).X p)
        ((Cohomology.Singular.ChainDual.simplicialScalarChains (R := k) K).X q))
      ((Cohomology.Singular.Basic.simplicialCochains K ((Cohomology.Singular.ChainDual.simplicialScalarChains (R := k) K).X p)).d p (p + 1)
        (Products.Cap.simplexCochain K p)) (Products.Cap.simplexCochain K q)) z
  erw [hcast] at h
  erw [cup_tensor_pairing K (Products.Cap.simplexCochain K p) (Products.Cap.simplexCochain K q),
    cup_tensor_pairing K
      ((Cohomology.Singular.Basic.simplicialCochains K ((Cohomology.Singular.ChainDual.simplicialScalarChains (R := k) K).X p)).d p (p + 1)
        (Products.Cap.simplexCochain K p)) (Products.Cap.simplexCochain K q),
    cup_tensor_pairing K (Products.Cap.simplexCochain K p)
      ((Cohomology.Singular.Basic.simplicialCochains K ((Cohomology.Singular.ChainDual.simplicialScalarChains (R := k) K).X q)).d q (q + 1)
        (Products.Cap.simplexCochain K q))] at h
  simp only [Products.Cap.simplexCochain_dual, Products.Cap.simplexCochain_coboundary_dual, TensorProduct.map_id,
    LinearMap.id_apply] at h
  exact h

/-- Front/back splitting commutes with maps of simplicial sets. -/
theorem component_naturality {K L : SSet.{0}} (f : K ⟶ L) (p q : ℕ) :
    (component (k := k) L p q).comp ((Cohomology.Singular.EvaluationNaturality.simplicialScalarChainMap (R := k) f).f (p + q)).hom =
      (TensorProduct.map ((Cohomology.Singular.EvaluationNaturality.simplicialScalarChainMap (R := k) f).f p).hom
        ((Cohomology.Singular.EvaluationNaturality.simplicialScalarChainMap (R := k) f).f q).hom).comp (component K p q) := by
  apply Cohomology.Singular.ChainDual.chainFunctional_ext K (ModuleCat.of k
    ((Cohomology.Singular.ChainDual.simplicialScalarChains (R := k) L).X p ⊗[k] (Cohomology.Singular.ChainDual.simplicialScalarChains (R := k) L).X q))
  intro s
  simp only [LinearMap.comp_apply, Cohomology.Singular.EvaluationNaturality.simplicialScalarChainMap_simplex, component_simplex,
    TensorProduct.map_tmul, Products.SimplexFaceIdentities.frontFace_naturality, Products.SimplexFaceIdentities.backFace_naturality]

end Construction.AlexanderWhitneyComponents

end

end OAI.AlgebraicTopology.Kunneth.AlexanderWhitney
