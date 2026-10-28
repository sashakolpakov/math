import OAI.AlgebraicTopology.Cohomology.Singular.Formulas
import Mathlib.Algebra.Category.ModuleCat.Colimits
import Mathlib.LinearAlgebra.Span.Basic

/-! # Chain Dual -/

namespace OAI.AlgebraicTopology.Cohomology.Singular.ChainDual

noncomputable section

/-!
# Singular cochains as linear maps on singular chains

The genuine coproduct defining simplicial chains is freely generated over the
coefficient ring by the simplices. Its linear maps into a coefficient module are
therefore exactly the ordinary cochains. The equivalence below is compatible
with the actual alternating boundary and coboundary operators.
-/

open _root_.CategoryTheory _root_.CategoryTheory.Limits Opposite
open scoped Simplicial

variable {R : Type} [CommRing R]

/-- Simplicial chains with coefficients in the scalar ring itself. -/
abbrev simplicialScalarChains (K : SSet.{0}) : ChainComplex (ModuleCat.{0} R) ℕ :=
  K.chainComplex (ModuleCat.of R R)

/-- The chain consisting of one simplex with coefficient one. -/
def simplexChain (K : SSet.{0}) {n : ℕ} (s : K _⦋n⦌) :
    (simplicialScalarChains (R := R) K).X n :=
  K.ιChainComplex (R := ModuleCat.of R R) s 1

/-- Scalar-linear maps on simplicial chains are determined by their values on simplices. -/
theorem chainFunctional_ext (K : SSet.{0}) (M : ModuleCat.{0} R) {n : ℕ}
    {f g : (simplicialScalarChains (R := R) K).X n →ₗ[R] M}
    (h : ∀ s : K _⦋n⦌, f (simplexChain K s) = g (simplexChain K s)) : f = g := by
  have hfg : ModuleCat.ofHom f = ModuleCat.ofHom g := by
    apply SSet.chainComplex_hom_ext (X := K) (R := ModuleCat.of R R)
    intro s
    apply ModuleCat.hom_ext
    apply LinearMap.ext_ring
    exact h s
  exact congrArg ModuleCat.Hom.hom hfg

/-- Extend the values assigned to simplices uniquely and linearly to all chains. -/
def chainFunctionalOfFunction (K : SSet.{0}) (M : ModuleCat.{0} R) (n : ℕ)
    (v : K _⦋n⦌ → M) : (simplicialScalarChains (R := R) K).X n →ₗ[R] M :=
  (Sigma.desc (fun s : K _⦋n⦌ =>
    ModuleCat.ofHom (LinearMap.toSpanSingleton R M (v s)))).hom

@[simp]
theorem chainFunctionalOfFunction_simplex (K : SSet.{0}) (M : ModuleCat.{0} R)
    (n : ℕ) (v : K _⦋n⦌ → M) (s : K _⦋n⦌) :
    chainFunctionalOfFunction K M n v (simplexChain K s) = v s := by
  have h := Sigma.ι_comp_desc (fun t : K _⦋n⦌ =>
    (ModuleCat.ofHom (LinearMap.toSpanSingleton R M (v t)) :
      ModuleCat.of R R ⟶ M)) s
  have he := congrArg (fun f : ModuleCat.of R R ⟶ M => f.hom 1) h
  exact he.trans (LinearMap.toSpanSingleton_apply_one R M (v s))

/-- The universal property of the free scalar chain module, as a linear equivalence. -/
def functionChainFunctionalEquiv (K : SSet.{0}) (M : ModuleCat.{0} R) (n : ℕ) :
    (K _⦋n⦌ → M) ≃ₗ[R] ((simplicialScalarChains (R := R) K).X n →ₗ[R] M) where
  toFun := chainFunctionalOfFunction K M n
  invFun f s := f (simplexChain K s)
  left_inv v := by
    funext s
    exact chainFunctionalOfFunction_simplex K M n v s
  right_inv f := by
    apply chainFunctional_ext K M
    intro s
    exact chainFunctionalOfFunction_simplex K M n _ s
  map_add' v w := by
    apply chainFunctional_ext K M
    intro s
    simp only [chainFunctionalOfFunction_simplex, Pi.add_apply, LinearMap.add_apply]
  map_smul' r v := by
    apply chainFunctional_ext K M
    intro s
    simp only [chainFunctionalOfFunction_simplex, Pi.smul_apply, LinearMap.smul_apply,
      RingHom.id_apply]

/-- Genuine simplicial cochains are exactly coefficient-valued linear maps on
scalar simplicial chains. In particular scalar-valued cochains form their linear dual. -/
def degreewiseChainDualEquiv (K : SSet.{0}) (M : ModuleCat.{0} R) (n : ℕ) :
    (Singular.Basic.simplicialCochains K M).X n ≃ₗ[R]
      ((simplicialScalarChains (R := R) K).X n →ₗ[R] M) :=
  (Coefficients.degreewiseFunctionIso K M n).toLinearEquiv.trans (functionChainFunctionalEquiv K M n)

@[simp]
theorem degreewiseChainDualEquiv_simplex (K : SSet.{0}) (M : ModuleCat.{0} R)
    {n : ℕ} (c : (Singular.Basic.simplicialCochains K M).X n) (s : K _⦋n⦌) :
    degreewiseChainDualEquiv K M n c (simplexChain K s) =
      Coefficients.simplicialEvaluation K M s c := by
  change chainFunctionalOfFunction K M n ((Coefficients.degreewiseFunctionIso K M n).hom c)
    (simplexChain K s) = _
  rw [chainFunctionalOfFunction_simplex, Coefficients.degreewiseFunctionIso_hom_apply]

/-- The actual chain boundary of a simplex is its signed sum of faces. -/
theorem simplexChain_boundary (K : SSet.{0}) {n : ℕ} (s : K _⦋n + 1⦌) :
    (simplicialScalarChains (R := R) K).d (n + 1) n (simplexChain K s) =
      ∑ i : Fin (n + 2), ((-1 : ℤ) ^ i.val) • simplexChain (R := R) K (K.δ i s) := by
  have h := congrArg
    (fun f : ModuleCat.of R R ⟶ (simplicialScalarChains (R := R) K).X n => f.hom 1)
    (K.ιChainComplex_d (R := ModuleCat.of R R) s)
  simpa only [simplexChain, ModuleCat.hom_comp, LinearMap.comp_apply,
    ModuleCat.hom_sum, ModuleCat.hom_zsmul, LinearMap.sum_apply,
    LinearMap.smul_apply] using h

/-- Under chain-cochain duality, the cochain differential is precomposition
with the genuine chain boundary. -/
theorem degreewiseChainDualEquiv_coboundary (K : SSet.{0}) (M : ModuleCat.{0} R)
    {n : ℕ} (c : (Singular.Basic.simplicialCochains K M).X n) :
    degreewiseChainDualEquiv K M (n + 1) ((Singular.Basic.simplicialCochains K M).d n (n + 1) c) =
      (degreewiseChainDualEquiv K M n c).comp
        ((simplicialScalarChains (R := R) K).d (n + 1) n).hom := by
  apply chainFunctional_ext K M
  intro s
  simp only [degreewiseChainDualEquiv_simplex, LinearMap.comp_apply,
    simplexChain_boundary, map_sum, map_zsmul, Formulas.evaluation_coboundary_apply]

/-- Chain-cochain adjointness for arbitrary indices, including the zero maps
outside the shape of the complex. -/
theorem degreewiseChainDualEquiv_d (K : SSet.{0}) (M : ModuleCat.{0} R)
    (i j : ℕ) (c : (Singular.Basic.simplicialCochains K M).X i) :
    degreewiseChainDualEquiv K M j ((Singular.Basic.simplicialCochains K M).d i j c) =
      (degreewiseChainDualEquiv K M i c).comp
        ((simplicialScalarChains (R := R) K).d j i).hom := by
  by_cases hij : (ComplexShape.up ℕ).Rel i j
  · have hj : i + 1 = j := hij
    subst j
    exact degreewiseChainDualEquiv_coboundary K M c
  · have hji : ¬(ComplexShape.down ℕ).Rel j i := hij
    rw [(Singular.Basic.simplicialCochains K M).shape i j hij,
      (simplicialScalarChains (R := R) K).shape j i hji]
    simp

/-- Evaluation pairs the coboundary of a cochain with a chain in the same way as
it pairs the cochain with the boundary of that chain. -/
theorem chainCochainPairing_coboundary (K : SSet.{0}) (M : ModuleCat.{0} R)
    {n : ℕ} (c : (Singular.Basic.simplicialCochains K M).X n)
    (z : (simplicialScalarChains (R := R) K).X (n + 1)) :
    degreewiseChainDualEquiv K M (n + 1) ((Singular.Basic.simplicialCochains K M).d n (n + 1) c) z =
      degreewiseChainDualEquiv K M n c
        ((simplicialScalarChains (R := R) K).d (n + 1) n z) :=
  LinearMap.congr_fun (degreewiseChainDualEquiv_coboundary K M c) z

/-- The same chain-duality equivalence on genuine continuous singular simplices. -/
def singularDegreewiseChainDualEquiv (M : ModuleCat.{0} R) (X : TopCat.{0}) (n : ℕ) :
    (Singular.Basic.singularCochains M X).X n ≃ₗ[R]
      (((TopCat.toSSet.obj X).chainComplex (ModuleCat.of R R)).X n →ₗ[R] M) :=
  degreewiseChainDualEquiv (TopCat.toSSet.obj X) M n

end

end OAI.AlgebraicTopology.Cohomology.Singular.ChainDual
