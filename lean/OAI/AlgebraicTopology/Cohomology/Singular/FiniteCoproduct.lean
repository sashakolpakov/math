import OAI.Geometry.Foundations.ConvexStdSimplexMetric
import OAI.AlgebraicTopology.Cohomology.Singular.IndexedProduct
import OAI.AlgebraicTopology.Cohomology.Singular.ContinuousFormulas
import OAI.AlgebraicTopology.Cohomology.Singular.RationalComplex
import Mathlib.Topology.Connected.Clopen
import Mathlib.Topology.Category.TopCat.Limits.Products

/-! # Finite Coproduct -/

namespace OAI.AlgebraicTopology.Cohomology.Singular.FiniteCoproduct

noncomputable section

/-!
# Singular cohomology of disjoint unions

A continuous singular simplex lies in a unique summand of a topological
disjoint union, because its standard simplex domain is connected. Hence
actual singular cochains identify with the product of the summands' cochain
complexes. The resulting cohomology equivalence is given by pullback along
the genuine inclusions and respects change of coefficients. The proof works
for any small index type, and in particular for finite disjoint unions.
-/

open scoped OAI.Geometry.Foundations.ConvexStdSimplexMetric.Convexity.StdSimplex

open _root_.CategoryTheory _root_.CategoryTheory.Limits Opposite
open scoped Simplicial

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

variable {I : Type} (X : I → TopCat.{0})

/-- The native singular-simplex map from the disjoint union of the summands'
simplex sets to the simplex set of the topological disjoint union. -/
def singularSigmaSimplexMap (n : ℕ) :
    (Σ i, Basic.singularSimplices (X i) n) → Basic.singularSimplices (TopCat.of (Σ i, X i)) n :=
  fun s => (TopCat.toSSet.map (TopCat.sigmaι X s.1)).app (op ⦋n⦌) s.2

theorem singularSigmaSimplexMap_injective (n : ℕ) :
    Function.Injective (singularSigmaSimplexMap X n) := by
  rintro ⟨i, s⟩ ⟨j, t⟩ h
  let z := Classical.choice (inferInstance : Nonempty (Convexity.StdSimplex ℝ (Fin (n + 1))))
  have hij : i = j := congrArg (fun u : Basic.singularSimplices (TopCat.of (Σ i, X i)) n =>
    (Coefficients.singularSimplicesEquivContinuousMap (TopCat.of (Σ i, X i)) n u z).1) h
  subst j
  apply congrArg (Sigma.mk i)
  apply (Coefficients.singularSimplicesEquivContinuousMap (X i) n).injective
  ext w
  exact (@sigma_mk_injective I (fun i => X i) i) (congrArg
    (fun u : Basic.singularSimplices (TopCat.of (Σ i, X i)) n =>
      Coefficients.singularSimplicesEquivContinuousMap (TopCat.of (Σ i, X i)) n u w) h)

/-- Connectedness of the standard simplex forces a singular simplex to lie
in one summand. -/
theorem singularSigmaSimplexMap_surjective (n : ℕ) :
    Function.Surjective (singularSigmaSimplexMap X n) := by
  intro s
  obtain ⟨i, f, hf, hs⟩ :=
    (Coefficients.singularSimplicesEquivContinuousMap (TopCat.of (Σ i, X i)) n s).continuous.exists_lift_sigma
  refine ⟨⟨i, (Coefficients.singularSimplicesEquivContinuousMap (X i) n).symm ⟨f, hf⟩⟩, ?_⟩
  apply (Coefficients.singularSimplicesEquivContinuousMap (TopCat.of (Σ i, X i)) n).injective
  apply ContinuousMap.ext
  intro z
  change @Sigma.mk I (fun i => X i) i
    (Coefficients.singularSimplicesEquivContinuousMap (X i) n
      ((Coefficients.singularSimplicesEquivContinuousMap (X i) n).symm ⟨f, hf⟩) z) = _
  rw [Equiv.apply_symm_apply]
  exact (congrFun hs z).symm

/-- Singular simplices of the disjoint union are precisely the disjoint
union of the singular simplices of its summands. -/
def singularSigmaSimplexEquiv (n : ℕ) :
    (Σ i, Basic.singularSimplices (X i) n) ≃ Basic.singularSimplices (TopCat.of (Σ i, X i)) n :=
  Equiv.ofBijective (singularSigmaSimplexMap X n)
    ⟨singularSigmaSimplexMap_injective X n, singularSigmaSimplexMap_surjective X n⟩

variable {R : Type} [Ring R] (M : ModuleCat.{0} R)

/-- Restriction of functions on singular simplices to the summands. -/
def singularSigmaFunctionEquiv (n : ℕ) :
    (Basic.singularSimplices (TopCat.of (Σ i, X i)) n → M) ≃ₗ[R]
      (∀ i, Basic.singularSimplices (X i) n → M) where
  toFun f i s := f (singularSigmaSimplexMap X n ⟨i, s⟩)
  invFun f s :=
    let t := (singularSigmaSimplexEquiv X n).symm s
    f t.1 t.2
  left_inv f := by
    funext s
    exact congrArg f ((singularSigmaSimplexEquiv X n).apply_symm_apply s)
  right_inv f := by
    funext i s
    change (fun t : Σ j, Basic.singularSimplices (X j) n => f t.1 t.2)
      ((singularSigmaSimplexEquiv X n).symm ((singularSigmaSimplexEquiv X n) ⟨i, s⟩)) = _
    rw [Equiv.symm_apply_apply]
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- The actual degreewise singular-cochain equivalence for a disjoint union. -/
def singularSigmaCochainEquiv (n : ℕ) :
    (Basic.singularCochains M (TopCat.of (Σ i, X i))).X n ≃ₗ[R]
      (∀ i, (Basic.singularCochains M (X i)).X n) :=
  (Coefficients.singularDegreewiseFunctionIso M (TopCat.of (Σ i, X i)) n).toLinearEquiv.trans
    ((singularSigmaFunctionEquiv X M n).trans
      (LinearEquiv.piCongrRight fun i => (Coefficients.singularDegreewiseFunctionIso M (X i) n).symm.toLinearEquiv))

/-- Each coordinate of the cochain equivalence is actual singular pullback. -/
theorem singularSigmaCochainEquiv_apply (n : ℕ)
    (c : (Basic.singularCochains M (TopCat.of (Σ i, X i))).X n) (i : I) :
    singularSigmaCochainEquiv X M n c i = (Functor.singularPullback M (TopCat.sigmaι X i)).f n c := by
  apply (Coefficients.singularDegreewiseFunctionIso M (X i) n).toLinearEquiv.injective
  change (Coefficients.singularDegreewiseFunctionIso M (X i) n).hom _ =
    (Coefficients.singularDegreewiseFunctionIso M (X i) n).hom _
  funext s
  change (Coefficients.singularDegreewiseFunctionIso M (X i) n).hom
    ((Coefficients.singularDegreewiseFunctionIso M (X i) n).inv _) s = _
  rw [Iso.inv_hom_id_apply]
  exact (Formulas.degreewiseFunctionIso_pullback M (TopCat.toSSet.map (TopCat.sigmaι X i)) c s).symm

/-- The singular cochain complex of an actual disjoint union is canonically
the product of the summands' cochain complexes. -/
def singularSigmaCochainIso :
    Basic.singularCochains M (TopCat.of (Σ i, X i)) ≅
      OAI.Topology.Euclidean.ProductComplexes.Globalization.indexedProductComplex R (fun i => Basic.singularCochains M (X i)) :=
  HomologicalComplex.Hom.isoOfComponents
    (fun n => (singularSigmaCochainEquiv X M n).toModuleIso) (by
      intro p q _
      apply ModuleCat.hom_ext
      apply LinearMap.ext
      intro c
      funext i
      change (Basic.singularCochains M (X i)).d p q (singularSigmaCochainEquiv X M p c i) =
        singularSigmaCochainEquiv X M q ((Basic.singularCochains M (TopCat.of (Σ i, X i))).d p q c) i
      rw [singularSigmaCochainEquiv_apply, singularSigmaCochainEquiv_apply]
      exact ConcreteCategory.congr_hom ((Functor.singularPullback M (TopCat.sigmaι X i)).comm p q) c)

@[reassoc (attr := simp)]
theorem singularSigmaCochainIso_projection (i : I) :
    (singularSigmaCochainIso X M).hom ≫
        IndexedProduct.indexedProductProjection R (fun j => Basic.singularCochains M (X j)) i =
      Functor.singularPullback M (TopCat.sigmaι X i) := by
  apply HomologicalComplex.Hom.ext
  funext n
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro c
  exact singularSigmaCochainEquiv_apply X M n c i

/-- Actual singular cohomology of a disjoint union is the product of the
summands' singular cohomology, in every degree. -/
def singularSigmaCohomologyEquiv (n : ℕ) :
    Basic.singularCohomology M (TopCat.of (Σ i, X i)) n ≃ₗ[R]
      (∀ i, Basic.singularCohomology M (X i) n) :=
  ((HomologicalComplex.homologyFunctor (ModuleCat.{0} R) (ComplexShape.up ℕ) n).mapIso
    (singularSigmaCochainIso X M)).toLinearEquiv.trans
      (IndexedProduct.indexedProductCohomologyEquiv R (fun i => Basic.singularCochains M (X i)) n)

/-- The cohomology equivalence is pullback along the actual inclusions. -/
theorem singularSigmaCohomologyEquiv_apply (n : ℕ)
    (c : Basic.singularCohomology M (TopCat.of (Σ i, X i)) n) (i : I) :
    singularSigmaCohomologyEquiv X M n c i =
      Functor.singularCohomologyPullback M (TopCat.sigmaι X i) n c := by
  change IndexedProduct.indexedProductCohomologyEquiv R (fun j => Basic.singularCochains M (X j)) n
    (HomologicalComplex.homologyMap (singularSigmaCochainIso X M).hom n c) i = _
  rw [IndexedProduct.indexedProductCohomologyEquiv_apply]
  have h := congrArg (fun f => HomologicalComplex.homologyMap f n)
    (singularSigmaCochainIso_projection X M i)
  rw [HomologicalComplex.homologyMap_comp] at h
  exact ConcreteCategory.congr_hom h c

/-- Disjoint-union cohomology commutes with any linear change of coefficients. -/
theorem singularSigmaCohomologyEquiv_coefficientMap {N : ModuleCat.{0} R}
    (f : M ⟶ N) (n : ℕ) (c : Basic.singularCohomology M (TopCat.of (Σ i, X i)) n) (i : I) :
    singularSigmaCohomologyEquiv X N n (Coefficients.coefficientMap f (TopCat.of (Σ i, X i)) n c) i =
      Coefficients.coefficientMap f (X i) n (singularSigmaCohomologyEquiv X M n c i) := by
  rw [singularSigmaCohomologyEquiv_apply, singularSigmaCohomologyEquiv_apply]
  exact (ConcreteCategory.congr_hom (Functor.coefficientMap_naturality f (TopCat.sigmaι X i) n) c).symm

/-- The canonical rational-to-complex cohomology inclusion respects the
disjoint-union decomposition into actual component cohomology groups. -/
theorem singularSigmaCohomologyEquiv_rationalToComplex (n : ℕ)
    (c : Basic.singularCohomology (ModuleCat.of ℚ ℚ) (TopCat.of (Σ i, X i)) n) (i : I) :
    singularSigmaCohomologyEquiv X (ModuleCat.of ℂ ℂ) n
        (RationalComplex.rationalToComplexCohomology (TopCat.of (Σ i, X i)) n c) i =
      RationalComplex.rationalToComplexCohomology (X i) n
        (singularSigmaCohomologyEquiv X (ModuleCat.of ℚ ℚ) n c i) := by
  rw [singularSigmaCohomologyEquiv_apply, singularSigmaCohomologyEquiv_apply]
  exact (ConcreteCategory.congr_hom
    (RationalComplex.rationalToComplexCohomology_naturality (TopCat.sigmaι X i) n) c).symm

/-- Singular cohomology of mathlib's categorical topological coproduct is
the product of the component cohomology modules. This includes every finite
topological coproduct. -/
def singularCoproductCohomologyEquiv (n : ℕ) :
    Basic.singularCohomology M (∐ X) n ≃ₗ[R] (∀ i, Basic.singularCohomology M (X i) n) :=
  ((Functor.singularCohomologyFunctor M n).mapIso (TopCat.sigmaIsoSigma X).op.symm).toLinearEquiv.trans
    (singularSigmaCohomologyEquiv X M n)

/-- The coproduct cohomology equivalence is induced by the actual categorical
coproduct inclusions. -/
theorem singularCoproductCohomologyEquiv_apply (n : ℕ)
    (c : Basic.singularCohomology M (∐ X) n) (i : I) :
    singularCoproductCohomologyEquiv X M n c i =
      Functor.singularCohomologyPullback M (Sigma.ι X i) n c := by
  change singularSigmaCohomologyEquiv X M n
    (Functor.singularCohomologyPullback M (TopCat.sigmaIsoSigma X).inv n c) i = _
  rw [singularSigmaCohomologyEquiv_apply]
  have hi : TopCat.sigmaι X i ≫ (TopCat.sigmaIsoSigma X).inv = Sigma.ι X i := by
    rw [← TopCat.sigmaIsoSigma_hom_ι X i, Category.assoc, Iso.hom_inv_id, Category.comp_id]
  have hp : Functor.singularCohomologyPullback M (TopCat.sigmaIsoSigma X).inv n ≫
      Functor.singularCohomologyPullback M (TopCat.sigmaι X i) n =
      Functor.singularCohomologyPullback M (Sigma.ι X i) n := by
    rw [← Functor.singularCohomologyPullback_comp, hi]
  exact ConcreteCategory.congr_hom hp c

/-- The canonical categorical-coproduct decomposition respects any linear
change of coefficients. -/
theorem singularCoproductCohomologyEquiv_coefficientMap {N : ModuleCat.{0} R}
    (f : M ⟶ N) (n : ℕ) (c : Basic.singularCohomology M (∐ X) n) (i : I) :
    singularCoproductCohomologyEquiv X N n (Coefficients.coefficientMap f (∐ X) n c) i =
      Coefficients.coefficientMap f (X i) n (singularCoproductCohomologyEquiv X M n c i) := by
  rw [singularCoproductCohomologyEquiv_apply, singularCoproductCohomologyEquiv_apply]
  exact (ConcreteCategory.congr_hom (Functor.coefficientMap_naturality f (Sigma.ι X i) n) c).symm

/-- The ordinary rational-to-complex coefficient inclusion acts componentwise
under the genuine topological-coproduct cohomology decomposition. -/
theorem singularCoproductCohomologyEquiv_rationalToComplex (n : ℕ)
    (c : Basic.singularCohomology (ModuleCat.of ℚ ℚ) (∐ X) n) (i : I) :
    singularCoproductCohomologyEquiv X (ModuleCat.of ℂ ℂ) n
        (RationalComplex.rationalToComplexCohomology (∐ X) n c) i =
      RationalComplex.rationalToComplexCohomology (X i) n
        (singularCoproductCohomologyEquiv X (ModuleCat.of ℚ ℚ) n c i) := by
  rw [singularCoproductCohomologyEquiv_apply, singularCoproductCohomologyEquiv_apply]
  exact (ConcreteCategory.congr_hom
    (RationalComplex.rationalToComplexCohomology_naturality (Sigma.ι X i) n) c).symm

end

end OAI.AlgebraicTopology.Cohomology.Singular.FiniteCoproduct
