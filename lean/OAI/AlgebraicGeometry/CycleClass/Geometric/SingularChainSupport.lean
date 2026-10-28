import OAI.Geometry.Foundations.ConvexStdSimplexMetric
import OAI.AlgebraicGeometry.CycleClass.Geometric.LocalHomology
import OAI.AlgebraicGeometry.CycleClass.Geometric.SmallSimplex

/-! # Singular Chain Support -/

namespace OAI.AlgebraicGeometry.CycleClass.Geometric.SingularChainSupport.Cycles

noncomputable section

/-!
# Finite support of genuine integral singular chains

The degreewise coproduct in mathlib's singular chain complex is canonically
identified with finitely supported integer functions on the actual continuous
singular simplices. The finite-family Lebesgue argument then applies to every
element of the genuine chain complex.
-/

open scoped OAI.Geometry.Foundations.ConvexStdSimplexMetric.Convexity.StdSimplex

open _root_.CategoryTheory _root_.CategoryTheory.Limits
open scoped Simplicial

/-- The canonical finite-support description of genuine singular chains. -/
def singularChainDegreeFinsuppIso (X : TopCat.{0}) (n : ℕ) :
    (LocalHomology.Cycles.integralSingularChains X).X n ≅
      ModuleCat.of ℤ (((TopCat.toSSet.obj X).obj (.op ⦋n⦌)) →₀ ℤ) :=
  ((TopCat.toSSet.obj X).isColimitChainComplexXCofan (ModuleCat.of ℤ ℤ) n).coconePointUniqueUpToIso
      (ModuleCat.finsuppCoconeIsColimit ℤ ℤ ((TopCat.toSSet.obj X).obj (.op ⦋n⦌)))

/-- Coefficients of a genuine singular chain in its simplex basis. -/
def singularChainCoefficients (X : TopCat.{0}) (n : ℕ) :
    (LocalHomology.Cycles.integralSingularChains X).X n ≃ₗ[ℤ]
      (((TopCat.toSSet.obj X).obj (.op ⦋n⦌)) →₀ ℤ) :=
  (singularChainDegreeFinsuppIso X n).toLinearEquiv

/-- The coefficient description sends the actual simplex summand to the
corresponding finitely supported singleton. -/
@[reassoc (attr := simp)]
theorem singularChainCoefficients_simplex (X : TopCat.{0}) (n : ℕ)
    (σ : (TopCat.toSSet.obj X).obj (.op ⦋n⦌)) :
    (TopCat.toSSet.obj X).ιChainComplex (R := ModuleCat.of ℤ ℤ) σ ≫
      (singularChainDegreeFinsuppIso X n).hom =
        ModuleCat.ofHom (Finsupp.lsingle σ (R := ℤ) (M := ModuleCat.of ℤ ℤ)) :=
  ((TopCat.toSSet.obj X).isColimitChainComplexXCofan (ModuleCat.of ℤ ℤ) n).comp_coconePointUniqueUpToIso_hom
      (ModuleCat.finsuppCoconeIsColimit ℤ ℤ ((TopCat.toSSet.obj X).obj (.op ⦋n⦌)))
      (Discrete.mk σ)

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- Elementwise form of the canonical simplex coefficient formula. -/
@[simp]
theorem singularChainCoefficients_simplex_apply (X : TopCat.{0}) (n : ℕ)
    (σ : (TopCat.toSSet.obj X).obj (.op ⦋n⦌)) (a : ℤ) :
    singularChainCoefficients X n
      ((TopCat.toSSet.obj X).ιChainComplex (R := ModuleCat.of ℤ ℤ) σ a) =
        Finsupp.single σ a := by
  change (singularChainDegreeFinsuppIso X n).hom.hom
    (((TopCat.toSSet.obj X).ιChainComplex (R := ModuleCat.of ℤ ℤ) σ).hom a) = _
  simpa only [ModuleCat.hom_comp, LinearMap.comp_apply,
    ModuleCat.hom_ofHom, Finsupp.lsingle_apply] using!
      congrArg (fun f : ModuleCat.of ℤ ℤ ⟶
        ModuleCat.of ℤ (((TopCat.toSSet.obj X).obj (.op ⦋n⦌)) →₀ ℤ) ↦ f.hom a)
        (singularChainCoefficients_simplex X n σ)

/-- The finite set of simplices occurring with nonzero coefficient. -/
def singularChainSupport {X : TopCat.{0}} {n : ℕ}
    (c : (LocalHomology.Cycles.integralSingularChains X).X n) :
    Finset ((TopCat.toSSet.obj X).obj (.op ⦋n⦌)) :=
  (singularChainCoefficients X n c).support

@[simp]
theorem singularChainCoefficients_eq_zero_iff {X : TopCat.{0}} {n : ℕ}
    (c : (LocalHomology.Cycles.integralSingularChains X).X n) :
    singularChainCoefficients X n c = 0 ↔ c = 0 :=
  (singularChainCoefficients X n).map_eq_zero_iff

/-- One geometric refinement exponent works simultaneously on every simplex
in an actual chain. The input maps are real continuous subsimplices, and their
mesh estimate remains an explicit hypothesis to be proved by subdivision. -/
theorem singularChain_geometric_smallness {X : TopCat.{0}} {ι : Type}
    (U : ι → Set X) (hopen : ∀ i, IsOpen (U i))
    (hcover : ∀ x : X, ∃ i, x ∈ U i) {n : ℕ}
    (c : (LocalHomology.Cycles.integralSingularChains X).X n) {r : ℝ} (hr : r < 1) :
    ∃ N : ℕ, ∀ σ ∈ singularChainSupport c, ∀ (m : ℕ)
      (τ : C(Convexity.StdSimplex ℝ (Fin (m + 1)), Convexity.StdSimplex ℝ (Fin (n + 1)))),
      (∀ a b, dist (τ a) (τ b) ≤ r ^ N) →
      ∃ i, Set.range ((X.toSSetObjEquiv (.op ⦋n⦌) σ).comp τ) ⊆ U i := by
  classical
  let s := (singularChainSupport c).image (X.toSSetObjEquiv (.op ⦋n⦌))
  obtain ⟨N, hN⟩ := SmallSimplex.Cycles.singularSimplices_geometric_smallness U hopen hcover s hr
  refine ⟨N, ?_⟩
  intro σ hσ m τ hτ
  exact hN _ (Finset.mem_image.mpr ⟨σ, hσ, rfl⟩) m τ hτ

end

end OAI.AlgebraicGeometry.CycleClass.Geometric.SingularChainSupport.Cycles
