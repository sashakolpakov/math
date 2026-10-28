import OAI.AlgebraicTopology.Products.CapBoundary
import OAI.AlgebraicGeometry.CycleClass.Geometric.LocalHomology
import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings

/-! # Integral Cap Coefficients -/

namespace OAI.AlgebraicTopology.Duality.Poincare.IntegralCapCoefficients

noncomputable section

/-!
# Integral coefficients and the finite mixed cap product

An actual finite integral simplicial chain is sent to the same linear
combination of scalar simplices. The map is built from the already proved
free-chain universal property and commutes with the actual differential.
The mixed cap product is the existing scalar cap product after this map.
-/

open _root_.CategoryTheory
open scoped Simplicial

open OAI.AlgebraicGeometry.CycleClass.Geometric.LocalHomology.Cycles OAI.AlgebraicTopology.Products.CapBoundary

variable {R : Type} [CommRing R]

private def integerLinearOfAdditive {M N : Type}
    [AddCommGroup M] [AddCommGroup N]
    {modM : Module ℤ M} {modN : Module ℤ N} (f : M →+ N) : M →ₗ[ℤ] N where
  toFun := f
  map_add' := f.map_add
  map_smul' r x := by
    change f (modM.smul r x) = modN.smul r (f x)
    simp only [int_smul_eq_zsmul, map_zsmul]

/-- Replace the integral coefficients of a finite simplicial chain by their
images in the scalar ring, keeping every actual simplex unchanged. -/
def integralToScalarSimplicial (K : SSet.{0}) (n : ℕ) :
    (Cohomology.Singular.ChainDual.simplicialScalarChains (R := ℤ) K).X n →ₗ[ℤ]
      (Cohomology.Singular.ChainDual.simplicialScalarChains (R := R) K).X n :=
  Cohomology.Singular.ChainDual.chainFunctionalOfFunction K
    (ModuleCat.of ℤ ((Cohomology.Singular.ChainDual.simplicialScalarChains (R := R) K).X n)) n
    (Cohomology.Singular.ChainDual.simplexChain (R := R) K)

@[simp]
theorem integralToScalarSimplicial_simplex (K : SSet.{0}) (n : ℕ) (s : K _⦋n⦌) :
    integralToScalarSimplicial (R := R) K n (Cohomology.Singular.ChainDual.simplexChain (R := ℤ) K s) =
      Cohomology.Singular.ChainDual.simplexChain (R := R) K s :=
  Cohomology.Singular.ChainDual.chainFunctionalOfFunction_simplex K _ n _ s

/-- Coefficient change commutes with every actual simplicial differential. -/
theorem integralToScalarSimplicial_d (K : SSet.{0}) (i j : ℕ)
    (z : (Cohomology.Singular.ChainDual.simplicialScalarChains (R := ℤ) K).X i) :
    integralToScalarSimplicial (R := R) K j
        ((Cohomology.Singular.ChainDual.simplicialScalarChains (R := ℤ) K).d i j z) =
      (Cohomology.Singular.ChainDual.simplicialScalarChains (R := R) K).d i j
        (integralToScalarSimplicial (R := R) K i z) := by
  by_cases hij : (ComplexShape.down ℕ).Rel i j
  · have hi : j + 1 = i := hij
    subst i
    have h : (integralToScalarSimplicial (R := R) K j).comp
        ((Cohomology.Singular.ChainDual.simplicialScalarChains (R := ℤ) K).d (j + 1) j).hom =
        (((Cohomology.Singular.ChainDual.simplicialScalarChains (R := R) K).d (j + 1) j).hom.restrictScalars ℤ).comp
          (integralToScalarSimplicial (R := R) K (j + 1)) := by
      apply Cohomology.Singular.ChainDual.chainFunctional_ext K (ModuleCat.of ℤ ((Cohomology.Singular.ChainDual.simplicialScalarChains (R := R) K).X j))
      intro s
      simp only [LinearMap.comp_apply, LinearMap.restrictScalars_apply,
        integralToScalarSimplicial_simplex, Cohomology.Singular.ChainDual.simplexChain_boundary, map_sum, map_zsmul]
    exact LinearMap.congr_fun h z
  · rw [(Cohomology.Singular.ChainDual.simplicialScalarChains (R := ℤ) K).shape i j hij,
      (Cohomology.Singular.ChainDual.simplicialScalarChains (R := R) K).shape i j hij]
    simp

/-- Coefficient change is natural for maps of simplicial sets. -/
theorem integralToScalarSimplicial_naturality {K L : SSet.{0}} (f : K ⟶ L)
    (n : ℕ) (z : (Cohomology.Singular.ChainDual.simplicialScalarChains (R := ℤ) K).X n) :
    (Cohomology.Singular.EvaluationNaturality.simplicialScalarChainMap (R := R) f).f n
        (integralToScalarSimplicial (R := R) K n z) =
      integralToScalarSimplicial (R := R) L n
        ((Cohomology.Singular.EvaluationNaturality.simplicialScalarChainMap (R := ℤ) f).f n z) := by
  have h : (((Cohomology.Singular.EvaluationNaturality.simplicialScalarChainMap (R := R) f).f n).hom.restrictScalars ℤ).comp
      (integralToScalarSimplicial (R := R) K n) =
      (integralToScalarSimplicial (R := R) L n).comp
        ((Cohomology.Singular.EvaluationNaturality.simplicialScalarChainMap (R := ℤ) f).f n).hom := by
    apply Cohomology.Singular.ChainDual.chainFunctional_ext K (ModuleCat.of ℤ ((Cohomology.Singular.ChainDual.simplicialScalarChains (R := R) L).X n))
    intro s
    simp only [LinearMap.comp_apply, LinearMap.restrictScalars_apply,
      integralToScalarSimplicial_simplex, Cohomology.Singular.EvaluationNaturality.simplicialScalarChainMap_simplex]
  exact LinearMap.congr_fun h z

@[simp]
theorem integralToScalarSimplicial_chainCast (K : SSet.{0}) {i j : ℕ} (h : i = j)
    (z : (Cohomology.Singular.ChainDual.simplicialScalarChains (R := ℤ) K).X i) :
    integralToScalarSimplicial (R := R) K j (Products.Cap.chainCast (R := ℤ) K h z) =
      Products.Cap.chainCast (R := R) K h (integralToScalarSimplicial (R := R) K i z) := by
  subst j
  rfl

/-- Bundle the same coefficient change as an actual chain map, viewing the
scalar chain complex as an integer-module complex by restriction of scalars. -/
def integralToScalarSimplicialChainMap (K : SSet.{0}) :
    Cohomology.Singular.ChainDual.simplicialScalarChains (R := ℤ) K ⟶
      ((ModuleCat.restrictScalars (Int.castRingHom R)).mapHomologicalComplex
        (ComplexShape.down ℕ)).obj (Cohomology.Singular.ChainDual.simplicialScalarChains (R := R) K) where
  f n := ModuleCat.ofHom (X := (Cohomology.Singular.ChainDual.simplicialScalarChains (R := ℤ) K).X n)
    (Y := (ModuleCat.restrictScalars (Int.castRingHom R)).obj
      ((Cohomology.Singular.ChainDual.simplicialScalarChains (R := R) K).X n))
    (integerLinearOfAdditive (integralToScalarSimplicial (R := R) K n).toAddMonoidHom)
  comm' := by
    intro i j _
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro z
    exact (integralToScalarSimplicial_d (R := R) K i j z).symm

@[simp]
theorem integralToScalarSimplicialChainMap_f_apply (K : SSet.{0}) (n : ℕ)
    (z : (Cohomology.Singular.ChainDual.simplicialScalarChains (R := ℤ) K).X n) :
    (integralToScalarSimplicialChainMap (R := R) K).f n z =
      integralToScalarSimplicial (R := R) K n z := rfl

/-- The genuine mixed cap product: scalar cochains cap finite integral
chains, producing finite scalar chains. -/
def mixedSimplicialCap (K : SSet.{0}) (p q : ℕ) :
    (Cohomology.Singular.Basic.simplicialCochains K (ModuleCat.of R R)).X p →ₗ[R]
      ((Cohomology.Singular.ChainDual.simplicialScalarChains (R := ℤ) K).X (p + q) →ₗ[ℤ]
        (Cohomology.Singular.ChainDual.simplicialScalarChains (R := R) K).X q) where
  toFun c := ((Products.Cap.cap (R := R) K p q c).restrictScalars ℤ).comp
    (integralToScalarSimplicial (R := R) K (p + q))
  map_add' c d := by
    apply LinearMap.ext
    intro z
    change Products.Cap.cap K p q (c + d) (integralToScalarSimplicial K (p + q) z) =
      Products.Cap.cap K p q c (integralToScalarSimplicial K (p + q) z) +
        Products.Cap.cap K p q d (integralToScalarSimplicial K (p + q) z)
    rw [map_add, LinearMap.add_apply]
  map_smul' r c := by
    apply LinearMap.ext
    intro z
    change Products.Cap.cap K p q (r • c) (integralToScalarSimplicial K (p + q) z) =
      r • Products.Cap.cap K p q c (integralToScalarSimplicial K (p + q) z)
    rw [map_smul, LinearMap.smul_apply]

@[simp]
theorem mixedSimplicialCap_apply (K : SSet.{0}) (p q : ℕ)
    (c : (Cohomology.Singular.Basic.simplicialCochains K (ModuleCat.of R R)).X p)
    (z : (Cohomology.Singular.ChainDual.simplicialScalarChains (R := ℤ) K).X (p + q)) :
    mixedSimplicialCap K p q c z =
      Products.Cap.cap K p q c (integralToScalarSimplicial K (p + q) z) := rfl

@[simp]
theorem mixedSimplicialCap_simplex (K : SSet.{0}) (p q : ℕ)
    (c : (Cohomology.Singular.Basic.simplicialCochains K (ModuleCat.of R R)).X p) (s : K _⦋p + q⦌) :
    mixedSimplicialCap K p q c (Cohomology.Singular.ChainDual.simplexChain (R := ℤ) K s) =
      Cohomology.Singular.Coefficients.simplicialEvaluation K (ModuleCat.of R R) (Products.SimplexFaceIdentities.frontFace K p q s) c •
        Cohomology.Singular.ChainDual.simplexChain (R := R) K (Products.SimplexFaceIdentities.backFace K p q s) := by
  rw [mixedSimplicialCap_apply, integralToScalarSimplicial_simplex, Products.Cap.cap_simplex]

theorem mixedSimplicialCap_naturality {K L : SSet.{0}} (f : K ⟶ L) (p q : ℕ)
    (c : (Cohomology.Singular.Basic.simplicialCochains L (ModuleCat.of R R)).X p)
    (z : (Cohomology.Singular.ChainDual.simplicialScalarChains (R := ℤ) K).X (p + q)) :
    (Cohomology.Singular.EvaluationNaturality.simplicialScalarChainMap (R := R) f).f q
        (mixedSimplicialCap K p q ((Cohomology.Singular.Functor.simplicialPullback (ModuleCat.of R R) f).f p c) z) =
      mixedSimplicialCap L p q c ((Cohomology.Singular.EvaluationNaturality.simplicialScalarChainMap (R := ℤ) f).f (p + q) z) := by
  simp only [mixedSimplicialCap_apply]
  rw [← integralToScalarSimplicial_naturality]
  exact LinearMap.congr_fun (Products.Cap.cap_naturality f p q c)
    (integralToScalarSimplicial K (p + q) z)

/-- The mixed signed boundary identity is inherited from the already proved
scalar cap identity and the coefficient chain-map relation. -/
theorem mixedSimplicialCap_boundary (K : SSet.{0}) (p q : ℕ)
    (c : (Cohomology.Singular.Basic.simplicialCochains K (ModuleCat.of R R)).X p)
    (z : (Cohomology.Singular.ChainDual.simplicialScalarChains (R := ℤ) K).X (p + q + 1)) :
    mixedSimplicialCap K p q c ((Cohomology.Singular.ChainDual.simplicialScalarChains (R := ℤ) K).d (p + q + 1) (p + q) z) =
      mixedSimplicialCap K (p + 1) q
        ((Cohomology.Singular.Basic.simplicialCochains K (ModuleCat.of R R)).d p (p + 1) c)
        (Products.Cap.chainCast (R := ℤ) K (by omega : p + q + 1 = (p + 1) + q) z) +
      ((-1 : ℤ) ^ p) • ((Cohomology.Singular.ChainDual.simplicialScalarChains (R := R) K).d (q + 1) q
        (mixedSimplicialCap K p (q + 1) c z)) := by
  simp only [mixedSimplicialCap_apply, integralToScalarSimplicial_d,
    integralToScalarSimplicial_chainCast]
  exact Products.CapBoundary.cap_boundary K p q c (integralToScalarSimplicial K (p + q + 1) z)

theorem boundary_mixedSimplicialCap (K : SSet.{0}) (p q : ℕ)
    (c : (Cohomology.Singular.Basic.simplicialCochains K (ModuleCat.of R R)).X p)
    (z : (Cohomology.Singular.ChainDual.simplicialScalarChains (R := ℤ) K).X (p + q + 1)) :
    (Cohomology.Singular.ChainDual.simplicialScalarChains (R := R) K).d (q + 1) q
        (mixedSimplicialCap K p (q + 1) c z) =
      ((-1 : ℤ) ^ p) •
        (mixedSimplicialCap K p q c
            ((Cohomology.Singular.ChainDual.simplicialScalarChains (R := ℤ) K).d (p + q + 1) (p + q) z) -
          mixedSimplicialCap K (p + 1) q
            ((Cohomology.Singular.Basic.simplicialCochains K (ModuleCat.of R R)).d p (p + 1) c)
            (Products.Cap.chainCast (R := ℤ) K (by omega : p + q + 1 = (p + 1) + q) z)) := by
  simp only [mixedSimplicialCap_apply, integralToScalarSimplicial_d,
    integralToScalarSimplicial_chainCast]
  exact Products.CapBoundary.boundary_cap K p q c (integralToScalarSimplicial K (p + q + 1) z)

/-- The actual coefficient change on finite integral singular chains. -/
abbrev integralToScalarSingular (X : TopCat.{0}) (n : ℕ) :
    (AlgebraicGeometry.CycleClass.Geometric.LocalHomology.Cycles.integralSingularChains X).X n →ₗ[ℤ] (Cohomology.Singular.Evaluation.singularScalarChains (R := R) X).X n :=
  integralToScalarSimplicial (TopCat.toSSet.obj X) n

/-- The genuine singular coefficient chain map, with its target scalars
restricted to the integers only for expressing the categorical arrow. -/
abbrev integralToScalarSingularChainMap (X : TopCat.{0}) :
    AlgebraicGeometry.CycleClass.Geometric.LocalHomology.Cycles.integralSingularChains X ⟶
      ((ModuleCat.restrictScalars (Int.castRingHom R)).mapHomologicalComplex
        (ComplexShape.down ℕ)).obj (Cohomology.Singular.Evaluation.singularScalarChains (R := R) X) :=
  integralToScalarSimplicialChainMap (TopCat.toSSet.obj X)

theorem integralToScalarSingular_d (X : TopCat.{0}) (i j : ℕ)
    (z : (AlgebraicGeometry.CycleClass.Geometric.LocalHomology.Cycles.integralSingularChains X).X i) :
    integralToScalarSingular (R := R) X j ((AlgebraicGeometry.CycleClass.Geometric.LocalHomology.Cycles.integralSingularChains X).d i j z) =
      (Cohomology.Singular.Evaluation.singularScalarChains (R := R) X).d i j (integralToScalarSingular (R := R) X i z) :=
  integralToScalarSimplicial_d (TopCat.toSSet.obj X) i j z

theorem integralToScalarSingular_naturality {X Y : TopCat.{0}} (f : X ⟶ Y)
    (n : ℕ) (z : (AlgebraicGeometry.CycleClass.Geometric.LocalHomology.Cycles.integralSingularChains X).X n) :
    (Cohomology.Singular.EvaluationNaturality.singularScalarChainMap (R := R) f).f n (integralToScalarSingular (R := R) X n z) =
      integralToScalarSingular (R := R) Y n ((AlgebraicGeometry.CycleClass.Geometric.LocalHomology.Cycles.integralSingularChainFunctor.map f).f n z) :=
  integralToScalarSimplicial_naturality (TopCat.toSSet.map f) n z

theorem integralToScalarSingularChainMap_naturality {X Y : TopCat.{0}} (f : X ⟶ Y) :
    AlgebraicGeometry.CycleClass.Geometric.LocalHomology.Cycles.integralSingularChainFunctor.map f ≫ integralToScalarSingularChainMap (R := R) Y =
      integralToScalarSingularChainMap (R := R) X ≫
        ((ModuleCat.restrictScalars (Int.castRingHom R)).mapHomologicalComplex
          (ComplexShape.down ℕ)).map (Cohomology.Singular.EvaluationNaturality.singularScalarChainMap (R := R) f) := by
  ext n : 1
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro z
  exact (integralToScalarSingular_naturality (R := R) f n z).symm

/-- Scalar singular cochains cap integral singular chains; in particular
`R = ℚ` gives the pairing needed for integral orientation classes. -/
abbrev mixedSingularCap (X : TopCat.{0}) (p q : ℕ) :
    (Cohomology.Singular.Basic.singularCochains (ModuleCat.of R R) X).X p →ₗ[R]
      ((AlgebraicGeometry.CycleClass.Geometric.LocalHomology.Cycles.integralSingularChains X).X (p + q) →ₗ[ℤ] (Cohomology.Singular.Evaluation.singularScalarChains (R := R) X).X q) :=
  mixedSimplicialCap (TopCat.toSSet.obj X) p q

@[simp]
theorem mixedSingularCap_apply (X : TopCat.{0}) (p q : ℕ)
    (c : (Cohomology.Singular.Basic.singularCochains (ModuleCat.of R R) X).X p)
    (z : (AlgebraicGeometry.CycleClass.Geometric.LocalHomology.Cycles.integralSingularChains X).X (p + q)) :
    mixedSingularCap X p q c z = Products.Cap.singularCap X p q c (integralToScalarSingular X (p + q) z) :=
  rfl

theorem mixedSingularCap_naturality {X Y : TopCat.{0}} (f : X ⟶ Y) (p q : ℕ)
    (c : (Cohomology.Singular.Basic.singularCochains (ModuleCat.of R R) Y).X p)
    (z : (AlgebraicGeometry.CycleClass.Geometric.LocalHomology.Cycles.integralSingularChains X).X (p + q)) :
    (Cohomology.Singular.EvaluationNaturality.singularScalarChainMap (R := R) f).f q
        (mixedSingularCap X p q ((Cohomology.Singular.Functor.singularPullback (ModuleCat.of R R) f).f p c) z) =
      mixedSingularCap Y p q c ((AlgebraicGeometry.CycleClass.Geometric.LocalHomology.Cycles.integralSingularChainFunctor.map f).f (p + q) z) :=
  mixedSimplicialCap_naturality (TopCat.toSSet.map f) p q c z

theorem mixedSingularCap_boundary (X : TopCat.{0}) (p q : ℕ)
    (c : (Cohomology.Singular.Basic.singularCochains (ModuleCat.of R R) X).X p)
    (z : (AlgebraicGeometry.CycleClass.Geometric.LocalHomology.Cycles.integralSingularChains X).X (p + q + 1)) :
    mixedSingularCap X p q c ((AlgebraicGeometry.CycleClass.Geometric.LocalHomology.Cycles.integralSingularChains X).d (p + q + 1) (p + q) z) =
      mixedSingularCap X (p + 1) q ((Cohomology.Singular.Basic.singularCochains (ModuleCat.of R R) X).d p (p + 1) c)
        (Products.Cap.chainCast (R := ℤ) (TopCat.toSSet.obj X)
          (by omega : p + q + 1 = (p + 1) + q) z) +
      ((-1 : ℤ) ^ p) • ((Cohomology.Singular.Evaluation.singularScalarChains (R := R) X).d (q + 1) q
        (mixedSingularCap X p (q + 1) c z)) :=
  mixedSimplicialCap_boundary (TopCat.toSSet.obj X) p q c z

theorem boundary_mixedSingularCap (X : TopCat.{0}) (p q : ℕ)
    (c : (Cohomology.Singular.Basic.singularCochains (ModuleCat.of R R) X).X p)
    (z : (AlgebraicGeometry.CycleClass.Geometric.LocalHomology.Cycles.integralSingularChains X).X (p + q + 1)) :
    (Cohomology.Singular.Evaluation.singularScalarChains (R := R) X).d (q + 1) q (mixedSingularCap X p (q + 1) c z) =
      ((-1 : ℤ) ^ p) •
        (mixedSingularCap X p q c ((AlgebraicGeometry.CycleClass.Geometric.LocalHomology.Cycles.integralSingularChains X).d (p + q + 1) (p + q) z) -
          mixedSingularCap X (p + 1) q ((Cohomology.Singular.Basic.singularCochains (ModuleCat.of R R) X).d p (p + 1) c)
            (Products.Cap.chainCast (R := ℤ) (TopCat.toSSet.obj X)
              (by omega : p + q + 1 = (p + 1) + q) z)) :=
  boundary_mixedSimplicialCap (TopCat.toSSet.obj X) p q c z

end

end OAI.AlgebraicTopology.Duality.Poincare.IntegralCapCoefficients
