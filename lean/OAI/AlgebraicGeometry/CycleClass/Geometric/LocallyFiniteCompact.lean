import OAI.AlgebraicGeometry.CycleClass.Geometric.LocallyFiniteChains
import OAI.AlgebraicGeometry.CycleClass.Geometric.SingularChainSupport
import Mathlib.Topology.Compactness.LocallyFinite

/-! # Locally Finite Compact -/

namespace OAI.AlgebraicGeometry.CycleClass.Geometric.LocallyFiniteCompact.Cycles

noncomputable section

/-!
# Spatially locally finite chains on compact spaces

Local finiteness here concerns the images of nonzero simplices in the underlying
space. Compactness makes the entire coefficient support finite because every
singular simplex has nonempty image. The resulting equivalence is with the
actual degree modules of the ordinary singular chain complex.
-/

open Set Filter Function _root_.CategoryTheory _root_.CategoryTheory.Limits
open scoped _root_.Topology Simplicial

namespace SpatialSupport

variable {X ι : Type*} [TopologicalSpace X]
variable {R : Type*} [Semiring R]

/-- Finite coefficient support implies spatial local finiteness for any family
of images, without a compactness or separation assumption on the space. -/
theorem of_finiteSupport {image : ι → Set X} {c : ι → R}
    (hc : (support c).Finite) : LocallyFiniteChains.Cycles.SpatialSupport.IsLocallyFinite image c := by
  intro x
  refine ⟨univ, univ_mem, hc.subset ?_⟩
  rintro i ⟨y, ⟨hne, _⟩, _⟩
  exact hne

/-- On a compact space, a spatially locally finite family of nonempty indexed
images can have only finitely many nonzero coefficients. -/
theorem finite_support_of_compact [CompactSpace X] {image : ι → Set X}
    (hne : ∀ i, (image i).Nonempty) {c : ι → R}
    (hc : LocallyFiniteChains.Cycles.SpatialSupport.IsLocallyFinite image c) : (support c).Finite := by
  have hfin := LocallyFinite.finite_nonempty_of_compact hc
  apply hfin.subset
  intro i hi
  obtain ⟨x, hx⟩ := hne i
  exact ⟨x, hi, hx⟩

/-- Finite chains include canonically into spatially locally finite chains. -/
def ofFinsupp (image : ι → Set X) : (ι →₀ R) →ₗ[R] LocallyFiniteChains.Cycles.SpatialSupport.module R image where
  toFun c := ⟨c, of_finiteSupport c.hasFiniteSupport⟩
  map_add' c d := by
    apply Subtype.ext
    funext i
    rfl
  map_smul' r c := by
    apply Subtype.ext
    funext i
    rfl

@[simp]
theorem ofFinsupp_apply (image : ι → Set X) (c : ι →₀ R) (i : ι) :
    ofFinsupp image c i = c i := rfl

theorem ofFinsupp_injective (image : ι → Set X) :
    Function.Injective (ofFinsupp (R := R) image) := by
  intro c d h
  apply Finsupp.ext
  intro i
  exact congrArg (fun z : LocallyFiniteChains.Cycles.SpatialSupport.module R image => z i) h

/-- On a compact space the coefficient-preserving inclusion is an equivalence,
provided the indexed geometric images are nonempty. -/
def equivFinsupp [CompactSpace X] (image : ι → Set X)
    (hne : ∀ i, (image i).Nonempty) : LocallyFiniteChains.Cycles.SpatialSupport.module R image ≃ₗ[R] (ι →₀ R) where
  toFun c := Finsupp.ofSupportFinite (c : ι → R)
    (finite_support_of_compact hne c.property)
  invFun c := ofFinsupp image c
  left_inv c := by
    apply Subtype.ext
    funext i
    rfl
  right_inv c := by
    apply Finsupp.ext
    intro i
    rfl
  map_add' c d := by
    apply Finsupp.ext
    intro i
    rfl
  map_smul' r c := by
    apply Finsupp.ext
    intro i
    rfl

@[simp]
theorem equivFinsupp_apply [CompactSpace X] (image : ι → Set X)
    (hne : ∀ i, (image i).Nonempty) (c : LocallyFiniteChains.Cycles.SpatialSupport.module R image) (i : ι) :
    equivFinsupp image hne c i = c i := rfl

@[simp]
theorem equivFinsupp_symm_apply [CompactSpace X] (image : ι → Set X)
    (hne : ∀ i, (image i).Nonempty) (c : ι →₀ R) (i : ι) :
    (equivFinsupp image hne).symm c i = c i := rfl

end SpatialSupport

/-- A spatially locally finite singular chain in a compact space has finite
support on the actual singular-simplex indexing set. -/
theorem locallyFiniteSingularChains_finite_support {R : Type*} [Semiring R]
    (X : TopCat.{0}) [CompactSpace X] (n : ℕ)
    (c : LocallyFiniteChains.Cycles.LocallyFiniteSingularChains R X n) :
    (support (c : (TopCat.toSSet.obj X).obj (.op ⦋n⦌) → R)).Finite :=
  SpatialSupport.finite_support_of_compact (LocallyFiniteChains.Cycles.singularSimplexImage_nonempty X n) c.property

/-- Coefficient-preserving equivalence of spatially locally finite and finitely
supported singular coefficients on a compact space. -/
def locallyFiniteSingularCoefficientsEquiv (R : Type*) [Semiring R]
    (X : TopCat.{0}) [CompactSpace X] (n : ℕ) :
    LocallyFiniteChains.Cycles.LocallyFiniteSingularChains R X n ≃ₗ[R]
      ((TopCat.toSSet.obj X).obj (.op ⦋n⦌) →₀ R) :=
  SpatialSupport.equivFinsupp (LocallyFiniteChains.Cycles.singularSimplexImage X n) (LocallyFiniteChains.Cycles.singularSimplexImage_nonempty X n)

/-- The standard coproduct description identifies an ordinary singular chain
degree with finitely supported coefficients on genuine singular simplices. -/
def ordinarySingularChainCoefficients (R : Type) [CommRing R]
    (X : TopCat.{0}) (n : ℕ) :
    ((TopCat.toSSet.obj X).chainComplex (ModuleCat.of R R)).X n ≃ₗ[R]
      ((TopCat.toSSet.obj X).obj (.op ⦋n⦌) →₀ R) :=
  (((TopCat.toSSet.obj X).isColimitChainComplexXCofan (ModuleCat.of R R) n).coconePointUniqueUpToIso
      (ModuleCat.finsuppCoconeIsColimit R R
        ((TopCat.toSSet.obj X).obj (.op ⦋n⦌)))).toLinearEquiv

/-- The canonical inclusion of ordinary singular chains into spatially locally
finite chains is defined for every space. -/
def ordinaryToLocallyFinite (R : Type) [CommRing R] (X : TopCat.{0}) (n : ℕ) :
    ((TopCat.toSSet.obj X).chainComplex (ModuleCat.of R R)).X n →ₗ[R]
      LocallyFiniteChains.Cycles.LocallyFiniteSingularChains R X n :=
  (SpatialSupport.ofFinsupp (LocallyFiniteChains.Cycles.singularSimplexImage X n)).comp
    (ordinarySingularChainCoefficients R X n).toLinearMap

/-- Compact spaces have exactly the same ordinary and spatially locally finite
singular chains, degree by degree, with the canonical coefficient identification. -/
def locallyFiniteOrdinaryEquiv (R : Type) [CommRing R]
    (X : TopCat.{0}) [CompactSpace X] (n : ℕ) :
    LocallyFiniteChains.Cycles.LocallyFiniteSingularChains R X n ≃ₗ[R]
      ((TopCat.toSSet.obj X).chainComplex (ModuleCat.of R R)).X n :=
  (locallyFiniteSingularCoefficientsEquiv R X n).trans
    (ordinarySingularChainCoefficients R X n).symm

/-- The inverse of the compact-space equivalence is precisely the canonical
ordinary-chain inclusion already defined without compactness. -/
theorem locallyFiniteOrdinaryEquiv_symm (R : Type) [CommRing R]
    (X : TopCat.{0}) [CompactSpace X] (n : ℕ) :
    (locallyFiniteOrdinaryEquiv R X n).symm.toLinearMap =
      ordinaryToLocallyFinite R X n := by
  apply LinearMap.ext
  intro c
  apply Subtype.ext
  funext σ
  rfl

/-- Specialization to the existing ordinary integral singular-chain complex. -/
def locallyFiniteIntegralOrdinaryEquiv (X : TopCat.{0}) [CompactSpace X] (n : ℕ) :
    LocallyFiniteChains.Cycles.LocallyFiniteSingularChains ℤ X n ≃ₗ[ℤ] (LocalHomology.Cycles.integralSingularChains X).X n :=
  locallyFiniteOrdinaryEquiv ℤ X n

end

end OAI.AlgebraicGeometry.CycleClass.Geometric.LocallyFiniteCompact.Cycles
