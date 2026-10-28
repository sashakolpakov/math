import OAI.AlgebraicGeometry.CycleClass.Geometric.LocallyFiniteOperation
import OAI.AlgebraicGeometry.CycleClass.Geometric.LocallyFiniteComparison
import OAI.AlgebraicTopology.Products.CapBoundary

/-! # Locally Finite Cap -/

namespace OAI.AlgebraicGeometry.CycleClass.Geometric.LocallyFiniteCap.Cycles

noncomputable section

section

/-!
# Cap products with spatially locally finite chains

The ordinary Alexander--Whitney cap formula extends to locally finite chains
because the retained back face has image inside the original simplex. Each
output coefficient is a proved finite sum. This construction works over any
commutative coefficient ring, including both integers and rationals.
-/

open _root_.CategoryTheory
open scoped Simplicial BigOperators
open OAI.AlgebraicTopology.Products.CapBoundary

variable {R : Type} [CommRing R] (X : TopCat.{0})

/-- The face retained by the cap product stays in the original geometric simplex. -/
theorem singularBackFaceImage_subset (p q : ℕ)
    (s : (TopCat.toSSet.obj X) _⦋p + q⦌) :
    LocallyFiniteChains.Cycles.singularSimplexImage X q (AlgebraicTopology.Products.SimplexFaceIdentities.backFace (TopCat.toSSet.obj X) p q s) ⊆
      LocallyFiniteChains.Cycles.singularSimplexImage X (p + q) s :=
  LocallyFiniteComplex.Cycles.singularSimplexImage_map_subset X (AlgebraicTopology.Products.SimplexFaceIdentities.backInclusion p q).op s

/-- The exact one-term coefficient kernel of the ordinary cap formula. -/
def locallyFiniteCapKernel (p q : ℕ)
    (c : (AlgebraicTopology.Cohomology.Singular.Basic.singularCochains (ModuleCat.of R R) X).X p)
    (s : (TopCat.toSSet.obj X) _⦋p + q⦌) :
    ((TopCat.toSSet.obj X) _⦋q⦌) →₀ R :=
  Finsupp.single (AlgebraicTopology.Products.SimplexFaceIdentities.backFace (TopCat.toSSet.obj X) p q s)
    (AlgebraicTopology.Cohomology.Singular.Coefficients.simplicialEvaluation (TopCat.toSSet.obj X) (ModuleCat.of R R)
      (AlgebraicTopology.Products.SimplexFaceIdentities.frontFace (TopCat.toSSet.obj X) p q s) c)

/-- The actual cap kernel is subordinate to simplex images. -/
theorem locallyFiniteCapKernel_subordinate (p q : ℕ)
    (c : (AlgebraicTopology.Cohomology.Singular.Basic.singularCochains (ModuleCat.of R R) X).X p)
    (s : (TopCat.toSSet.obj X) _⦋p + q⦌)
    (t : (TopCat.toSSet.obj X) _⦋q⦌)
    (ht : t ∈ (locallyFiniteCapKernel X p q c s).support) :
    LocallyFiniteChains.Cycles.singularSimplexImage X q t ⊆ LocallyFiniteChains.Cycles.singularSimplexImage X (p + q) s := by
  have he : t = AlgebraicTopology.Products.SimplexFaceIdentities.backFace (TopCat.toSSet.obj X) p q s :=
    Finset.mem_singleton.mp (Finsupp.support_single_subset ht)
  rw [he]
  exact singularBackFaceImage_subset X p q s

/-- Cap by a fixed ordinary cochain on the genuine locally finite chain module. -/
def locallyFiniteCapLinear (p q : ℕ)
    (c : (AlgebraicTopology.Cohomology.Singular.Basic.singularCochains (ModuleCat.of R R) X).X p) :
    LocallyFiniteChains.Cycles.LocallyFiniteSingularChains R X (p + q) →ₗ[R] LocallyFiniteChains.Cycles.LocallyFiniteSingularChains R X q :=
  LocallyFiniteOperation.Cycles.SpatialSupport.kernelOperation (locallyFiniteCapKernel X p q c)
    (locallyFiniteCapKernel_subordinate X p q c) (LocallyFiniteChains.Cycles.singularSimplexImage_nonempty X q)

theorem locallyFiniteCapLinear_isSpatiallyLocal (p q : ℕ)
    (c : (AlgebraicTopology.Cohomology.Singular.Basic.singularCochains (ModuleCat.of R R) X).X p) :
    LocallyFiniteOperation.Cycles.SpatialSupport.IsSpatiallyLocal (locallyFiniteCapLinear X p q c) :=
  LocallyFiniteOperation.Cycles.SpatialSupport.kernelOperation_isSpatiallyLocal _ _ _

/-- The canonical ordinary-chain inclusion has exactly the expected singleton
coefficient on each genuine singular simplex generator. -/
theorem ordinaryToLocallyFinite_simplexChain (n : ℕ)
    (s : (TopCat.toSSet.obj X) _⦋n⦌) :
    LocallyFiniteCompact.Cycles.ordinaryToLocallyFinite R X n (AlgebraicTopology.Cohomology.Singular.ChainDual.simplexChain (TopCat.toSSet.obj X) s) =
      LocallyFiniteCompact.Cycles.SpatialSupport.ofFinsupp (LocallyFiniteChains.Cycles.singularSimplexImage X n) (Finsupp.single s (1 : R)) := by
  exact ConcreteCategory.congr_hom (LocallyFiniteComparison.Cycles.ordinaryToLocallyFinite_simplex R X n s) 1

/-- On a finite singleton, locally finite cap is the literal ordinary formula. -/
theorem locallyFiniteCapLinear_single (p q : ℕ)
    (c : (AlgebraicTopology.Cohomology.Singular.Basic.singularCochains (ModuleCat.of R R) X).X p)
    (s : (TopCat.toSSet.obj X) _⦋p + q⦌) (r : R) :
    locallyFiniteCapLinear X p q c
        (LocallyFiniteCompact.Cycles.SpatialSupport.ofFinsupp (LocallyFiniteChains.Cycles.singularSimplexImage X (p + q)) (Finsupp.single s r)) =
      LocallyFiniteCompact.Cycles.SpatialSupport.ofFinsupp (LocallyFiniteChains.Cycles.singularSimplexImage X q)
        (r • locallyFiniteCapKernel X p q c s) := by
  unfold locallyFiniteCapLinear
  rw [LocallyFiniteOperation.Cycles.SpatialSupport.kernelOperation_ofFinsupp, Finsupp.linearCombination_single]

/-- The locally finite construction extends the existing genuine singular cap
product on all ordinary chains, not just on abstract coefficient functions. -/
theorem locallyFiniteCapLinear_ordinary (p q : ℕ)
    (c : (AlgebraicTopology.Cohomology.Singular.Basic.singularCochains (ModuleCat.of R R) X).X p)
    (z : (AlgebraicTopology.Cohomology.Singular.Evaluation.singularScalarChains (R := R) X).X (p + q)) :
    locallyFiniteCapLinear X p q c (LocallyFiniteCompact.Cycles.ordinaryToLocallyFinite R X (p + q) z) =
      LocallyFiniteCompact.Cycles.ordinaryToLocallyFinite R X q (AlgebraicTopology.Products.Cap.singularCap X p q c z) := by
  have he : (locallyFiniteCapLinear X p q c).comp (LocallyFiniteCompact.Cycles.ordinaryToLocallyFinite R X (p + q)) =
      (LocallyFiniteCompact.Cycles.ordinaryToLocallyFinite R X q).comp (AlgebraicTopology.Products.Cap.singularCap X p q c) := by
    apply AlgebraicTopology.Cohomology.Singular.ChainDual.chainFunctional_ext (TopCat.toSSet.obj X)
      (ModuleCat.of R (LocallyFiniteChains.Cycles.LocallyFiniteSingularChains R X q))
    intro s
    simp only [LinearMap.comp_apply, ordinaryToLocallyFinite_simplexChain,
      locallyFiniteCapLinear_single, one_smul, AlgebraicTopology.Products.Cap.singularCap, AlgebraicTopology.Products.Cap.cap_simplex, map_smul]
    change LocallyFiniteCompact.Cycles.SpatialSupport.ofFinsupp (LocallyFiniteChains.Cycles.singularSimplexImage X q)
        (Finsupp.single _ _) = _
    rw [← map_smul, Finsupp.smul_single]
    simp only [smul_eq_mul, mul_one]
  exact LinearMap.congr_fun he z

/-- Spatially local maps agree as soon as they agree on ordinary chains. -/
theorem spatiallyLocal_ext_ordinary {n m : ℕ}
    {F G : LocallyFiniteChains.Cycles.LocallyFiniteSingularChains R X n →ₗ[R] LocallyFiniteChains.Cycles.LocallyFiniteSingularChains R X m}
    (hF : LocallyFiniteOperation.Cycles.SpatialSupport.IsSpatiallyLocal F) (hG : LocallyFiniteOperation.Cycles.SpatialSupport.IsSpatiallyLocal G)
    (h : ∀ z : (AlgebraicTopology.Cohomology.Singular.Evaluation.singularScalarChains (R := R) X).X n,
      F (LocallyFiniteCompact.Cycles.ordinaryToLocallyFinite R X n z) = G (LocallyFiniteCompact.Cycles.ordinaryToLocallyFinite R X n z)) : F = G := by
  apply LocallyFiniteOperation.Cycles.SpatialSupport.IsSpatiallyLocal.ext hF hG (LocallyFiniteChains.Cycles.singularSimplexImage_nonempty X m)
  intro a
  have hz := h ((LocallyFiniteCompact.Cycles.ordinarySingularChainCoefficients R X n).symm a)
  simpa only [LocallyFiniteCompact.Cycles.ordinaryToLocallyFinite, LinearMap.comp_apply, LinearEquiv.coe_coe,
    LinearEquiv.apply_symm_apply] using hz

/-- The locally finite extension is additive in its ordinary cochain. -/
theorem locallyFiniteCapLinear_add (p q : ℕ)
    (c d : (AlgebraicTopology.Cohomology.Singular.Basic.singularCochains (ModuleCat.of R R) X).X p) :
    locallyFiniteCapLinear X p q (c + d) =
      locallyFiniteCapLinear X p q c + locallyFiniteCapLinear X p q d := by
  apply spatiallyLocal_ext_ordinary X (locallyFiniteCapLinear_isSpatiallyLocal X p q (c + d))
    ((locallyFiniteCapLinear_isSpatiallyLocal X p q c).add
      (locallyFiniteCapLinear_isSpatiallyLocal X p q d))
  intro z
  simp only [LinearMap.add_apply, locallyFiniteCapLinear_ordinary, map_add]

/-- Scalar multiples of spatially local linear operations remain local. -/
theorem spatiallyLocal_smul {n m : ℕ}
    {F : LocallyFiniteChains.Cycles.LocallyFiniteSingularChains R X n →ₗ[R] LocallyFiniteChains.Cycles.LocallyFiniteSingularChains R X m}
    (hF : LocallyFiniteOperation.Cycles.SpatialSupport.IsSpatiallyLocal F) (r : R) :
    LocallyFiniteOperation.Cycles.SpatialSupport.IsSpatiallyLocal (r • F) := by
  intro x a b hab t ht
  exact congrArg (fun v : R => r • v) (hF x a b hab t ht)

/-- The locally finite extension is linear in its ordinary cochain. -/
theorem locallyFiniteCapLinear_smul (p q : ℕ) (r : R)
    (c : (AlgebraicTopology.Cohomology.Singular.Basic.singularCochains (ModuleCat.of R R) X).X p) :
    locallyFiniteCapLinear X p q (r • c) = r • locallyFiniteCapLinear X p q c := by
  apply spatiallyLocal_ext_ordinary X (locallyFiniteCapLinear_isSpatiallyLocal X p q (r • c))
    (spatiallyLocal_smul X (locallyFiniteCapLinear_isSpatiallyLocal X p q c) r)
  intro z
  simp only [LinearMap.smul_apply, locallyFiniteCapLinear_ordinary, map_smul]

/-- The actual bilinear cap product of an ordinary singular cochain and a
spatially locally finite singular chain. -/
def locallyFiniteCap (p q : ℕ) :
    (AlgebraicTopology.Cohomology.Singular.Basic.singularCochains (ModuleCat.of R R) X).X p →ₗ[R]
      LocallyFiniteChains.Cycles.LocallyFiniteSingularChains R X (p + q) →ₗ[R] LocallyFiniteChains.Cycles.LocallyFiniteSingularChains R X q where
  toFun := locallyFiniteCapLinear X p q
  map_add' := locallyFiniteCapLinear_add X p q
  map_smul' := locallyFiniteCapLinear_smul X p q

@[simp]
theorem locallyFiniteCap_ordinary (p q : ℕ)
    (c : (AlgebraicTopology.Cohomology.Singular.Basic.singularCochains (ModuleCat.of R R) X).X p)
    (z : (AlgebraicTopology.Cohomology.Singular.Evaluation.singularScalarChains (R := R) X).X (p + q)) :
    locallyFiniteCap X p q c (LocallyFiniteCompact.Cycles.ordinaryToLocallyFinite R X (p + q) z) =
      LocallyFiniteCompact.Cycles.ordinaryToLocallyFinite R X q (AlgebraicTopology.Products.Cap.singularCap X p q c z) :=
  locallyFiniteCapLinear_ordinary X p q c z

end

/-!
# The boundary identity for locally finite cap products

Spatial locality reduces the identity to ordinary finite chains, where the
Alexander--Whitney boundary formula has already been proved. All coefficient
rings are retained; no compactness of the ambient space is required.
-/

open _root_.CategoryTheory
open OAI.AlgebraicTopology.Products.CapBoundary
open scoped BigOperators

variable {R : Type} [CommRing R] (X : TopCat.{0})

theorem spatiallyLocal_zsmul {n m : ℕ}
    {F : LocallyFiniteChains.Cycles.LocallyFiniteSingularChains R X n →ₗ[R] LocallyFiniteChains.Cycles.LocallyFiniteSingularChains R X m}
    (hF : LocallyFiniteOperation.Cycles.SpatialSupport.IsSpatiallyLocal F) (r : ℤ) :
    LocallyFiniteOperation.Cycles.SpatialSupport.IsSpatiallyLocal (r • F) := by
  intro x a b hab t ht
  exact congrArg (fun v : R => r • v) (hF x a b hab t ht)

theorem spatiallyLocal_finset_sum {n m : ℕ} {ι : Type*} (s : Finset ι)
    (F : ι → LocallyFiniteChains.Cycles.LocallyFiniteSingularChains R X n →ₗ[R] LocallyFiniteChains.Cycles.LocallyFiniteSingularChains R X m)
    (hF : ∀ i ∈ s, LocallyFiniteOperation.Cycles.SpatialSupport.IsSpatiallyLocal (F i)) :
    LocallyFiniteOperation.Cycles.SpatialSupport.IsSpatiallyLocal (∑ i ∈ s, F i) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      simpa only [Finset.sum_empty] using
        (LocallyFiniteOperation.Cycles.SpatialSupport.IsSpatiallyLocal.zero (R := R)
          (LocallyFiniteChains.Cycles.singularSimplexImage X n) (LocallyFiniteChains.Cycles.singularSimplexImage X m))
  | @insert i s hi ih =>
      rw [Finset.sum_insert hi]
      exact (hF i (Finset.mem_insert_self i s)).add
        (ih (fun j hj => hF j (Finset.mem_insert_of_mem hj)))

/-- The genuine locally finite boundary is spatially local over any
commutative coefficient ring. -/
theorem locallyFiniteBoundary_isSpatiallyLocal (n : ℕ) :
    LocallyFiniteOperation.Cycles.SpatialSupport.IsSpatiallyLocal (LocallyFiniteChains.Cycles.locallyFiniteBoundary R X n) := by
  unfold LocallyFiniteChains.Cycles.locallyFiniteBoundary
  apply spatiallyLocal_finset_sum X
  intro i _
  exact spatiallyLocal_smul X
    (LocallyFiniteOperation.Cycles.SpatialSupport.pushforward_isSpatiallyLocal
      ((TopCat.toSSet.obj X).δ i) (LocallyFiniteChains.Cycles.singularSimplexImage_face_subset X n i)
      (LocallyFiniteChains.Cycles.singularSimplexImage_nonempty X n)) ((-1 : R) ^ i.val)

/-- On ordinary chains, the locally finite differential is the ordinary
singular differential followed by the canonical inclusion. -/
theorem locallyFiniteBoundary_ordinary (n : ℕ)
    (z : (AlgebraicTopology.Cohomology.Singular.Evaluation.singularScalarChains (R := R) X).X (n + 1)) :
    LocallyFiniteChains.Cycles.locallyFiniteBoundary R X n (LocallyFiniteCompact.Cycles.ordinaryToLocallyFinite R X (n + 1) z) =
      LocallyFiniteCompact.Cycles.ordinaryToLocallyFinite R X n ((AlgebraicTopology.Cohomology.Singular.Evaluation.singularScalarChains (R := R) X).d (n + 1) n z) := by
  rw [← LocallyFiniteComplex.Cycles.locallyFiniteSingularComplex_d R X n]
  exact ConcreteCategory.congr_hom (LocallyFiniteComparison.Cycles.ordinaryToLocallyFinite_comm R X n) z

/-- Transport of the actual locally finite degree module along an equality. -/
def locallyFiniteChainCast {a b : ℕ} (h : a = b) :
    LocallyFiniteChains.Cycles.LocallyFiniteSingularChains R X a →ₗ[R] LocallyFiniteChains.Cycles.LocallyFiniteSingularChains R X b :=
  h ▸ LinearMap.id

@[simp]
theorem locallyFiniteChainCast_rfl (n : ℕ) :
    locallyFiniteChainCast (R := R) X (rfl : n = n) = LinearMap.id := rfl

theorem locallyFiniteChainCast_isSpatiallyLocal {a b : ℕ} (h : a = b) :
    LocallyFiniteOperation.Cycles.SpatialSupport.IsSpatiallyLocal (locallyFiniteChainCast (R := R) X h) := by
  subst b
  exact LocallyFiniteOperation.Cycles.SpatialSupport.IsSpatiallyLocal.id (LocallyFiniteChains.Cycles.singularSimplexImage X a)

@[simp]
theorem locallyFiniteChainCast_ordinary {a b : ℕ} (h : a = b)
    (z : (AlgebraicTopology.Cohomology.Singular.Evaluation.singularScalarChains (R := R) X).X a) :
    locallyFiniteChainCast X h (LocallyFiniteCompact.Cycles.ordinaryToLocallyFinite R X a z) =
      LocallyFiniteCompact.Cycles.ordinaryToLocallyFinite R X b (AlgebraicTopology.Products.Cap.chainCast (TopCat.toSSet.obj X) h z) := by
  subst b
  rfl

/-- The exact Alexander--Whitney boundary identity on locally finite chains. -/
theorem locallyFiniteCap_boundary (p q : ℕ)
    (c : (AlgebraicTopology.Cohomology.Singular.Basic.singularCochains (ModuleCat.of R R) X).X p)
    (z : LocallyFiniteChains.Cycles.LocallyFiniteSingularChains R X (p + q + 1)) :
    locallyFiniteCap X p q c (LocallyFiniteChains.Cycles.locallyFiniteBoundary R X (p + q) z) =
      locallyFiniteCap X (p + 1) q
        ((AlgebraicTopology.Cohomology.Singular.Basic.singularCochains (ModuleCat.of R R) X).d p (p + 1) c)
        (locallyFiniteChainCast X (by omega : p + q + 1 = (p + 1) + q) z) +
      ((-1 : ℤ) ^ p) •
        LocallyFiniteChains.Cycles.locallyFiniteBoundary R X q (locallyFiniteCap X p (q + 1) c z) := by
  let F := (locallyFiniteCap X p q c).comp (LocallyFiniteChains.Cycles.locallyFiniteBoundary R X (p + q))
  let G := (locallyFiniteCap X (p + 1) q
      ((AlgebraicTopology.Cohomology.Singular.Basic.singularCochains (ModuleCat.of R R) X).d p (p + 1) c)).comp
        (locallyFiniteChainCast X (by omega : p + q + 1 = (p + 1) + q)) +
    ((-1 : ℤ) ^ p) • (LocallyFiniteChains.Cycles.locallyFiniteBoundary R X q).comp (locallyFiniteCap X p (q + 1) c)
  have hF : LocallyFiniteOperation.Cycles.SpatialSupport.IsSpatiallyLocal F :=
    (locallyFiniteCapLinear_isSpatiallyLocal X p q c).comp
      (locallyFiniteBoundary_isSpatiallyLocal X (p + q))
  have hG : LocallyFiniteOperation.Cycles.SpatialSupport.IsSpatiallyLocal G :=
    ((locallyFiniteCapLinear_isSpatiallyLocal X (p + 1) q
        ((AlgebraicTopology.Cohomology.Singular.Basic.singularCochains (ModuleCat.of R R) X).d p (p + 1) c)).comp
      (locallyFiniteChainCast_isSpatiallyLocal X _)).add
      (spatiallyLocal_zsmul X ((locallyFiniteBoundary_isSpatiallyLocal X q).comp
        (locallyFiniteCapLinear_isSpatiallyLocal X p (q + 1) c)) _)
  have he : F = G := by
    apply spatiallyLocal_ext_ordinary X hF hG
    intro w
    simp only [F, G, LinearMap.comp_apply, LinearMap.add_apply, LinearMap.smul_apply,
      locallyFiniteCap_ordinary, locallyFiniteBoundary_ordinary, locallyFiniteChainCast_ordinary]
    erw [locallyFiniteCap_ordinary X p (q + 1) c w]
    rw [locallyFiniteBoundary_ordinary]
    simpa only [map_add, map_zsmul] using
      congrArg (LocallyFiniteCompact.Cycles.ordinaryToLocallyFinite R X q) (AlgebraicTopology.Products.CapBoundary.singularCap_boundary X p q c w)
  exact LinearMap.congr_fun he z

/-- The boundary identity solved for the outgoing boundary of the cap product. -/
theorem boundary_locallyFiniteCap (p q : ℕ)
    (c : (AlgebraicTopology.Cohomology.Singular.Basic.singularCochains (ModuleCat.of R R) X).X p)
    (z : LocallyFiniteChains.Cycles.LocallyFiniteSingularChains R X (p + q + 1)) :
    LocallyFiniteChains.Cycles.locallyFiniteBoundary R X q (locallyFiniteCap X p (q + 1) c z) =
      ((-1 : ℤ) ^ p) •
        (locallyFiniteCap X p q c (LocallyFiniteChains.Cycles.locallyFiniteBoundary R X (p + q) z) -
          locallyFiniteCap X (p + 1) q
            ((AlgebraicTopology.Cohomology.Singular.Basic.singularCochains (ModuleCat.of R R) X).d p (p + 1) c)
            (locallyFiniteChainCast X (by omega : p + q + 1 = (p + 1) + q) z)) := by
  rw [locallyFiniteCap_boundary X p q c z, add_sub_cancel_left, smul_smul]
  have hs : ((-1 : ℤ) ^ p) * ((-1 : ℤ) ^ p) = 1 := by
    rw [← mul_pow]
    simp
  rw [hs, one_smul]

end

end OAI.AlgebraicGeometry.CycleClass.Geometric.LocallyFiniteCap.Cycles
