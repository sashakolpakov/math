import OAI.AlgebraicTopology.DeRham.Comparison.CubicalSupport
import Mathlib.Algebra.Category.ModuleCat.Abelian
import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
import Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex

/-! # Cubical Local Cochains -/

namespace OAI.AlgebraicTopology.DeRham.Comparison.CubicalLocalCochains

noncomputable section

section

/-!
# Exactness of normalized smooth cubical cochains on convex subsets

These cochains are the actual additive duals of the supported normalized
cubical chains. The primitive of a positive-degree cocycle is explicit:
precompose it with the straight-line prism operator. No comparison map or
local exactness hypothesis is supplied as extra data.
-/

open _root_.CategoryTheory

variable {m n : ℕ}

/-- Additive-coefficient cochains on the normalized smooth cubes in `U`. -/
abbrev SupportedCubicalCochain (U : Set (Fin m → ℝ)) (A : Type*) [AddCommGroup A]
    (n : ℕ) :=
  CubicalSupport.normalizedSupportedCubicalChains U n →ₗ[ℤ] A

/-- The coboundary is precomposition with the actual restricted chain boundary. -/
def supportedCubicalCoboundary (U : Set (Fin m → ℝ)) (A : Type*) [AddCommGroup A]
    (n : ℕ) :
    SupportedCubicalCochain U A n →ₗ[ℤ] SupportedCubicalCochain U A (n + 1) where
  toFun φ := φ.comp (CubicalSupport.supportedNormalizedBoundary U n)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

@[simp]
theorem supportedCubicalCoboundary_apply (U : Set (Fin m → ℝ)) (A : Type*)
    [AddCommGroup A] (φ : SupportedCubicalCochain U A n)
    (c : CubicalSupport.normalizedSupportedCubicalChains U (n + 1)) :
    supportedCubicalCoboundary U A n φ c = φ (CubicalSupport.supportedNormalizedBoundary U n c) := rfl

theorem supportedCubicalCoboundary_squared (U : Set (Fin m → ℝ)) (A : Type*)
    [AddCommGroup A] (φ : SupportedCubicalCochain U A n) :
    supportedCubicalCoboundary U A (n + 1) (supportedCubicalCoboundary U A n φ) = 0 := by
  ext c
  change φ (CubicalSupport.supportedNormalizedBoundary U n
    (CubicalSupport.supportedNormalizedBoundary U (n + 1) c)) = 0
  rw [CubicalSupport.supportedNormalizedBoundary_sq_zero, map_zero]

/-- The explicit cochain homotopy dual to the genuine straight-line prism. -/
def supportedCochainPrism {U : Set (Fin m → ℝ)} (hU : Convex ℝ U)
    {x₀ : Fin m → ℝ} (hx₀ : x₀ ∈ U) (A : Type*) [AddCommGroup A] (n : ℕ) :
    SupportedCubicalCochain U A (n + 1) →ₗ[ℤ] SupportedCubicalCochain U A n where
  toFun φ := φ.comp (CubicalSupport.supportedNormalizedPrism hU hx₀ n)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- The dual prism identity contracts the actual cochains in positive degrees. -/
theorem supportedCochainPrism_identity {U : Set (Fin m → ℝ)} (hU : Convex ℝ U)
    {x₀ : Fin m → ℝ} (hx₀ : x₀ ∈ U) (A : Type*) [AddCommGroup A]
    (φ : SupportedCubicalCochain U A (n + 1)) :
    supportedCubicalCoboundary U A n (supportedCochainPrism hU hx₀ A n φ) +
        supportedCochainPrism hU hx₀ A (n + 1)
          (supportedCubicalCoboundary U A (n + 1) φ) = φ := by
  ext c
  change φ (CubicalSupport.supportedNormalizedPrism hU hx₀ n (CubicalSupport.supportedNormalizedBoundary U n c)) +
    φ (CubicalSupport.supportedNormalizedBoundary U (n + 1) (CubicalSupport.supportedNormalizedPrism hU hx₀ (n + 1) c)) =
      φ c
  rw [← map_add]
  exact congrArg φ ((add_comm _ _).trans (CubicalSupport.supportedNormalizedPrism_contraction hU hx₀ c))

/-- Every positive-degree cocycle has the explicitly given prism primitive. -/
theorem supportedCubicalCocycle_prism_primitive {U : Set (Fin m → ℝ)} (hU : Convex ℝ U)
    {x₀ : Fin m → ℝ} (hx₀ : x₀ ∈ U) (A : Type*) [AddCommGroup A]
    (φ : SupportedCubicalCochain U A (n + 1))
    (hφ : supportedCubicalCoboundary U A (n + 1) φ = 0) :
    supportedCubicalCoboundary U A n (supportedCochainPrism hU hx₀ A n φ) = φ := by
  simpa only [hφ, map_zero, add_zero] using supportedCochainPrism_identity hU hx₀ A φ

/-- Exactness of the actual coboundary maps in every positive degree. -/
theorem supportedCubicalCoboundary_exact {U : Set (Fin m → ℝ)} (hU : Convex ℝ U)
    {x₀ : Fin m → ℝ} (hx₀ : x₀ ∈ U) (A : Type*) [AddCommGroup A] (n : ℕ) :
    Function.Exact (supportedCubicalCoboundary U A n)
      (supportedCubicalCoboundary U A (n + 1)) := by
  apply LinearMap.exact_of_comp_of_mem_range
  · apply LinearMap.ext
    intro φ
    exact supportedCubicalCoboundary_squared U A φ
  · intro φ hφ
    exact ⟨supportedCochainPrism hU hx₀ A n φ,
      supportedCubicalCocycle_prism_primitive hU hx₀ A φ hφ⟩

/-- The supported normalized cubical cochain complex with arbitrary additive coefficients. -/
def supportedCubicalCochainComplex (U : Set (Fin m → ℝ)) (A : Type*) [AddCommGroup A] :
    CochainComplex (ModuleCat ℤ) ℕ :=
  CochainComplex.of (fun n => ModuleCat.of ℤ (SupportedCubicalCochain U A n))
    (fun n => ModuleCat.ofHom (supportedCubicalCoboundary U A n))
    (fun _ => by
      apply ModuleCat.hom_ext
      apply LinearMap.ext
      intro φ
      exact supportedCubicalCoboundary_squared U A φ)

@[simp]
theorem supportedCubicalCochainComplex_d (U : Set (Fin m → ℝ)) (A : Type*)
    [AddCommGroup A] (n : ℕ) :
    (supportedCubicalCochainComplex U A).d n (n + 1) =
      ModuleCat.ofHom (supportedCubicalCoboundary U A n) :=
  CochainComplex.of_d
    (fun j => ModuleCat.of ℤ (SupportedCubicalCochain U A j))
    (fun j => ModuleCat.ofHom (supportedCubicalCoboundary U A j)) n

/-- The bundled cochain complex is exact in positive degree on every nonempty convex target. -/
theorem supportedCubicalCochainComplex_exactAt {U : Set (Fin m → ℝ)}
    (hU : Convex ℝ U) {x₀ : Fin m → ℝ} (hx₀ : x₀ ∈ U)
    (A : Type*) [AddCommGroup A] (n : ℕ) :
    (supportedCubicalCochainComplex U A).ExactAt (n + 1) := by
  apply (HomologicalComplex.exactAt_iff' _ n (n + 1) (n + 2)
    ((ComplexShape.up ℕ).prev_eq' (show (ComplexShape.up ℕ).Rel n (n + 1) from rfl))
    ((ComplexShape.up ℕ).next_eq'
      (show (ComplexShape.up ℕ).Rel (n + 1) (n + 2) from rfl))).2
  apply (ShortComplex.moduleCat_exact_iff _).2
  intro φ hφ
  change (supportedCubicalCochainComplex U A).d (n + 1) (n + 2) φ = 0 at hφ
  rw [supportedCubicalCochainComplex_d] at hφ
  refine ⟨supportedCochainPrism hU hx₀ A n φ, ?_⟩
  change (supportedCubicalCochainComplex U A).d n (n + 1)
    (supportedCochainPrism hU hx₀ A n φ) = φ
  rw [supportedCubicalCochainComplex_d]
  exact supportedCubicalCocycle_prism_primitive hU hx₀ A φ hφ

/-- Its actual categorical cohomology is zero in every positive degree. -/
theorem supportedCubicalCohomology_isZero {U : Set (Fin m → ℝ)}
    (hU : Convex ℝ U) {x₀ : Fin m → ℝ} (hx₀ : x₀ ∈ U)
    (A : Type*) [AddCommGroup A] (n : ℕ) :
    Limits.IsZero ((supportedCubicalCochainComplex U A).homology (n + 1)) :=
  (HomologicalComplex.exactAt_iff_isZero_homology _ _).mp
    (supportedCubicalCochainComplex_exactAt hU hx₀ A n)

end

/-!
# Augmentation and degree-zero normalized cubical cocycles

The augmentation is the actual sum of coefficients of zero-dimensional
cubes. The chosen point has augmentation one. The degree-zero prism identity
identifies its kernel with boundaries and identifies degree-zero cocycles
on a nonempty convex target with constant coefficient values.
-/

open OAI.AlgebraicTopology.DeRham.Comparison.StokesF.SingularCubeStokes

variable {n m : ℕ}

/-- The augmentation on actual normalized degree-zero cubical chains. -/
def normalizedCubicalAugmentation (m : ℕ) : CubicalDegenerateQ.NormalizedCubicalChain 0 m →ₗ[ℤ] ℤ :=
  (CubicalDegenerateQ.degenerateSubmodule 0 m).liftQ
    (Finsupp.degree : StokesF.SingularCubeStokes.SingularChain 0 m →+ ℤ).toIntLinearMap
    (by rw [CubicalDegenerateQ.degenerateSubmodule_zero]; exact bot_le)

@[simp]
theorem normalizedCubicalAugmentation_mk (c : StokesF.SingularCubeStokes.SingularChain 0 m) :
    normalizedCubicalAugmentation m ((CubicalDegenerateQ.degenerateSubmodule 0 m).mkQ c) =
      Finsupp.degree c := rfl

/-- The augmentation vanishes on every actual normalized boundary. -/
theorem normalizedCubicalAugmentation_boundary (c : CubicalDegenerateQ.NormalizedCubicalChain 1 m) :
    normalizedCubicalAugmentation m (CubicalDegenerateQ.normalizedBoundary 0 m c) = 0 := by
  refine Submodule.Quotient.induction_on (CubicalDegenerateQ.degenerateSubmodule 1 m) c ?_
  intro d
  simpa only [← Submodule.mkQ_apply, CubicalDegenerateQ.normalizedBoundary_mk,
    normalizedCubicalAugmentation_mk] using CubicalDegeneracies.degree_singularBoundary d

/-- The normalized zero-chain carried by a single chosen point. -/
def normalizedPointChain (x : Fin m → ℝ) : CubicalDegenerateQ.NormalizedCubicalChain 0 m :=
  (CubicalDegenerateQ.degenerateSubmodule 0 m).mkQ (Finsupp.single (CubicalDegeneracies.constantSmoothCube 0 x) 1)

@[simp]
theorem normalizedCubicalAugmentation_point (x : Fin m → ℝ) :
    normalizedCubicalAugmentation m (normalizedPointChain x) = 1 := by
  change normalizedCubicalAugmentation m
    ((CubicalDegenerateQ.degenerateSubmodule 0 m).mkQ (Finsupp.single (CubicalDegeneracies.constantSmoothCube 0 x) 1)) = 1
  rw [normalizedCubicalAugmentation_mk, Finsupp.degree_single]

/-- The constant cube operator is coefficient sum times its single constant cube. -/
theorem constantCubeOperator_eq_degree_smul (x₀ : Fin m → ℝ) (c : StokesF.SingularCubeStokes.SingularChain n m) :
    CubicalPrism.constantCubeOperator n m x₀ c =
      Finsupp.degree c • Finsupp.single (CubicalDegeneracies.constantSmoothCube n x₀) 1 := by
  induction c using Finsupp.induction with
  | zero => simp
  | single_add σ k c hσ hk ih =>
    simp only [map_add, CubicalPrism.constantCubeOperator_single, Finsupp.degree_single, add_smul, ih,
      Finsupp.smul_single, smul_eq_mul, mul_one]

/-- On degree-zero normalized chains, the constant operator is point times augmentation. -/
theorem normalizedConstant_zero_eq_augmentation_smul (x₀ : Fin m → ℝ)
    (c : CubicalDegenerateQ.NormalizedCubicalChain 0 m) :
    CubicalPrism.normalizedConstant 0 m x₀ c = normalizedCubicalAugmentation m c • normalizedPointChain x₀ := by
  refine Submodule.Quotient.induction_on (CubicalDegenerateQ.degenerateSubmodule 0 m) c ?_
  intro d
  change CubicalPrism.normalizedConstant 0 m x₀ ((CubicalDegenerateQ.degenerateSubmodule 0 m).mkQ d) = _
  rw [CubicalPrism.normalizedConstant_mk, constantCubeOperator_eq_degree_smul, map_smul]
  rfl

/-- The concrete augmented prism identity in degree zero. -/
theorem normalized_prism_zero_augmentation (x₀ : Fin m → ℝ)
    (c : CubicalDegenerateQ.NormalizedCubicalChain 0 m) :
    CubicalDegenerateQ.normalizedBoundary 0 m (CubicalPrism.normalizedPrism 0 m x₀ c) =
      c - normalizedCubicalAugmentation m c • normalizedPointChain x₀ := by
  rw [CubicalPrism.normalized_prism_identity_zero, normalizedConstant_zero_eq_augmentation_smul]

/-- Every augmentation-zero normalized zero-chain is a boundary. -/
theorem normalized_aug_zero_is_boundary (x₀ : Fin m → ℝ)
    (c : CubicalDegenerateQ.NormalizedCubicalChain 0 m) (hc : normalizedCubicalAugmentation m c = 0) :
    CubicalDegenerateQ.normalizedBoundary 0 m (CubicalPrism.normalizedPrism 0 m x₀ c) = c := by
  simpa only [hc, zero_smul, sub_zero] using normalized_prism_zero_augmentation x₀ c

/-- Exactness at the zero-chain group in the augmented normalized complex. -/
theorem normalizedCubicalAugmentation_exact (x₀ : Fin m → ℝ) :
    Function.Exact (CubicalDegenerateQ.normalizedBoundary 0 m) (normalizedCubicalAugmentation m) := by
  apply LinearMap.exact_of_comp_of_mem_range
  · apply LinearMap.ext
    exact normalizedCubicalAugmentation_boundary
  · intro c hc
    exact ⟨CubicalPrism.normalizedPrism 0 m x₀ c, normalized_aug_zero_is_boundary x₀ c hc⟩

/-- The chosen point splits the augmentation and, in particular, makes it surjective. -/
theorem normalizedCubicalAugmentation_surjective (x₀ : Fin m → ℝ) :
    Function.Surjective (normalizedCubicalAugmentation m) := by
  intro k
  refine ⟨k • normalizedPointChain x₀, ?_⟩
  simp only [map_smul, normalizedCubicalAugmentation_point, smul_eq_mul, mul_one]

/-- The augmentation restricted to normalized zero-chains in a target subset. -/
def supportedCubicalAugmentation (U : Set (Fin m → ℝ)) :
    CubicalSupport.normalizedSupportedCubicalChains U 0 →ₗ[ℤ] ℤ :=
  (normalizedCubicalAugmentation m).comp (CubicalSupport.normalizedSupportedCubicalChains U 0).subtype

/-- The point zero-chain belongs to the supported module exactly as a genuine cube in `U`. -/
def supportedPointChain {U : Set (Fin m → ℝ)} {x : Fin m → ℝ} (hx : x ∈ U) :
    CubicalSupport.normalizedSupportedCubicalChains U 0 :=
  ⟨normalizedPointChain x,
    Submodule.mem_map_of_mem (CubicalSupport.single_mem_supportedCubicalChains _ (fun _ _ => hx) 1)⟩

@[simp]
theorem supportedCubicalAugmentation_point {U : Set (Fin m → ℝ)} {x : Fin m → ℝ}
    (hx : x ∈ U) : supportedCubicalAugmentation U (supportedPointChain hx) = 1 :=
  normalizedCubicalAugmentation_point x

theorem supportedCubicalAugmentation_boundary (U : Set (Fin m → ℝ))
    (c : CubicalSupport.normalizedSupportedCubicalChains U 1) :
    supportedCubicalAugmentation U (CubicalSupport.supportedNormalizedBoundary U 0 c) = 0 :=
  normalizedCubicalAugmentation_boundary c.val

/-- The augmented prism identity holds inside the supported degree-zero module. -/
theorem supportedNormalizedPrism_zero {U : Set (Fin m → ℝ)} (hU : Convex ℝ U)
    {x₀ : Fin m → ℝ} (hx₀ : x₀ ∈ U) (c : CubicalSupport.normalizedSupportedCubicalChains U 0) :
    CubicalSupport.supportedNormalizedBoundary U 0 (CubicalSupport.supportedNormalizedPrism hU hx₀ 0 c) =
      c - supportedCubicalAugmentation U c • supportedPointChain hx₀ := by
  apply Subtype.ext
  exact normalized_prism_zero_augmentation x₀ c.val

/-- A coefficient value as a constant normalized cubical zero-cochain. -/
def constantSupportedCochain (U : Set (Fin m → ℝ)) (A : Type*) [AddCommGroup A] :
    A →ₗ[ℤ] SupportedCubicalCochain U A 0 where
  toFun a := (LinearMap.toSpanSingleton ℤ A a).comp (supportedCubicalAugmentation U)
  map_add' a b := by
    ext c
    exact smul_add (supportedCubicalAugmentation U c) a b
  map_smul' k a := by
    ext c
    exact smul_comm (supportedCubicalAugmentation U c) k a

@[simp]
theorem constantSupportedCochain_apply (U : Set (Fin m → ℝ)) (A : Type*) [AddCommGroup A]
    (a : A) (c : CubicalSupport.normalizedSupportedCubicalChains U 0) :
    constantSupportedCochain U A a c = supportedCubicalAugmentation U c • a := rfl

@[simp]
theorem constantSupportedCochain_point {U : Set (Fin m → ℝ)} {x : Fin m → ℝ}
    (hx : x ∈ U) (A : Type*) [AddCommGroup A] (a : A) :
    constantSupportedCochain U A a (supportedPointChain hx) = a := by
  rw [constantSupportedCochain_apply, supportedCubicalAugmentation_point, one_smul]

/-- Constant zero-cochains are closed on any target subset. -/
theorem constantSupportedCochain_closed (U : Set (Fin m → ℝ)) (A : Type*)
    [AddCommGroup A] (a : A) :
    supportedCubicalCoboundary U A 0 (constantSupportedCochain U A a) = 0 := by
  ext c
  change supportedCubicalAugmentation U (CubicalSupport.supportedNormalizedBoundary U 0 c) • a = 0
  rw [supportedCubicalAugmentation_boundary, zero_smul]

/-- On a nonempty convex target, every closed zero-cochain is determined by
its value at the chosen point. -/
theorem supportedZeroCocycle_apply {U : Set (Fin m → ℝ)} (hU : Convex ℝ U)
    {x₀ : Fin m → ℝ} (hx₀ : x₀ ∈ U) (A : Type*) [AddCommGroup A]
    (φ : SupportedCubicalCochain U A 0) (hφ : supportedCubicalCoboundary U A 0 φ = 0)
    (c : CubicalSupport.normalizedSupportedCubicalChains U 0) :
    φ c = supportedCubicalAugmentation U c • φ (supportedPointChain hx₀) := by
  have hzero : φ (CubicalSupport.supportedNormalizedBoundary U 0 (CubicalSupport.supportedNormalizedPrism hU hx₀ 0 c)) = 0 :=
    congrArg (fun f : SupportedCubicalCochain U A 1 => f (CubicalSupport.supportedNormalizedPrism hU hx₀ 0 c)) hφ
  rw [supportedNormalizedPrism_zero, map_sub, map_smul] at hzero
  exact sub_eq_zero.mp hzero

/-- Constant zero-cochains inject whenever the target contains a point. -/
theorem constantSupportedCochain_injective {U : Set (Fin m → ℝ)}
    {x₀ : Fin m → ℝ} (hx₀ : x₀ ∈ U) (A : Type*) [AddCommGroup A] :
    Function.Injective (constantSupportedCochain U A) := by
  intro a b hab
  have h := congrArg (fun f : SupportedCubicalCochain U A 0 => f (supportedPointChain hx₀)) hab
  simpa only [constantSupportedCochain_point] using h

/-- The kernel of the degree-zero coboundary consists precisely of constant cochains. -/
theorem supportedZeroCocycle_ker_eq_range {U : Set (Fin m → ℝ)} (hU : Convex ℝ U)
    {x₀ : Fin m → ℝ} (hx₀ : x₀ ∈ U) (A : Type*) [AddCommGroup A] :
    LinearMap.ker (supportedCubicalCoboundary U A 0) =
      LinearMap.range (constantSupportedCochain U A) := by
  ext φ
  constructor
  · intro hφ
    refine ⟨φ (supportedPointChain hx₀), ?_⟩
    ext c
    exact (supportedZeroCocycle_apply hU hx₀ A φ hφ c).symm
  · rintro ⟨a, rfl⟩
    exact constantSupportedCochain_closed U A a

/-- The coefficients themselves are canonically the closed zero-cochains on
a nonempty convex target, with inverse evaluation at the selected point. -/
def supportedZeroCocycleEquiv {U : Set (Fin m → ℝ)} (hU : Convex ℝ U)
    {x₀ : Fin m → ℝ} (hx₀ : x₀ ∈ U) (A : Type*) [AddCommGroup A] :
    A ≃ₗ[ℤ] LinearMap.ker (supportedCubicalCoboundary U A 0) :=
  (LinearEquiv.ofInjective (constantSupportedCochain U A)
    (constantSupportedCochain_injective hx₀ A)).trans
      (LinearEquiv.ofEq _ _ (supportedZeroCocycle_ker_eq_range hU hx₀ A).symm)

@[simp]
theorem supportedZeroCocycleEquiv_apply {U : Set (Fin m → ℝ)} (hU : Convex ℝ U)
    {x₀ : Fin m → ℝ} (hx₀ : x₀ ∈ U) (A : Type*) [AddCommGroup A] (a : A) :
    (supportedZeroCocycleEquiv hU hx₀ A a).val = constantSupportedCochain U A a := rfl

/-- The inverse to the constant-cocycle equivalence really is point evaluation. -/
@[simp]
theorem supportedZeroCocycleEquiv_symm_apply {U : Set (Fin m → ℝ)} (hU : Convex ℝ U)
    {x₀ : Fin m → ℝ} (hx₀ : x₀ ∈ U) (A : Type*) [AddCommGroup A]
    (φ : LinearMap.ker (supportedCubicalCoboundary U A 0)) :
    (supportedZeroCocycleEquiv hU hx₀ A).symm φ = φ.val (supportedPointChain hx₀) := by
  have h := congrArg
    (fun ψ : LinearMap.ker (supportedCubicalCoboundary U A 0) => ψ.val (supportedPointChain hx₀))
    ((supportedZeroCocycleEquiv hU hx₀ A).apply_symm_apply φ)
  simpa only [supportedZeroCocycleEquiv_apply, constantSupportedCochain_point] using h

end

end OAI.AlgebraicTopology.DeRham.Comparison.CubicalLocalCochains
