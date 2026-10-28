import OAI.AlgebraicTopology.DeRham.Comparison.StokesF
import OAI.AlgebraicTopology.DeRham.Comparison.CubicalDegenerateQ
import OAI.AlgebraicTopology.DeRham.Comparison.CubicalDegeneracies
import Mathlib.LinearAlgebra.Finsupp.Defs
import Mathlib.Analysis.Convex.Basic

/-! # Cubical Prism -/

namespace OAI.AlgebraicTopology.DeRham.Comparison.CubicalPrism

noncomputable section

/-!
# The straight-line smooth cubical prism

The first coordinate is the homotopy parameter. This file constructs the
actual smooth prism from a cube to a fixed point of its Euclidean target.
-/

open OAI.AlgebraicTopology.DeRham.Comparison.StokesF.SingularCubeStokes
open scoped ContDiff

variable {n m : ℕ}

/-- The straight-line prism, with its homotopy parameter in coordinate zero. -/
def prismCube (x₀ : Fin m → ℝ) (σ : StokesF.SingularCubeStokes.SmoothSingularCube n m) :
    StokesF.SingularCubeStokes.SmoothSingularCube (n + 1) m where
  toFun := fun t => t 0 • σ (Fin.tail t) + (1 - t 0) • x₀
  smooth := by
    have ht : ContDiff ℝ ∞ (fun t : Fin (n + 1) → ℝ => t 0) :=
      contDiff_apply (𝕜 := ℝ) (E := ℝ) 0
    have htail : ContDiff ℝ ∞ (Fin.tail : (Fin (n + 1) → ℝ) → (Fin n → ℝ)) :=
      contDiff_pi.mpr fun i => contDiff_apply (𝕜 := ℝ) (E := ℝ) i.succ
    exact (ht.smul (σ.smooth.comp htail)).add
      ((contDiff_const.sub ht).smul contDiff_const)

@[simp]
theorem prismCube_apply (x₀ : Fin m → ℝ) (σ : StokesF.SingularCubeStokes.SmoothSingularCube n m)
    (t : Fin (n + 1) → ℝ) :
    prismCube x₀ σ t = t 0 • σ (Fin.tail t) + (1 - t 0) • x₀ := rfl

@[simp]
theorem prismCube_face_one (x₀ : Fin m → ℝ) (σ : StokesF.SingularCubeStokes.SmoothSingularCube n m) :
    StokesF.SingularCubeStokes.singularFace (prismCube x₀ σ) 0 1 = σ := by
  apply StokesF.Stokes.Cube.ext
  funext t
  change (Fin.insertNth (α := fun _ => ℝ) 0 1 t) 0 • σ (Fin.tail (Fin.insertNth (α := fun _ => ℝ) 0 1 t)) +
      (1 - (Fin.insertNth (α := fun _ => ℝ) 0 1 t) 0) • x₀ = σ t
  simp only [Fin.insertNth_zero', Fin.cons_zero, Fin.tail_cons, one_smul,
    sub_self, zero_smul, add_zero]

@[simp]
theorem prismCube_face_zero (x₀ : Fin m → ℝ) (σ : StokesF.SingularCubeStokes.SmoothSingularCube n m) :
    StokesF.SingularCubeStokes.singularFace (prismCube x₀ σ) 0 0 = CubicalDegeneracies.constantSmoothCube n x₀ := by
  apply StokesF.Stokes.Cube.ext
  funext t
  change (Fin.insertNth (α := fun _ => ℝ) 0 0 t) 0 • σ (Fin.tail (Fin.insertNth (α := fun _ => ℝ) 0 0 t)) +
      (1 - (Fin.insertNth (α := fun _ => ℝ) 0 0 t) 0) • x₀ = x₀
  simp only [Fin.insertNth_zero', Fin.cons_zero, Fin.tail_cons, zero_smul,
    sub_zero, one_smul, zero_add]

/-- All other prism faces are the corresponding prisms on cube faces. -/
theorem prismCube_face_succ (x₀ : Fin m → ℝ) (σ : StokesF.SingularCubeStokes.SmoothSingularCube (n + 1) m)
    (i : Fin (n + 1)) (ε : ℝ) :
    StokesF.SingularCubeStokes.singularFace (prismCube x₀ σ) i.succ ε =
      prismCube x₀ (StokesF.SingularCubeStokes.singularFace σ i ε) := by
  apply StokesF.Stokes.Cube.ext
  funext t
  change (Fin.insertNth (α := fun _ => ℝ) i.succ ε t) 0 • σ (Fin.tail (Fin.insertNth (α := fun _ => ℝ) i.succ ε t)) +
      (1 - (Fin.insertNth (α := fun _ => ℝ) i.succ ε t) 0) • x₀ =
    t 0 • σ (Fin.insertNth (α := fun _ => ℝ) i ε (Fin.tail t)) + (1 - t 0) • x₀
  have hparam : Fin.insertNth (α := fun _ => ℝ) i.succ ε t =
      Fin.cons (t 0) (Fin.insertNth (α := fun _ => ℝ) i ε (Fin.tail t)) := by
    calc
      Fin.insertNth (α := fun _ => ℝ) i.succ ε t =
          Fin.insertNth (α := fun _ => ℝ) i.succ ε (Fin.cons (t 0) (Fin.tail t)) :=
        congrArg (Fin.insertNth (α := fun _ => ℝ) i.succ ε) (Fin.cons_self_tail t).symm
      _ = _ := Fin.insertNth_succ_cons i ε (t 0) (Fin.tail t)
  rw [hparam]
  simp only [Fin.cons_zero, Fin.tail_cons]

/-- The prism extends integer-linearly to the actual free cubical chain group. -/
def prismOperator (n m : ℕ) (x₀ : Fin m → ℝ) :
    StokesF.SingularCubeStokes.SingularChain n m →ₗ[ℤ] StokesF.SingularCubeStokes.SingularChain (n + 1) m :=
  Finsupp.lmapDomain ℤ ℤ (prismCube x₀)

/-- The map sending each cube to the constant cube of the same degree. -/
def constantCubeOperator (n m : ℕ) (x₀ : Fin m → ℝ) :
    StokesF.SingularCubeStokes.SingularChain n m →ₗ[ℤ] StokesF.SingularCubeStokes.SingularChain n m :=
  Finsupp.lmapDomain ℤ ℤ (fun _ => CubicalDegeneracies.constantSmoothCube n x₀)

@[simp]
theorem prismOperator_single (x₀ : Fin m → ℝ) (σ : StokesF.SingularCubeStokes.SmoothSingularCube n m) (k : ℤ) :
    prismOperator n m x₀ (Finsupp.single σ k) = Finsupp.single (prismCube x₀ σ) k := by
  simp [prismOperator]

@[simp]
theorem constantCubeOperator_single (x₀ : Fin m → ℝ)
    (σ : StokesF.SingularCubeStokes.SmoothSingularCube n m) (k : ℤ) :
    constantCubeOperator n m x₀ (Finsupp.single σ k) =
      Finsupp.single (CubicalDegeneracies.constantSmoothCube n x₀) k := by
  simp [constantCubeOperator]

/-- The boundary of a prism has its two end faces and the negative side prisms. -/
theorem boundary_prismCube (x₀ : Fin m → ℝ) (σ : StokesF.SingularCubeStokes.SmoothSingularCube (n + 1) m) :
    StokesF.SingularCubeStokes.singularBoundarySingle (prismCube x₀ σ) =
      Finsupp.single σ 1 - Finsupp.single (CubicalDegeneracies.constantSmoothCube (n + 1) x₀) 1 -
        prismOperator n m x₀ (StokesF.SingularCubeStokes.singularBoundarySingle σ) := by
  classical
  unfold StokesF.SingularCubeStokes.singularBoundarySingle StokesF.Stokes.boundaryGenerator
  rw [Fin.sum_univ_succ]
  simp only [prismCube_face_one, prismCube_face_zero, Fin.val_zero, pow_zero,
    zero_add, pow_one, Finsupp.single_neg, sub_eq_add_neg, prismCube_face_succ]
  simp only [map_sum, map_add, prismOperator_single]
  simp only [Fin.val_succ, pow_succ, mul_neg, mul_one, Finsupp.single_neg, neg_neg]
  have hs :
      (∑ i : Fin (n + 1),
        (-Finsupp.single (prismCube x₀ (StokesF.SingularCubeStokes.singularFace σ i 1)) ((-1 : ℤ) ^ (i : ℕ)) +
          Finsupp.single (prismCube x₀ (StokesF.SingularCubeStokes.singularFace σ i 0)) ((-1 : ℤ) ^ (i : ℕ)))) =
      -(∑ i : Fin (n + 1),
        (Finsupp.single (prismCube x₀ (StokesF.SingularCubeStokes.singularFace σ i 1)) ((-1 : ℤ) ^ (i : ℕ)) +
          -Finsupp.single (prismCube x₀ (StokesF.SingularCubeStokes.singularFace σ i 0)) ((-1 : ℤ) ^ (i : ℕ)))) := by
    rw [← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro i _
    abel
  rw [hs]

/-- The straight-line prism identity on arbitrary positive-degree chains. -/
theorem prism_chain_identity (x₀ : Fin m → ℝ) (c : StokesF.SingularCubeStokes.SingularChain (n + 1) m) :
    StokesF.SingularCubeStokes.singularBoundary (prismOperator (n + 1) m x₀ c) +
        prismOperator n m x₀ (StokesF.SingularCubeStokes.singularBoundary c) =
      c - constantCubeOperator (n + 1) m x₀ c := by
  have hoperator :
      (StokesF.Stokes.boundaryLinear (n + 1) m).comp (prismOperator (n + 1) m x₀) +
          (prismOperator n m x₀).comp (StokesF.Stokes.boundaryLinear n m) =
        LinearMap.id - constantCubeOperator (n + 1) m x₀ := by
    apply Finsupp.lhom_ext
    intro σ k
    change StokesF.Stokes.boundary (prismOperator (n + 1) m x₀ (Finsupp.single σ k)) +
        prismOperator n m x₀ (StokesF.Stokes.boundary (Finsupp.single σ k)) =
      Finsupp.single σ k - constantCubeOperator (n + 1) m x₀ (Finsupp.single σ k)
    rw [prismOperator_single, StokesF.Stokes.boundary_generator, StokesF.Stokes.boundary_generator,
      map_smul, constantCubeOperator_single]
    have hgenerator : StokesF.Stokes.boundaryGenerator (prismCube x₀ σ) =
        Finsupp.single σ 1 - Finsupp.single (CubicalDegeneracies.constantSmoothCube (n + 1) x₀) 1 -
          prismOperator n m x₀ (StokesF.Stokes.boundaryGenerator σ) :=
      boundary_prismCube x₀ σ
    rw [hgenerator]
    simp only [smul_sub, Finsupp.smul_single, smul_eq_mul, mul_one]
    abel
  exact LinearMap.congr_fun hoperator c

/-- The degree-zero prism has just its two endpoint faces. -/
theorem boundary_prismCube_zero (x₀ : Fin m → ℝ) (σ : StokesF.SingularCubeStokes.SmoothSingularCube 0 m) :
    StokesF.SingularCubeStokes.singularBoundarySingle (prismCube x₀ σ) =
      Finsupp.single σ 1 - Finsupp.single (CubicalDegeneracies.constantSmoothCube 0 x₀) 1 := by
  classical
  simp [StokesF.SingularCubeStokes.singularBoundarySingle, StokesF.Stokes.boundaryGenerator, sub_eq_add_neg]

/-- The degree-zero version of the prism identity, without an incoming boundary. -/
theorem prism_chain_identity_zero (x₀ : Fin m → ℝ) (c : StokesF.SingularCubeStokes.SingularChain 0 m) :
    StokesF.SingularCubeStokes.singularBoundary (prismOperator 0 m x₀ c) = c - constantCubeOperator 0 m x₀ c := by
  have hoperator : (StokesF.Stokes.boundaryLinear 0 m).comp (prismOperator 0 m x₀) =
      LinearMap.id - constantCubeOperator 0 m x₀ := by
    apply Finsupp.lhom_ext
    intro σ k
    change StokesF.Stokes.boundary (prismOperator 0 m x₀ (Finsupp.single σ k)) =
      Finsupp.single σ k - constantCubeOperator 0 m x₀ (Finsupp.single σ k)
    rw [prismOperator_single, constantCubeOperator_single,
      StokesF.Stokes.boundary_generator]
    have hgenerator : StokesF.Stokes.boundaryGenerator (prismCube x₀ σ) =
        Finsupp.single σ 1 - Finsupp.single (CubicalDegeneracies.constantSmoothCube 0 x₀) 1 :=
      boundary_prismCube_zero x₀ σ
    rw [hgenerator]
    simp only [smul_sub, Finsupp.smul_single, smul_eq_mul, mul_one]
  exact LinearMap.congr_fun hoperator c

/-- An ignored cube coordinate remains ignored in the prism, shifted by one. -/
theorem prismCube_ignoresCoordinate (x₀ : Fin m → ℝ) (σ : StokesF.SingularCubeStokes.SmoothSingularCube n m)
    (i : Fin n) (hi : CubicalDegeneracyOperators.IgnoresCoordinate σ i) :
    CubicalDegeneracyOperators.IgnoresCoordinate (prismCube x₀ σ) i.succ := by
  intro x t
  simp only [prismCube_apply, Fin.tail_update_succ,
    Function.update_of_ne (fun h => Fin.succ_ne_zero i h.symm)]
  rw [hi (Fin.tail x) t]

/-- A prism of a degenerate cube is degenerate. -/
theorem isDegenerate_prismCube (x₀ : Fin m → ℝ) (σ : StokesF.SingularCubeStokes.SmoothSingularCube n m)
    (hσ : CubicalDegeneracyOperators.IsDegenerateCube σ) : CubicalDegeneracyOperators.IsDegenerateCube (prismCube x₀ σ) := by
  obtain ⟨i, hi⟩ := hσ
  exact ⟨i.succ, prismCube_ignoresCoordinate x₀ σ i hi⟩

/-- Prism operators preserve the submodule of degenerate chains. -/
theorem degenerateSubmodule_le_comap_prism (n m : ℕ) (x₀ : Fin m → ℝ) :
    CubicalDegenerateQ.degenerateSubmodule n m ≤
      (CubicalDegenerateQ.degenerateSubmodule (n + 1) m).comap (prismOperator n m x₀) := by
  apply Submodule.span_le.mpr
  rintro _ ⟨σ, hσ, rfl⟩
  change prismOperator n m x₀ (Finsupp.single σ 1) ∈ CubicalDegenerateQ.degenerateSubmodule (n + 1) m
  rw [prismOperator_single]
  exact CubicalDegenerateQ.single_mem_degenerateSubmodule _ (isDegenerate_prismCube x₀ σ hσ)

/-- Constant-cube operators also preserve degenerate chains. -/
theorem degenerateSubmodule_le_comap_constant (n m : ℕ) (x₀ : Fin m → ℝ) :
    CubicalDegenerateQ.degenerateSubmodule n m ≤
      (CubicalDegenerateQ.degenerateSubmodule n m).comap (constantCubeOperator n m x₀) := by
  apply Submodule.span_le.mpr
  rintro _ ⟨σ, ⟨i, hi⟩, rfl⟩
  change constantCubeOperator n m x₀ (Finsupp.single σ 1) ∈ CubicalDegenerateQ.degenerateSubmodule n m
  rw [constantCubeOperator_single]
  exact CubicalDegenerateQ.single_mem_degenerateSubmodule _ ⟨i, fun _ _ => rfl⟩

/-- The actual prism induced on normalized smooth cubical chains. -/
def normalizedPrism (n m : ℕ) (x₀ : Fin m → ℝ) :
    CubicalDegenerateQ.NormalizedCubicalChain n m →ₗ[ℤ] CubicalDegenerateQ.NormalizedCubicalChain (n + 1) m :=
  (CubicalDegenerateQ.degenerateSubmodule n m).mapQ (CubicalDegenerateQ.degenerateSubmodule (n + 1) m)
    (prismOperator n m x₀) (degenerateSubmodule_le_comap_prism n m x₀)

/-- The constant-cube operator induced on normalized chains. -/
def normalizedConstant (n m : ℕ) (x₀ : Fin m → ℝ) :
    CubicalDegenerateQ.NormalizedCubicalChain n m →ₗ[ℤ] CubicalDegenerateQ.NormalizedCubicalChain n m :=
  (CubicalDegenerateQ.degenerateSubmodule n m).mapQ (CubicalDegenerateQ.degenerateSubmodule n m)
    (constantCubeOperator n m x₀) (degenerateSubmodule_le_comap_constant n m x₀)

@[simp]
theorem normalizedPrism_mk (x₀ : Fin m → ℝ) (c : StokesF.SingularCubeStokes.SingularChain n m) :
    normalizedPrism n m x₀ ((CubicalDegenerateQ.degenerateSubmodule n m).mkQ c) =
      (CubicalDegenerateQ.degenerateSubmodule (n + 1) m).mkQ (prismOperator n m x₀ c) := rfl

@[simp]
theorem normalizedConstant_mk (x₀ : Fin m → ℝ) (c : StokesF.SingularCubeStokes.SingularChain n m) :
    normalizedConstant n m x₀ ((CubicalDegenerateQ.degenerateSubmodule n m).mkQ c) =
      (CubicalDegenerateQ.degenerateSubmodule n m).mkQ (constantCubeOperator n m x₀ c) := rfl

/-- The chain homotopy identity descends through the proved degeneracy quotient. -/
theorem normalized_prism_identity (x₀ : Fin m → ℝ)
    (c : CubicalDegenerateQ.NormalizedCubicalChain (n + 1) m) :
    CubicalDegenerateQ.normalizedBoundary (n + 1) m (normalizedPrism (n + 1) m x₀ c) +
        normalizedPrism n m x₀ (CubicalDegenerateQ.normalizedBoundary n m c) =
      c - normalizedConstant (n + 1) m x₀ c := by
  refine Submodule.Quotient.induction_on (CubicalDegenerateQ.degenerateSubmodule (n + 1) m) c ?_
  intro d
  simpa only [← Submodule.mkQ_apply, normalizedPrism_mk, CubicalDegenerateQ.normalizedBoundary_mk,
    normalizedConstant_mk, map_add, map_sub] using
      congrArg (CubicalDegenerateQ.degenerateSubmodule (n + 1) m).mkQ (prism_chain_identity x₀ d)

/-- The endpoint identity in degree zero also descends to normalized chains. -/
theorem normalized_prism_identity_zero (x₀ : Fin m → ℝ)
    (c : CubicalDegenerateQ.NormalizedCubicalChain 0 m) :
    CubicalDegenerateQ.normalizedBoundary 0 m (normalizedPrism 0 m x₀ c) =
      c - normalizedConstant 0 m x₀ c := by
  refine Submodule.Quotient.induction_on (CubicalDegenerateQ.degenerateSubmodule 0 m) c ?_
  intro d
  simpa only [← Submodule.mkQ_apply, normalizedPrism_mk, CubicalDegenerateQ.normalizedBoundary_mk,
    normalizedConstant_mk, map_sub] using
      congrArg (CubicalDegenerateQ.degenerateSubmodule 0 m).mkQ (prism_chain_identity_zero x₀ d)

/-- Every positive-dimensional constant cube is degenerate. -/
theorem isDegenerate_constantSmoothCube (n : ℕ) (x₀ : Fin m → ℝ) :
    CubicalDegeneracyOperators.IsDegenerateCube (CubicalDegeneracies.constantSmoothCube (n + 1) x₀) :=
  ⟨0, fun _ _ => rfl⟩

/-- The constant operator takes positive-degree chains into degenerate chains. -/
theorem constantCubeOperator_mem_degenerateSubmodule (x₀ : Fin m → ℝ)
    (c : StokesF.SingularCubeStokes.SingularChain (n + 1) m) :
    constantCubeOperator (n + 1) m x₀ c ∈ CubicalDegenerateQ.degenerateSubmodule (n + 1) m := by
  induction c using Finsupp.induction with
  | zero => simp only [map_zero, Submodule.zero_mem]
  | single_add σ k c hσ hk ih =>
    rw [map_add, constantCubeOperator_single]
    exact Submodule.add_mem _
      (CubicalDegenerateQ.single_coeff_mem_degenerateSubmodule _ (isDegenerate_constantSmoothCube n x₀) k) ih

/-- Positive-dimensional constant chains vanish in the normalized quotient. -/
@[simp]
theorem normalizedConstant_succ (x₀ : Fin m → ℝ)
    (c : CubicalDegenerateQ.NormalizedCubicalChain (n + 1) m) :
    normalizedConstant (n + 1) m x₀ c = 0 := by
  refine Submodule.Quotient.induction_on (CubicalDegenerateQ.degenerateSubmodule (n + 1) m) c ?_
  intro d
  change (CubicalDegenerateQ.degenerateSubmodule (n + 1) m).mkQ
    (constantCubeOperator (n + 1) m x₀ d) = 0
  exact (Submodule.Quotient.mk_eq_zero (CubicalDegenerateQ.degenerateSubmodule (n + 1) m)).mpr
    (constantCubeOperator_mem_degenerateSubmodule x₀ d)

/-- In positive degrees the normalized prism is a contraction of the identity. -/
theorem normalized_prism_contraction (x₀ : Fin m → ℝ)
    (c : CubicalDegenerateQ.NormalizedCubicalChain (n + 1) m) :
    CubicalDegenerateQ.normalizedBoundary (n + 1) m (normalizedPrism (n + 1) m x₀ c) +
        normalizedPrism n m x₀ (CubicalDegenerateQ.normalizedBoundary n m c) = c := by
  simpa only [normalizedConstant_succ, sub_zero] using normalized_prism_identity x₀ c

/-- Every positive-degree normalized Euclidean cubical cycle is a boundary. -/
theorem normalized_cycle_is_boundary (x₀ : Fin m → ℝ)
    (c : CubicalDegenerateQ.NormalizedCubicalChain (n + 1) m) (hc : CubicalDegenerateQ.normalizedBoundary n m c = 0) :
    CubicalDegenerateQ.normalizedBoundary (n + 1) m (normalizedPrism (n + 1) m x₀ c) = c := by
  simpa only [hc, map_zero, add_zero] using normalized_prism_contraction x₀ c

/-- The prism stays in a convex target on its parameter cube. -/
theorem prismCube_mapsTo_convex {U : Set (Fin m → ℝ)} (hU : Convex ℝ U)
    {x₀ : Fin m → ℝ} (hx₀ : x₀ ∈ U) (σ : StokesF.SingularCubeStokes.SmoothSingularCube n m)
    (hσ : Set.MapsTo σ (StokesF.SingularCubeStokes.unitCube n) U) :
    Set.MapsTo (prismCube x₀ σ) (StokesF.SingularCubeStokes.unitCube (n + 1)) U := by
  intro t ht
  have htail : Fin.tail t ∈ StokesF.SingularCubeStokes.unitCube n :=
    ⟨fun i => ht.1 i.succ, fun i => ht.2 i.succ⟩
  exact hU (hσ htail) hx₀ (ht.1 0) (sub_nonneg.mpr (ht.2 0)) (by ring)

end

end OAI.AlgebraicTopology.DeRham.Comparison.CubicalPrism
