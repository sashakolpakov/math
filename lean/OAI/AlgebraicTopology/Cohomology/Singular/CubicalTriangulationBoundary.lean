import OAI.AlgebraicTopology.DeRham.Comparison.StokesF
import OAI.AlgebraicTopology.Cohomology.Singular.CubicalCancellation
import OAI.AlgebraicTopology.Cohomology.Singular.CubicalPermutationSigns
import OAI.AlgebraicTopology.Cohomology.Singular.CubicalPermutationReindex
import OAI.AlgebraicTopology.Cohomology.Singular.NormalizedCubicalTriangulation
import OAI.AlgebraicTopology.DeRham.Comparison.CubicalDegenerateQ

/-! # Cubical Triangulation Boundary -/

namespace OAI.AlgebraicTopology.Cohomology.Singular.CubicalTriangulationBoundary

noncomputable section

/-!
# Boundary compatibility of actual cubical triangulation

The signed sum of permutation simplices respects the actual cubical and
simplicial boundaries. Internal faces cancel, and the endpoint faces reindex
to the signed triangulations of cube faces. The resulting degreewise map
descends to the existing normalized cubical quotient.
-/

open _root_.CategoryTheory
open OAI.AlgebraicTopology.DeRham.Comparison.CubicalDegenerateQ
open scoped BigOperators Simplicial

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

variable {n m : ℕ}

private theorem integerSmulSum {A ι : Type*} [AddCommGroup A]
    (r : ℤ) (s : Finset ι) (f : ι → A) :
    r • (∑ i ∈ s, f i) = ∑ i ∈ s, r • f i := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih => simp only [Finset.sum_insert hi, zsmul_add, ih]

/-- The simplex boundary indices split into the two endpoints and the internal faces. -/
theorem sum_cubeFace_endpoints {A : Type*} [AddCommMonoid A] (F : Fin (n + 2) → A) :
    ∑ k, F k = F 0 + F (Fin.last (n + 1)) + ∑ k ∈ CubicalCancellation.cubeInternalFaceIndices n, F k := by
  classical
  have hi : CubicalCancellation.cubeInternalFaceIndices n =
      (Finset.univ.erase (0 : Fin (n + 2))).erase (Fin.last (n + 1)) := by
    ext k
    simp only [CubicalCancellation.cubeInternalFaceIndices, Finset.mem_filter, Finset.mem_univ, true_and,
      Finset.mem_erase, and_true, Fin.ne_iff_vne, Fin.val_zero, Fin.val_last]
    omega
  have hlast : Fin.last (n + 1) ∈ Finset.univ.erase (0 : Fin (n + 2)) := by
    simp [Fin.ext_iff]
  calc
    ∑ k, F k = F 0 + ∑ k ∈ Finset.univ.erase (0 : Fin (n + 2)), F k :=
      (Finset.add_sum_erase Finset.univ F (Finset.mem_univ 0)).symm
    _ = F 0 + (F (Fin.last (n + 1)) + ∑ k ∈ CubicalCancellation.cubeInternalFaceIndices n, F k) := by
      rw [hi, Finset.add_sum_erase _ F hlast]
    _ = _ := (add_assoc _ _ _).symm

/-- The actual simplicial boundary of one permutation simplex. -/
theorem cubeSimplexChain_boundary
    (cube : DeRham.Comparison.StokesF.SingularCubeStokes.SmoothSingularCube (n + 1) m)
    (σ : Equiv.Perm (Fin (n + 1))) :
    (NormalizedCubicalTriangulation.smoothIntegralChains m).d (n + 1) n
        (((Smooth.smoothSingularSubcomplex (Fin m → ℝ)).toSSet.ιChainComplex
          (R := ModuleCat.of ℤ ℤ) (CubicalTriangulation.triangulatedCubeSmoothSimplex cube σ)) 1) =
      ∑ k : Fin (n + 2), (-1 : ℤ) ^ k.val •
        CubicalCancellation.smoothCubeFaceChain (ModuleCat.of ℤ ℤ) cube σ k 1 := by
  change (((Smooth.smoothSingularSubcomplex (Fin m → ℝ)).toSSet.ιChainComplex
      (R := ModuleCat.of ℤ ℤ) (CubicalTriangulation.triangulatedCubeSmoothSimplex cube σ) ≫
      ((Smooth.smoothSingularSubcomplex (Fin m → ℝ)).toSSet.chainComplex
        (ModuleCat.of ℤ ℤ)).d (n + 1) n).hom) (1 : ℤ) = _
  rw [SSet.ιChainComplex_d]
  simp only [ModuleCat.hom_sum, LinearMap.sum_apply, ModuleCat.hom_zsmul,
    CubicalCancellation.smoothCubeFaceChain]
  apply Finset.sum_congr rfl
  intro k _
  exact map_zsmul
    (LinearMap.evalAddMonoidHom (σ₁₂ := RingHom.id ℤ)
      (M₂ := (NormalizedCubicalTriangulation.smoothIntegralChains m).X n) (1 : ℤ))
    ((-1 : ℤ) ^ k.val)
    (((Smooth.smoothSingularSubcomplex (Fin m → ℝ)).toSSet.ιChainComplex
      (R := ModuleCat.of ℤ ℤ)
      ((Smooth.smoothSingularSubcomplex (Fin m → ℝ)).toSSet.δ k
        (CubicalTriangulation.triangulatedCubeSmoothSimplex cube σ))).hom)

/-- Internal faces cancel in the boundary of the actual signed cube triangulation. -/
theorem signedCubeTriangulation_boundary_endpoints
    (cube : DeRham.Comparison.StokesF.SingularCubeStokes.SmoothSingularCube (n + 1) m) :
    (NormalizedCubicalTriangulation.smoothIntegralChains m).d (n + 1) n (NormalizedCubicalTriangulation.signedCubeTriangulation cube) =
      (∑ σ : Equiv.Perm (Fin (n + 1)), (Equiv.Perm.sign σ : ℤ) •
        CubicalCancellation.smoothCubeFaceChain (ModuleCat.of ℤ ℤ) cube σ 0 1) +
      ∑ σ : Equiv.Perm (Fin (n + 1)),
        ((Equiv.Perm.sign σ : ℤ) * (-1 : ℤ) ^ (n + 1)) •
          CubicalCancellation.smoothCubeFaceChain (ModuleCat.of ℤ ℤ) cube σ (Fin.last (n + 1)) 1 := by
  have he : (NormalizedCubicalTriangulation.smoothIntegralChains m).d (n + 1) n (NormalizedCubicalTriangulation.signedCubeTriangulation cube) =
      ∑ σ : Equiv.Perm (Fin (n + 1)), ∑ k : Fin (n + 2),
        (Equiv.Perm.sign σ : ℤ) • ((-1 : ℤ) ^ k.val •
          CubicalCancellation.smoothCubeFaceChain (ModuleCat.of ℤ ℤ) cube σ k 1) := by
    simp only [NormalizedCubicalTriangulation.signedCubeTriangulation, map_sum, map_zsmul]
    apply Finset.sum_congr rfl
    intro σ _
    rw [cubeSimplexChain_boundary]
    exact integerSmulSum (r := (Equiv.Perm.sign σ : ℤ)) (s := Finset.univ)
      (f := fun k : Fin (n + 2) => (-1 : ℤ) ^ k.val •
        CubicalCancellation.smoothCubeFaceChain (ModuleCat.of ℤ ℤ) cube σ k 1)
  rw [he]
  simp_rw [sum_cubeFace_endpoints]
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib]
  have hi := CubicalCancellation.smoothCubeInternalBoundaryChain_eq_zero (ModuleCat.of ℤ ℤ) cube (1 : ℤ)
  dsimp only [CubicalCancellation.smoothCubeInternalBoundaryChain] at hi
  rw [hi, add_zero]
  simp only [Fin.val_zero, pow_zero, one_zsmul, Fin.val_last, smul_smul]

/-- First simplex faces collect to the upper faces of the cube with their cubical signs. -/
theorem signedCubeTriangulation_firstEndpoints
    (cube : DeRham.Comparison.StokesF.SingularCubeStokes.SmoothSingularCube (n + 1) m) :
    (∑ σ : Equiv.Perm (Fin (n + 1)), (Equiv.Perm.sign σ : ℤ) •
      CubicalCancellation.smoothCubeFaceChain (ModuleCat.of ℤ ℤ) cube σ 0 1) =
    ∑ i : Fin (n + 1), (-1 : ℤ) ^ i.val •
      NormalizedCubicalTriangulation.signedCubeTriangulation (DeRham.Comparison.StokesF.SingularCubeStokes.singularFace cube i 1) := by
  calc
    _ = ∑ σ : Equiv.Perm (Fin (n + 1)),
        ((-1 : ℤ) ^ (σ 0).val * (Equiv.Perm.sign (CubicalEndpointFaces.eraseCubePermutation σ 0) : ℤ)) •
        ((Smooth.smoothSingularSubcomplex (Fin m → ℝ)).toSSet.ιChainComplex
          (R := ModuleCat.of ℤ ℤ) (CubicalTriangulation.triangulatedCubeSmoothSimplex
            (DeRham.Comparison.StokesF.SingularCubeStokes.singularFace cube (σ 0) 1) (CubicalEndpointFaces.eraseCubePermutation σ 0))) 1 := by
      apply Finset.sum_congr rfl
      intro σ _
      rw [CubicalPermutationSigns.cubePermutation_firstBoundarySign]
      unfold CubicalCancellation.smoothCubeFaceChain
      rw [CubicalEndpointFaces.triangulatedCubeSmoothSimplex_firstFace]
    _ = ∑ i : Fin (n + 1), ∑ τ : Equiv.Perm (Fin n),
        ((-1 : ℤ) ^ i.val * (Equiv.Perm.sign τ : ℤ)) •
        ((Smooth.smoothSingularSubcomplex (Fin m → ℝ)).toSSet.ιChainComplex
          (R := ModuleCat.of ℤ ℤ) (CubicalTriangulation.triangulatedCubeSmoothSimplex
            (DeRham.Comparison.StokesF.SingularCubeStokes.singularFace cube i 1) τ)) 1 :=
      CubicalPermutationReindex.sum_eraseCubePermutation (0 : Fin (n + 1)) (fun i τ =>
        ((-1 : ℤ) ^ i.val * (Equiv.Perm.sign τ : ℤ)) •
        ((Smooth.smoothSingularSubcomplex (Fin m → ℝ)).toSSet.ιChainComplex
          (R := ModuleCat.of ℤ ℤ) (CubicalTriangulation.triangulatedCubeSmoothSimplex
            (DeRham.Comparison.StokesF.SingularCubeStokes.singularFace cube i 1) τ)) 1)
    _ = _ := by
      simp only [NormalizedCubicalTriangulation.signedCubeTriangulation, mul_smul]
      apply Finset.sum_congr rfl
      intro i _
      exact (integerSmulSum (r := (-1 : ℤ) ^ i.val) (s := Finset.univ)
        (f := fun τ : Equiv.Perm (Fin n) => (Equiv.Perm.sign τ : ℤ) •
          ((Smooth.smoothSingularSubcomplex (Fin m → ℝ)).toSSet.ιChainComplex
            (R := ModuleCat.of ℤ ℤ) (CubicalTriangulation.triangulatedCubeSmoothSimplex
              (DeRham.Comparison.StokesF.SingularCubeStokes.singularFace cube i 1) τ)) 1)).symm

/-- Last simplex faces collect to the lower faces of the cube with their cubical signs. -/
theorem signedCubeTriangulation_lastEndpoints
    (cube : DeRham.Comparison.StokesF.SingularCubeStokes.SmoothSingularCube (n + 1) m) :
    (∑ σ : Equiv.Perm (Fin (n + 1)),
      ((Equiv.Perm.sign σ : ℤ) * (-1 : ℤ) ^ (n + 1)) •
        CubicalCancellation.smoothCubeFaceChain (ModuleCat.of ℤ ℤ) cube σ (Fin.last (n + 1)) 1) =
    ∑ i : Fin (n + 1), (-1 : ℤ) ^ (i.val + 1) •
      NormalizedCubicalTriangulation.signedCubeTriangulation (DeRham.Comparison.StokesF.SingularCubeStokes.singularFace cube i 0) := by
  calc
    _ = ∑ σ : Equiv.Perm (Fin (n + 1)),
        ((-1 : ℤ) ^ ((σ (Fin.last n)).val + 1) *
          (Equiv.Perm.sign (CubicalEndpointFaces.eraseCubePermutation σ (Fin.last n)) : ℤ)) •
        ((Smooth.smoothSingularSubcomplex (Fin m → ℝ)).toSSet.ιChainComplex
          (R := ModuleCat.of ℤ ℤ) (CubicalTriangulation.triangulatedCubeSmoothSimplex
            (DeRham.Comparison.StokesF.SingularCubeStokes.singularFace cube (σ (Fin.last n)) 0)
            (CubicalEndpointFaces.eraseCubePermutation σ (Fin.last n)))) 1 := by
      apply Finset.sum_congr rfl
      intro σ _
      rw [CubicalPermutationSigns.cubePermutation_lastBoundarySign]
      unfold CubicalCancellation.smoothCubeFaceChain
      rw [CubicalEndpointFaces.triangulatedCubeSmoothSimplex_lastFace]
      simp only [pow_succ, mul_neg_one, neg_mul]
    _ = ∑ i : Fin (n + 1), ∑ τ : Equiv.Perm (Fin n),
        ((-1 : ℤ) ^ (i.val + 1) * (Equiv.Perm.sign τ : ℤ)) •
        ((Smooth.smoothSingularSubcomplex (Fin m → ℝ)).toSSet.ιChainComplex
          (R := ModuleCat.of ℤ ℤ) (CubicalTriangulation.triangulatedCubeSmoothSimplex
            (DeRham.Comparison.StokesF.SingularCubeStokes.singularFace cube i 0) τ)) 1 :=
      CubicalPermutationReindex.sum_eraseCubePermutation (Fin.last n) (fun i τ =>
        ((-1 : ℤ) ^ (i.val + 1) * (Equiv.Perm.sign τ : ℤ)) •
        ((Smooth.smoothSingularSubcomplex (Fin m → ℝ)).toSSet.ιChainComplex
          (R := ModuleCat.of ℤ ℤ) (CubicalTriangulation.triangulatedCubeSmoothSimplex
            (DeRham.Comparison.StokesF.SingularCubeStokes.singularFace cube i 0) τ)) 1)
    _ = _ := by
      simp only [NormalizedCubicalTriangulation.signedCubeTriangulation, mul_smul]
      apply Finset.sum_congr rfl
      intro i _
      exact (integerSmulSum (r := (-1 : ℤ) ^ (i.val + 1)) (s := Finset.univ)
        (f := fun τ : Equiv.Perm (Fin n) => (Equiv.Perm.sign τ : ℤ) •
          ((Smooth.smoothSingularSubcomplex (Fin m → ℝ)).toSSet.ιChainComplex
            (R := ModuleCat.of ℤ ℤ) (CubicalTriangulation.triangulatedCubeSmoothSimplex
              (DeRham.Comparison.StokesF.SingularCubeStokes.singularFace cube i 0) τ)) 1)).symm

/-- The boundary of signed permutation triangulation is the signed triangulation
of the actual cubical boundary, before either normalization quotient. -/
theorem signedCubeTriangulation_boundary
    (cube : DeRham.Comparison.StokesF.SingularCubeStokes.SmoothSingularCube (n + 1) m) :
    (NormalizedCubicalTriangulation.smoothIntegralChains m).d (n + 1) n (NormalizedCubicalTriangulation.signedCubeTriangulation cube) =
      ∑ i : Fin (n + 1),
        ((-1 : ℤ) ^ i.val • NormalizedCubicalTriangulation.signedCubeTriangulation (DeRham.Comparison.StokesF.SingularCubeStokes.singularFace cube i 1) +
        (-1 : ℤ) ^ (i.val + 1) •
          NormalizedCubicalTriangulation.signedCubeTriangulation (DeRham.Comparison.StokesF.SingularCubeStokes.singularFace cube i 0)) := by
  rw [signedCubeTriangulation_boundary_endpoints,
    signedCubeTriangulation_firstEndpoints, signedCubeTriangulation_lastEndpoints,
    Finset.sum_add_distrib]

/-- The same actual boundary identity holds after simplicial normalization. -/
theorem normalizedCubeTriangulation_boundary
    (cube : DeRham.Comparison.StokesF.SingularCubeStokes.SmoothSingularCube (n + 1) m) :
    (NormalizedCubicalTriangulation.normalizedSmoothIntegralChains m).d (n + 1) n (NormalizedCubicalTriangulation.normalizedCubeTriangulation cube) =
      NormalizedCubicalTriangulation.cubicalToNormalizedSimplicialLinear n m (DeRham.Comparison.StokesF.SingularCubeStokes.singularBoundarySingle cube) := by
  have hcomm := ConcreteCategory.congr_hom
    (((Smooth.smoothSingularSubcomplex (Fin m → ℝ)).toSSet.toNormalizedChainComplex
      (ModuleCat.of ℤ ℤ)).comm (n + 1) n) (NormalizedCubicalTriangulation.signedCubeTriangulation cube)
  change (NormalizedCubicalTriangulation.normalizedSmoothIntegralChains m).d (n + 1) n
      (((Smooth.smoothSingularSubcomplex (Fin m → ℝ)).toSSet.toNormalizedChainComplex
        (ModuleCat.of ℤ ℤ)).f (n + 1) (NormalizedCubicalTriangulation.signedCubeTriangulation cube)) =
    ((Smooth.smoothSingularSubcomplex (Fin m → ℝ)).toSSet.toNormalizedChainComplex
      (ModuleCat.of ℤ ℤ)).f n
        ((NormalizedCubicalTriangulation.smoothIntegralChains m).d (n + 1) n (NormalizedCubicalTriangulation.signedCubeTriangulation cube)) at hcomm
  rw [NormalizedCubicalTriangulation.signedCubeTriangulation_normalize] at hcomm
  rw [hcomm, signedCubeTriangulation_boundary]
  simp only [DeRham.Comparison.StokesF.SingularCubeStokes.singularBoundarySingle, DeRham.Comparison.StokesF.Stokes.boundaryGenerator, map_sum, map_add, map_zsmul,
    NormalizedCubicalTriangulation.signedCubeTriangulation_normalize, NormalizedCubicalTriangulation.cubicalToNormalizedSimplicialLinear_single]

/-- Linear extension of signed triangulation intertwines the two genuine boundaries. -/
theorem cubicalToNormalizedSimplicialLinear_boundary (n m : ℕ) :
    ((NormalizedCubicalTriangulation.normalizedSmoothIntegralChains m).d (n + 1) n).hom.comp
        (NormalizedCubicalTriangulation.cubicalToNormalizedSimplicialLinear (n + 1) m) =
      (NormalizedCubicalTriangulation.cubicalToNormalizedSimplicialLinear n m).comp (DeRham.Comparison.CubicalDegenerateQ.cubicalBoundaryLinear n m) := by
  change ((NormalizedCubicalTriangulation.normalizedSmoothIntegralChains m).d (n + 1) n).hom.comp
      (Finsupp.linearCombination ℤ NormalizedCubicalTriangulation.normalizedCubeTriangulation) =
    (NormalizedCubicalTriangulation.cubicalToNormalizedSimplicialLinear n m).comp
      (Finsupp.linearCombination ℤ DeRham.Comparison.StokesF.Stokes.boundaryGenerator)
  calc
    _ = Finsupp.linearCombination ℤ
        (((NormalizedCubicalTriangulation.normalizedSmoothIntegralChains m).d (n + 1) n).hom ∘
          NormalizedCubicalTriangulation.normalizedCubeTriangulation) :=
      (Finsupp.linearCombination_linear_comp ℤ
        ((NormalizedCubicalTriangulation.normalizedSmoothIntegralChains m).d (n + 1) n).hom).symm
    _ = Finsupp.linearCombination ℤ
        (NormalizedCubicalTriangulation.cubicalToNormalizedSimplicialLinear n m ∘ DeRham.Comparison.StokesF.Stokes.boundaryGenerator) := by
      congr 1
      funext cube
      exact normalizedCubeTriangulation_boundary cube
    _ = _ := Finsupp.linearCombination_linear_comp ℤ
      (NormalizedCubicalTriangulation.cubicalToNormalizedSimplicialLinear n m)

/-- Boundary compatibility descends through the actual cubical degeneracy quotient. -/
theorem normalizedCubicalTriangulation_boundary
    (c : DeRham.Comparison.CubicalDegenerateQ.NormalizedCubicalChain (n + 1) m) :
    (NormalizedCubicalTriangulation.normalizedSmoothIntegralChains m).d (n + 1) n (NormalizedCubicalTriangulation.normalizedCubicalTriangulation (n + 1) m c) =
      NormalizedCubicalTriangulation.normalizedCubicalTriangulation n m (DeRham.Comparison.CubicalDegenerateQ.normalizedBoundary n m c) := by
  refine Submodule.Quotient.induction_on (DeRham.Comparison.CubicalDegenerateQ.degenerateSubmodule (n + 1) m) c ?_
  intro d
  change (NormalizedCubicalTriangulation.normalizedSmoothIntegralChains m).d (n + 1) n
      (NormalizedCubicalTriangulation.cubicalToNormalizedSimplicialLinear (n + 1) m d) =
    NormalizedCubicalTriangulation.cubicalToNormalizedSimplicialLinear n m (DeRham.Comparison.StokesF.SingularCubeStokes.singularBoundary d)
  exact LinearMap.congr_fun (cubicalToNormalizedSimplicialLinear_boundary n m) d

/-- The actual normalized cubical chain complex, with its already proved quotient boundary. -/
def normalizedCubicalChainComplex (m : ℕ) : ChainComplex (ModuleCat.{0} ℤ) ℕ :=
  ChainComplex.of (fun n => ModuleCat.of ℤ (DeRham.Comparison.CubicalDegenerateQ.NormalizedCubicalChain n m))
    (fun n => ModuleCat.ofHom (DeRham.Comparison.CubicalDegenerateQ.normalizedBoundary n m))
    (fun n => by
      apply ModuleCat.hom_ext
      apply LinearMap.ext
      intro c
      exact DeRham.Comparison.CubicalDegenerateQ.normalizedBoundary_sq_zero c)

/-- The packaged cubical complex uses the given boundary in every successive degree. -/
@[simp]
theorem normalizedCubicalChainComplex_d (m n : ℕ) :
    (normalizedCubicalChainComplex m).d (n + 1) n = ModuleCat.ofHom (DeRham.Comparison.CubicalDegenerateQ.normalizedBoundary n m) :=
  ChainComplex.of_d (fun j => ModuleCat.of ℤ (DeRham.Comparison.CubicalDegenerateQ.NormalizedCubicalChain j m))
    (fun j => ModuleCat.ofHom (DeRham.Comparison.CubicalDegenerateQ.normalizedBoundary j m)) n

/-- The actual signed cubical triangulation as a map of normalized chain complexes. -/
def normalizedCubicalTriangulationChainMap (m : ℕ) :
    normalizedCubicalChainComplex m ⟶ NormalizedCubicalTriangulation.normalizedSmoothIntegralChains m :=
  ChainComplex.ofHom (fun n => ModuleCat.ofHom (NormalizedCubicalTriangulation.normalizedCubicalTriangulation n m))
    (fun n => by
      rw [normalizedCubicalChainComplex_d]
      apply ModuleCat.hom_ext
      apply LinearMap.ext
      intro c
      exact normalizedCubicalTriangulation_boundary c)

/-- Each chain-map component is exactly the previously constructed signed quotient map. -/
@[simp]
theorem normalizedCubicalTriangulationChainMap_f (m n : ℕ) :
    (normalizedCubicalTriangulationChainMap m).f n =
      ModuleCat.ofHom (NormalizedCubicalTriangulation.normalizedCubicalTriangulation n m) := rfl

end

end OAI.AlgebraicTopology.Cohomology.Singular.CubicalTriangulationBoundary
