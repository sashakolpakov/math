import OAI.AlgebraicGeometry.CycleClass.Geometric.BarycentricSimplex
import OAI.AlgebraicGeometry.CycleClass.Geometric.SingularChainSupport
import Mathlib.GroupTheory.Perm.Sign
import Mathlib.LinearAlgebra.Finsupp.LinearCombination

/-! # Subdivision Operator -/

namespace OAI.AlgebraicGeometry.CycleClass.Geometric.SubdivisionOperator.Cycles

noncomputable section

/-!
# The actual degreewise barycentric subdivision operator

Each genuine continuous singular simplex is replaced by the signed sum of its
permutation-indexed barycentric subsimplices. The finite-support model extends
this assignment linearly and the proved chain-coordinate equivalence transports
it to mathlib's integral singular chains.

This is only a degreewise linear operator. No commutation with the differential
or subdivision chain homotopy is asserted here.
-/

open _root_.CategoryTheory
open scoped Simplicial BigOperators Classical

/-- The actual index set in degree `n` of integral singular chains. -/
abbrev SingularSimplex (X : TopCat.{0}) (n : ℕ) :=
  (TopCat.toSSet.obj X).obj (.op ⦋n⦌)

/-- A genuine singular simplex precomposed with one barycentric cell map. -/
def subdivisionSimplex (X : TopCat.{0}) (n : ℕ) (s : SingularSimplex X n)
    (σ : Equiv.Perm (Fin (n + 1))) : SingularSimplex X n :=
  (X.toSSetObjEquiv (.op ⦋n⦌)).symm
    ((X.toSSetObjEquiv (.op ⦋n⦌) s).comp (BarycentricSimplex.Cycles.barycentricSubdivisionMap σ))

/-- Geometrically the constructed simplex is exactly the indicated precomposition. -/
@[simp]
theorem subdivisionSimplex_toContinuousMap (X : TopCat.{0}) (n : ℕ)
    (s : SingularSimplex X n) (σ : Equiv.Perm (Fin (n + 1))) :
    X.toSSetObjEquiv (.op ⦋n⦌) (subdivisionSimplex X n s σ) =
      (X.toSSetObjEquiv (.op ⦋n⦌) s).comp (BarycentricSimplex.Cycles.barycentricSubdivisionMap σ) :=
  (X.toSSetObjEquiv (.op ⦋n⦌)).apply_symm_apply _

/-- Subdivision never enlarges the geometric range of a simplex. -/
theorem range_subdivisionSimplex_subset (X : TopCat.{0}) (n : ℕ)
    (s : SingularSimplex X n) (σ : Equiv.Perm (Fin (n + 1))) :
    Set.range (X.toSSetObjEquiv (.op ⦋n⦌) (subdivisionSimplex X n s σ)) ⊆
      Set.range (X.toSSetObjEquiv (.op ⦋n⦌) s) := by
  rw [subdivisionSimplex_toContinuousMap]
  rintro x ⟨t, rfl⟩
  exact ⟨BarycentricSimplex.Cycles.barycentricSubdivisionMap σ t, rfl⟩

/-- The signed barycentric chain associated to one actual singular simplex. -/
def subdivisionGenerator (X : TopCat.{0}) (n : ℕ) (s : SingularSimplex X n) :
    SingularSimplex X n →₀ ℤ :=
  ∑ σ : Equiv.Perm (Fin (n + 1)),
    Finsupp.single (subdivisionSimplex X n s σ) (Equiv.Perm.sign σ : ℤ)

/-- The signed finite sum extended linearly on genuine simplex coefficients. -/
def subdivisionFinsupp (X : TopCat.{0}) (n : ℕ) :
    (SingularSimplex X n →₀ ℤ) →ₗ[ℤ] (SingularSimplex X n →₀ ℤ) :=
  Finsupp.linearCombination ℤ (subdivisionGenerator X n)

/-- The operator is the displayed finite linear combination. -/
theorem subdivisionFinsupp_apply (X : TopCat.{0}) (n : ℕ)
    (c : SingularSimplex X n →₀ ℤ) :
    subdivisionFinsupp X n c =
      ∑ s ∈ c.support, c s • subdivisionGenerator X n s := rfl

/-- Formula on a generator with an arbitrary integer coefficient. -/
@[simp]
theorem subdivisionFinsupp_single (X : TopCat.{0}) (n : ℕ)
    (s : SingularSimplex X n) (a : ℤ) :
    subdivisionFinsupp X n (Finsupp.single s a) =
      ∑ σ : Equiv.Perm (Fin (n + 1)),
        Finsupp.single (subdivisionSimplex X n s σ) ((Equiv.Perm.sign σ : ℤ) * a) := by
  simp [subdivisionFinsupp, subdivisionGenerator, Finset.smul_sum, Finsupp.smul_single,
    mul_comm]

/-- Every nonzero generator term comes from an actual barycentric cell. -/
theorem mem_support_subdivisionGenerator (X : TopCat.{0}) (n : ℕ)
    (s t : SingularSimplex X n) (ht : t ∈ (subdivisionGenerator X n s).support) :
    ∃ σ : Equiv.Perm (Fin (n + 1)), subdivisionSimplex X n s σ = t := by
  obtain ⟨σ, _, hσ⟩ := Finsupp.mem_support_finsetSum t ht
  have hsingle : t ∈ ({subdivisionSimplex X n s σ} : Finset (SingularSimplex X n)) :=
    Finsupp.support_single_subset hσ
  exact ⟨σ, (Finset.mem_singleton.mp hsingle).symm⟩

/-- Every simplex with nonzero subdivided coefficient refines a simplex from
exactly the original finite support; cancellation can only remove terms. -/
theorem mem_support_subdivisionFinsupp (X : TopCat.{0}) (n : ℕ)
    (c : SingularSimplex X n →₀ ℤ) (t : SingularSimplex X n)
    (ht : t ∈ (subdivisionFinsupp X n c).support) :
    ∃ s ∈ c.support, ∃ σ : Equiv.Perm (Fin (n + 1)), subdivisionSimplex X n s σ = t := by
  rw [subdivisionFinsupp_apply] at ht
  obtain ⟨s, hs, hts⟩ := Finsupp.mem_support_finsetSum t ht
  have hgen : t ∈ (subdivisionGenerator X n s).support := Finsupp.support_smul hts
  obtain ⟨σ, hσ⟩ := mem_support_subdivisionGenerator X n s t hgen
  exact ⟨s, hs, σ, hσ⟩

/-- A finite geometric bound on the support, independent of cancellations. -/
theorem support_subdivisionFinsupp_subset (X : TopCat.{0}) (n : ℕ)
    (c : SingularSimplex X n →₀ ℤ) :
    (subdivisionFinsupp X n c).support ⊆ c.support.biUnion (fun s =>
      Finset.univ.image (subdivisionSimplex X n s)) := by
  intro t ht
  obtain ⟨s, hs, σ, hσ⟩ := mem_support_subdivisionFinsupp X n c t ht
  exact Finset.mem_biUnion.mpr ⟨s, hs, Finset.mem_image.mpr ⟨σ, Finset.mem_univ _, hσ⟩⟩

/-- Actual degreewise subdivision on mathlib's integral singular chains. -/
def subdivisionDegree (X : TopCat.{0}) (n : ℕ) :
    (LocalHomology.Cycles.integralSingularChains X).X n →ₗ[ℤ] (LocalHomology.Cycles.integralSingularChains X).X n :=
  (SingularChainSupport.Cycles.singularChainCoefficients X n).symm.toLinearMap ∘ₗ subdivisionFinsupp X n ∘ₗ
    (SingularChainSupport.Cycles.singularChainCoefficients X n).toLinearMap

/-- Its coefficients are exactly the signed finite-support operator. -/
@[simp]
theorem subdivisionDegree_coefficients (X : TopCat.{0}) (n : ℕ)
    (c : (LocalHomology.Cycles.integralSingularChains X).X n) :
    SingularChainSupport.Cycles.singularChainCoefficients X n (subdivisionDegree X n c) =
      subdivisionFinsupp X n (SingularChainSupport.Cycles.singularChainCoefficients X n c) := by
  simp [subdivisionDegree]

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- The concrete simplex-summand formula in the actual chain module. -/
theorem subdivisionDegree_simplex (X : TopCat.{0}) (n : ℕ)
    (s : SingularSimplex X n) (a : ℤ) :
    subdivisionDegree X n ((TopCat.toSSet.obj X).ιChainComplex
      (R := ModuleCat.of ℤ ℤ) s a) =
      ∑ σ : Equiv.Perm (Fin (n + 1)),
        (TopCat.toSSet.obj X).ιChainComplex (R := ModuleCat.of ℤ ℤ)
          (subdivisionSimplex X n s σ) ((Equiv.Perm.sign σ : ℤ) * a) := by
  have hcoeff (t : SingularSimplex X n) (b : ℤ) :
      SingularChainSupport.Cycles.singularChainCoefficients X n
        ((TopCat.toSSet.obj X).ιChainComplex (R := ModuleCat.of ℤ ℤ) t b) =
          Finsupp.single t b := by
    simpa only using! SingularChainSupport.Cycles.singularChainCoefficients_simplex_apply X n t b
  apply (SingularChainSupport.Cycles.singularChainCoefficients X n).injective
  simp only [subdivisionDegree_coefficients, hcoeff,
    subdivisionFinsupp_single, map_sum]

/-- The geometric support formula on the actual singular chain module. -/
theorem mem_support_subdivisionDegree (X : TopCat.{0}) (n : ℕ)
    (c : (LocalHomology.Cycles.integralSingularChains X).X n) (t : SingularSimplex X n)
    (ht : t ∈ SingularChainSupport.Cycles.singularChainSupport (subdivisionDegree X n c)) :
    ∃ s ∈ SingularChainSupport.Cycles.singularChainSupport c, ∃ σ : Equiv.Perm (Fin (n + 1)),
      subdivisionSimplex X n s σ = t := by
  change t ∈ (SingularChainSupport.Cycles.singularChainCoefficients X n (subdivisionDegree X n c)).support at ht
  rw [subdivisionDegree_coefficients] at ht
  exact mem_support_subdivisionFinsupp X n (SingularChainSupport.Cycles.singularChainCoefficients X n c) t ht

/-- Consequently each subdivided support simplex has range contained in the
range of some original support simplex. -/
theorem support_subdivisionDegree_range (X : TopCat.{0}) (n : ℕ)
    (c : (LocalHomology.Cycles.integralSingularChains X).X n) (t : SingularSimplex X n)
    (ht : t ∈ SingularChainSupport.Cycles.singularChainSupport (subdivisionDegree X n c)) :
    ∃ s ∈ SingularChainSupport.Cycles.singularChainSupport c,
      Set.range (X.toSSetObjEquiv (.op ⦋n⦌) t) ⊆
        Set.range (X.toSSetObjEquiv (.op ⦋n⦌) s) := by
  obtain ⟨s, hs, σ, rfl⟩ := mem_support_subdivisionDegree X n c t ht
  exact ⟨s, hs, range_subdivisionSimplex_subset X n s σ⟩

end

end OAI.AlgebraicGeometry.CycleClass.Geometric.SubdivisionOperator.Cycles
