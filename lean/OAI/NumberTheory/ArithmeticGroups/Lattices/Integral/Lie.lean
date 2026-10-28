import OAI.NumberTheory.ArithmeticGroups.Lattices.Lie.CharacteristicGap
import OAI.NumberTheory.ArithmeticGroups.Lattices.ExponentialNormal
import Mathlib.RingTheory.Localization.Integer

/-! # Lie -/

namespace OAI.NumberTheory.ArithmeticGroups.Lattices.Integral.Lie.Construction

noncomputable section

section

/-! Integral matrices in the rational Lie algebra form a finitely
generated full lattice. -/

open scoped Classical _root_.NumberField
open _root_.NumberField

attribute [local instance] LieRing.ofAssociativeRing

def integralMatrixModule {k : Type} [Field k] (n : ℕ) :
    Submodule (𝓞 k) (Matrix (Fin n) (Fin n) k) :=
  ((Algebra.linearMap (𝓞 k) k).mapMatrix (m := Fin n) (n := Fin n)).range

theorem mem_integralMatrixModule {k : Type} [Field k] {n : ℕ}
    (A : Matrix (Fin n) (Fin n) k) :
    A ∈ integralMatrixModule n ↔
      ∃ B : Matrix (Fin n) (Fin n) (𝓞 k), B.map (algebraMap (𝓞 k) k) = A := Iff.rfl

theorem integralMatrixModule_fg {k : Type} [Field k] (n : ℕ) :
    (integralMatrixModule (k := k) n).FG := by
  have h : (⊤ : Submodule (𝓞 k) (Matrix (Fin n) (Fin n) (𝓞 k))).FG := Module.Finite.fg_top
  simpa only [integralMatrixModule, Submodule.map_top] using
    h.map ((Algebra.linearMap (𝓞 k) k).mapMatrix (m := Fin n) (n := Fin n))

def integralLieLattice {k : Type} [Field k] {n : ℕ} (G : Algebraic.MatrixAlgebraicGroup k n) :
    Submodule (𝓞 k) (Infinitesimal.Action.Construction.infinitesimalStabilizer G) :=
  (integralMatrixModule n).comap ((Infinitesimal.Action.Construction.infinitesimalStabilizer G).toSubmodule.subtype.restrictScalars (𝓞 k))

theorem mem_integralLieLattice {k : Type} [Field k] {n : ℕ} (G : Algebraic.MatrixAlgebraicGroup k n)
    (A : Infinitesimal.Action.Construction.infinitesimalStabilizer G) :
    A ∈ integralLieLattice G ↔
      ∃ B : Matrix (Fin n) (Fin n) (𝓞 k), B.map (algebraMap (𝓞 k) k) = A.val := Iff.rfl

theorem integralLieLattice_fg
    {k : Type} [Field k] [NumberField k] {n : ℕ} (G : Algebraic.MatrixAlgebraicGroup k n) :
    (integralLieLattice G).FG := by
  let f := (Infinitesimal.Action.Construction.infinitesimalStabilizer G).toSubmodule.subtype.restrictScalars (𝓞 k)
  apply Submodule.fg_of_fg_map_injective f Subtype.val_injective
  apply (integralMatrixModule_fg n).of_le
  change ((integralMatrixModule n).comap f).map f ≤ integralMatrixModule n
  exact Submodule.map_comap_le _ _

theorem integralLieLattice_denominator
    {k : Type} [Field k] [NumberField k] {n : ℕ}
    (G : Algebraic.MatrixAlgebraicGroup k n) (A : Infinitesimal.Action.Construction.infinitesimalStabilizer G) :
    ∃ d : 𝓞 k, d ≠ 0 ∧ d • A ∈ integralLieLattice G := by
  obtain ⟨d, hd⟩ := IsLocalization.exist_integer_multiples_of_finite (nonZeroDivisors (𝓞 k))
    (fun ij : Fin n × Fin n => A.val ij.1 ij.2)
  choose B hB using hd
  refine ⟨d.val, mem_nonZeroDivisors_iff_ne_zero.mp d.property, ?_⟩
  apply (mem_integralLieLattice G _).mpr
  refine ⟨fun i j => B (i, j), ?_⟩
  ext i j : 1
  exact hB (i, j)

theorem integralLieLattice_full
    {k : Type} [Field k] [NumberField k] {n : ℕ} (G : Algebraic.MatrixAlgebraicGroup k n) :
    Submodule.span k (integralLieLattice G : Set (Infinitesimal.Action.Construction.infinitesimalStabilizer G)) = ⊤ := by
  apply top_unique
  intro A _
  obtain ⟨d, hd, hA⟩ := integralLieLattice_denominator G A
  have hdk : (algebraMap (𝓞 k) k d) ≠ 0 := by
    intro h
    exact hd (Subtype.ext h)
  have h := (Submodule.span k (integralLieLattice G : Set (Infinitesimal.Action.Construction.infinitesimalStabilizer G))).smul_mem
    (algebraMap (𝓞 k) k d)⁻¹ (Submodule.subset_span hA)
  have he : d • A = (algebraMap (𝓞 k) k d) • A := (IsScalarTower.algebraMap_smul k d A).symm
  rwa [he, inv_smul_smul₀ hdk] at h

end

section

/-! The actual standard arithmetic subgroup preserves the integral Lie
lattice through its adjoint action. -/

open scoped Classical _root_.NumberField

theorem standard_arithmetic_adjoint_preserves_integralLieLattice
    {k : Type} [Field k] [NumberField k] {n : ℕ}
    (G : Algebraic.MatrixAlgebraicGroup k n) (g : G.RationalPoints)
    (hg : g ∈ G.latticeStabilizer (IntegralLattice.FullLattice.standard k n))
    (A : Infinitesimal.Action.Construction.infinitesimalStabilizer G) (hA : A ∈ integralLieLattice G) :
    ExponentialNormal.Construction.infinitesimalAdjoint G g A ∈ integralLieLattice G := by
  obtain ⟨B, hB⟩ := (Matrices.Construction.standard_lattice_stabilizer_iff_integral G g).mp hg
  obtain ⟨C, hC⟩ := (mem_integralLieLattice G A).mp hA
  let ι := algebraMap (𝓞 k) k
  have hBv : ι.mapMatrix (B : Matrix (Fin n) (Fin n) (𝓞 k)) =
      (g.val : Matrix (Fin n) (Fin n) k) := congrArg Subtype.val hB
  have hBi : Matrix.SpecialLinearGroup.map ι (B⁻¹) = g.val⁻¹ := by
    rw [map_inv, hB]
  have hBiv : ι.mapMatrix ((B⁻¹ : Matrix.SpecialLinearGroup (Fin n) (𝓞 k)) :
      Matrix (Fin n) (Fin n) (𝓞 k)) =
      ((g.val⁻¹ : Algebraic.SL n k) : Matrix (Fin n) (Fin n) k) := congrArg Subtype.val hBi
  have hCv : ι.mapMatrix C = A.val := hC
  apply (mem_integralLieLattice G _).mpr
  refine ⟨(B : Matrix (Fin n) (Fin n) (𝓞 k)) * C *
    ((B⁻¹ : Matrix.SpecialLinearGroup (Fin n) (𝓞 k)) : Matrix (Fin n) (Fin n) (𝓞 k)), ?_⟩
  rw [ExponentialNormal.Construction.infinitesimalAdjoint_apply]
  change ι.mapMatrix (_ * _ * _) = _
  rw [map_mul, map_mul, hBv, hCv, hBiv]

theorem infinitesimalAdjoint_inverse_apply
    {k : Type} [Field k] {n : ℕ} (G : Algebraic.MatrixAlgebraicGroup k n)
    (g : G.RationalPoints) (A : Infinitesimal.Action.Construction.infinitesimalStabilizer G) :
    ExponentialNormal.Construction.infinitesimalAdjoint G g⁻¹ (ExponentialNormal.Construction.infinitesimalAdjoint G g A) = A := by
  apply Subtype.ext
  rw [ExponentialNormal.Construction.infinitesimalAdjoint_apply, ExponentialNormal.Construction.infinitesimalAdjoint_apply]
  change ((g.val⁻¹ : Algebraic.SL n k) : Matrix (Fin n) (Fin n) k) *
    ((g.val : Matrix (Fin n) (Fin n) k) * A.val * (g.val⁻¹ : Algebraic.SL n k)) *
      ((g.val⁻¹ : Algebraic.SL n k)⁻¹ : Algebraic.SL n k) = A.val
  rw [inv_inv, ← mul_assoc, ← mul_assoc,
    ← Matrix.SpecialLinearGroup.coe_mul, inv_mul_cancel, Matrix.SpecialLinearGroup.coe_one, one_mul,
    mul_assoc, ← Matrix.SpecialLinearGroup.coe_mul, inv_mul_cancel,
    Matrix.SpecialLinearGroup.coe_one, mul_one]

theorem standard_arithmetic_adjoint_integralLieLattice_iff
    {k : Type} [Field k] [NumberField k] {n : ℕ}
    (G : Algebraic.MatrixAlgebraicGroup k n) (g : G.RationalPoints)
    (hg : g ∈ G.latticeStabilizer (IntegralLattice.FullLattice.standard k n))
    (A : Infinitesimal.Action.Construction.infinitesimalStabilizer G) :
    ExponentialNormal.Construction.infinitesimalAdjoint G g A ∈ integralLieLattice G ↔ A ∈ integralLieLattice G := by
  constructor
  · intro h
    have hi := standard_arithmetic_adjoint_preserves_integralLieLattice G g⁻¹
      ((G.latticeStabilizer (IntegralLattice.FullLattice.standard k n)).inv_mem hg) _ h
    rwa [infinitesimalAdjoint_inverse_apply] at hi
  · exact standard_arithmetic_adjoint_preserves_integralLieLattice G g hg A

end

/-! The integral Lie lattice is closed under brackets, so it is a
finitely generated Lie algebra over the integers. -/

open scoped Classical _root_.NumberField

attribute [local instance] LieRing.ofAssociativeRing

theorem integralLieLattice_lie_mem
    {k : Type} [Field k] {n : ℕ} (G : Algebraic.MatrixAlgebraicGroup k n)
    (A B : Infinitesimal.Action.Construction.infinitesimalStabilizer G)
    (hA : A ∈ integralLieLattice G) (hB : B ∈ integralLieLattice G) :
    ⁅A, B⁆ ∈ integralLieLattice G := by
  obtain ⟨C, hC⟩ := (mem_integralLieLattice G A).mp hA
  obtain ⟨D, hD⟩ := (mem_integralLieLattice G B).mp hB
  apply (mem_integralLieLattice G _).mpr
  refine ⟨C * D - D * C, ?_⟩
  let ι := algebraMap (𝓞 k) k
  have hC' : ι.mapMatrix C = A.val := hC
  have hD' : ι.mapMatrix D = B.val := hD
  change ι.mapMatrix (C * D - D * C) = A.val * B.val - B.val * A.val
  rw [map_sub, map_mul, map_mul, hC', hD']

def integralLieOrder
    {k : Type} [Field k] {n : ℕ} (G : Algebraic.MatrixAlgebraicGroup k n) :
    LieSubalgebra ℤ (Infinitesimal.Action.Construction.infinitesimalStabilizer G) where
  toSubmodule := (integralLieLattice G).restrictScalars ℤ
  lie_mem' := fun {A B} hA hB => integralLieLattice_lie_mem G A B hA hB

theorem integralLieOrder_finite
    {k : Type} [Field k] [NumberField k] {n : ℕ} (G : Algebraic.MatrixAlgebraicGroup k n) :
    Module.Finite ℤ (integralLieOrder G) := by
  let : Module.Finite (𝓞 k) (integralLieLattice G) := Module.Finite.of_fg (integralLieLattice_fg G)
  change Module.Finite ℤ (integralLieLattice G)
  exact Module.Finite.trans (𝓞 k) (integralLieLattice G)

end

end OAI.NumberTheory.ArithmeticGroups.Lattices.Integral.Lie.Construction
