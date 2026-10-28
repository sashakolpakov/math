import OAI.NumberTheory.ArithmeticGroups.Lattices.Integral.Lie
import Mathlib.RingTheory.Algebraic.Integral
import Mathlib.LinearAlgebra.FreeModule.PID
import Mathlib.RingTheory.Localization.Integral

/-! # Mixed Lattice -/

namespace OAI.NumberTheory.ArithmeticGroups.Lattices.Lie.MixedLattice.Construction

noncomputable section

section

/-! The integral Lie order also spans the rational restriction of
scalars, and admits an integral basis. -/

open scoped Classical _root_.NumberField

theorem integralLieLattice_integer_denominator
    {k : Type} [Field k] [NumberField k] {n : ℕ}
    (G : Lattices.Algebraic.MatrixAlgebraicGroup k n) (A : Infinitesimal.Action.Construction.infinitesimalStabilizer G) :
    ∃ d : ℤ, d ≠ 0 ∧ d • A ∈ Lattices.Integral.Lie.Construction.integralLieLattice G := by
  let : Algebra.IsAlgebraic ℤ k := IsFractionRing.comap_isAlgebraic_iff (K := ℚ) |>.mpr inferInstance
  obtain ⟨d, hd, hA⟩ := Algebra.IsAlgebraic.exists_integral_multiples ℤ
    (Finset.univ.image (fun ij : Fin n × Fin n => A.val ij.1 ij.2))
  have hi (i j : Fin n) : IsIntegral ℤ (d • A.val i j) :=
    hA _ (Finset.mem_image.mpr ⟨(i, j), Finset.mem_univ _, rfl⟩)
  refine ⟨d, hd, (Lattices.Integral.Lie.Construction.mem_integralLieLattice G _).mpr ⟨fun i j => ⟨d • A.val i j, hi i j⟩, ?_⟩⟩
  rfl

theorem integralLieLattice_full_rational
    {k : Type} [Field k] [NumberField k] {n : ℕ} (G : Lattices.Algebraic.MatrixAlgebraicGroup k n) :
    Submodule.span ℚ (Lattices.Integral.Lie.Construction.integralLieLattice G : Set (Infinitesimal.Action.Construction.infinitesimalStabilizer G)) = ⊤ := by
  apply top_unique
  intro A _
  obtain ⟨d, hd, hA⟩ := integralLieLattice_integer_denominator G A
  have hdq : (d : ℚ) ≠ 0 := Int.cast_ne_zero.mpr hd
  have h := (Submodule.span ℚ (Lattices.Integral.Lie.Construction.integralLieLattice G : Set (Infinitesimal.Action.Construction.infinitesimalStabilizer G))).smul_mem
    (d : ℚ)⁻¹ (Submodule.subset_span hA)
  rwa [← Int.cast_smul_eq_zsmul ℚ, inv_smul_smul₀ hdq] at h

theorem integralLieOrder_free
    {k : Type} [Field k] [NumberField k] {n : ℕ} (G : Lattices.Algebraic.MatrixAlgebraicGroup k n) :
    Module.Free ℤ (Lattices.Integral.Lie.Construction.integralLieOrder G) := by
  let : Module.Finite ℤ (Lattices.Integral.Lie.Construction.integralLieOrder G) := Lattices.Integral.Lie.Construction.integralLieOrder_finite G
  let : Module.IsTorsionFree ℤ (Matrix (Fin n) (Fin n) k) :=
    inferInstanceAs (Module.IsTorsionFree ℤ (Fin n → Fin n → k))
  let f : Lattices.Integral.Lie.Construction.integralLieOrder G → Matrix (Fin n) (Fin n) k := fun A => A.val.val
  let : Module.IsTorsionFree ℤ (Lattices.Integral.Lie.Construction.integralLieOrder G) :=
    Function.Injective.moduleIsTorsionFree f
      (Subtype.val_injective.comp Subtype.val_injective) (fun _ _ => rfl)
  infer_instance

end

section

/-! The integral Lie order embeds as a discrete full lattice in its
real Minkowski span. -/

open scoped Classical _root_.NumberField _root_.Matrix.Norms.Elementwise
open _root_.NumberField _root_.NumberField.mixedEmbedding

attribute [local instance] LieRing.ofAssociativeRing

def lieMixedEmbedding
    {k : Type} [Field k] {n : ℕ} (G : Lattices.Algebraic.MatrixAlgebraicGroup k n) :
    Infinitesimal.Action.Construction.infinitesimalStabilizer G →ₗ[ℤ] Matrix (Fin n) (Fin n) (mixedSpace k) :=
  ((mixedEmbedding k).toIntAlgHom.toLinearMap.mapMatrix).comp
    ((Infinitesimal.Action.Construction.infinitesimalStabilizer G).toSubmodule.subtype.restrictScalars ℤ)

def lieMixedLattice
    {k : Type} [Field k] [NumberField k] {n : ℕ} (G : Lattices.Algebraic.MatrixAlgebraicGroup k n) :
    Submodule ℤ (Matrix (Fin n) (Fin n) (mixedSpace k)) :=
  ((Lattices.Integral.Lie.Construction.integralLieLattice G).restrictScalars ℤ).map (lieMixedEmbedding G)

theorem lieMixedLattice_discrete
    {k : Type} [Field k] [NumberField k] {n : ℕ} (G : Lattices.Algebraic.MatrixAlgebraicGroup k n) :
    DiscreteTopology (lieMixedLattice G) := by
  let f : lieMixedLattice G → ((Fin n × Fin n) → mixedEmbedding.integerLattice k) := fun x ij =>
    ⟨x.val ij.1 ij.2, by
      obtain ⟨A, hA, hAx⟩ := x.property
      rw [← hAx]
      obtain ⟨C, hC⟩ := (Lattices.Integral.Lie.Construction.mem_integralLieLattice G A).mp hA
      refine ⟨C ij.1 ij.2, ?_⟩
      change mixedEmbedding k (C ij.1 ij.2 : k) = mixedEmbedding k (A.val ij.1 ij.2)
      exact congrArg (mixedEmbedding k) (congrFun (congrFun hC ij.1) ij.2)⟩
  apply DiscreteTopology.of_continuous_injective (f := f)
  · apply continuous_pi
    intro ij
    apply Continuous.subtype_mk
    exact (continuous_apply ij.2).comp ((continuous_apply ij.1).comp continuous_subtype_val)
  · intro x y h
    apply Subtype.ext
    ext i j : 1
    exact congrArg (fun z => (z (i, j)).val) h

def lieMixedSpan
    {k : Type} [Field k] [NumberField k] {n : ℕ} (G : Lattices.Algebraic.MatrixAlgebraicGroup k n) :
    Submodule ℝ (Matrix (Fin n) (Fin n) (mixedSpace k)) :=
  Submodule.span ℝ (lieMixedLattice G : Set (Matrix (Fin n) (Fin n) (mixedSpace k)))

def lieMixedLatticeInSpan
    {k : Type} [Field k] [NumberField k] {n : ℕ} (G : Lattices.Algebraic.MatrixAlgebraicGroup k n) :
    Submodule ℤ (lieMixedSpan G) :=
  (lieMixedLattice G).comap ((lieMixedSpan G).subtype.restrictScalars ℤ)

instance lieMixedLatticeInSpan_discrete
    {k : Type} [Field k] [NumberField k] {n : ℕ} (G : Lattices.Algebraic.MatrixAlgebraicGroup k n) :
    DiscreteTopology (lieMixedLatticeInSpan G) := by
  let : DiscreteTopology (lieMixedLattice G) := lieMixedLattice_discrete G
  let f : lieMixedLatticeInSpan G → lieMixedLattice G := fun x => ⟨x.val.val, x.property⟩
  apply DiscreteTopology.of_continuous_injective (f := f)
  · exact (continuous_subtype_val.comp continuous_subtype_val).subtype_mk _
  · intro x y h
    apply Subtype.ext
    apply Subtype.ext
    exact congrArg (fun z : lieMixedLattice G => z.val) h

theorem lieMixedLatticeInSpan_full
    {k : Type} [Field k] [NumberField k] {n : ℕ} (G : Lattices.Algebraic.MatrixAlgebraicGroup k n) :
    Submodule.span ℝ (lieMixedLatticeInSpan G : Set (lieMixedSpan G)) = ⊤ := by
  have himage : (lieMixedSpan G).subtype '' (lieMixedLatticeInSpan G : Set (lieMixedSpan G)) =
      (lieMixedLattice G : Set (Matrix (Fin n) (Fin n) (mixedSpace k))) := by
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact hy
    · intro hx
      exact ⟨⟨x, Submodule.subset_span hx⟩, hx, rfl⟩
  apply (Submodule.map_injective_of_injective (lieMixedSpan G).injective_subtype).eq_iff.mp
  rw [Submodule.map_span, himage, Submodule.map_top, Submodule.range_subtype]
  rfl

theorem lieMixedLatticeInSpan_isZLattice
    {k : Type} [Field k] [NumberField k] {n : ℕ} (G : Lattices.Algebraic.MatrixAlgebraicGroup k n) :
    @IsZLattice ℝ _ (lieMixedSpan G) _ _ (lieMixedLatticeInSpan G)
      (lieMixedLatticeInSpan_discrete G) := by
  exact @IsZLattice.mk ℝ _ (lieMixedSpan G) _ _ (lieMixedLatticeInSpan G)
    (lieMixedLatticeInSpan_discrete G) (lieMixedLatticeInSpan_full G)

end

section

/-! The real span of the integral Lie lattice is stable under the full
Minkowski coefficient algebra. -/

open scoped Classical _root_.NumberField _root_.Matrix.Norms.Elementwise
open _root_.NumberField _root_.NumberField.mixedEmbedding

attribute [local instance] LieRing.ofAssociativeRing

theorem lieMixedEmbedding_integer_scalar
    {k : Type} [Field k] {n : ℕ} (G : Lattices.Algebraic.MatrixAlgebraicGroup k n)
    (a : 𝓞 k) (A : Infinitesimal.Action.Construction.infinitesimalStabilizer G) :
    lieMixedEmbedding G (a • A) = mixedEmbedding k (a : k) • lieMixedEmbedding G A := by
  ext i j : 1
  change mixedEmbedding k ((a : k) * A.val i j) = mixedEmbedding k (a : k) * mixedEmbedding k (A.val i j)
  exact map_mul _ _ _

theorem lieMixedLattice_integer_scalar_mem
    {k : Type} [Field k] [NumberField k] {n : ℕ} (G : Lattices.Algebraic.MatrixAlgebraicGroup k n)
    (a : 𝓞 k) {x : Matrix (Fin n) (Fin n) (mixedSpace k)} (hx : x ∈ lieMixedLattice G) :
    mixedEmbedding k (a : k) • x ∈ lieMixedLattice G := by
  obtain ⟨A, hA, rfl⟩ := hx
  exact ⟨a • A, (Lattices.Integral.Lie.Construction.integralLieLattice G).smul_mem a hA, lieMixedEmbedding_integer_scalar G a A⟩

theorem lieMixedSpan_integer_scalar_mem
    {k : Type} [Field k] [NumberField k] {n : ℕ} (G : Lattices.Algebraic.MatrixAlgebraicGroup k n)
    (a : 𝓞 k) {x : Matrix (Fin n) (Fin n) (mixedSpace k)} (hx : x ∈ lieMixedSpan G) :
    mixedEmbedding k (a : k) • x ∈ lieMixedSpan G := by
  induction hx using Submodule.span_induction with
  | mem y hy => exact Submodule.subset_span (lieMixedLattice_integer_scalar_mem G a hy)
  | zero => simpa only [smul_zero] using (lieMixedSpan G).zero_mem
  | add y z _ _ hy hz => simpa only [smul_add] using (lieMixedSpan G).add_mem hy hz
  | smul r y _ hy => simpa only [smul_comm (mixedEmbedding k (a : k)) r y] using (lieMixedSpan G).smul_mem r hy

theorem lieMixedSpan_scalar_mem
    {k : Type} [Field k] [NumberField k] {n : ℕ} (G : Lattices.Algebraic.MatrixAlgebraicGroup k n)
    (a : mixedSpace k) {x : Matrix (Fin n) (Fin n) (mixedSpace k)} (hx : x ∈ lieMixedSpan G) :
    a • x ∈ lieMixedSpan G := by
  have ha : a ∈ Submodule.span ℝ (mixedEmbedding.integerLattice k : Set (mixedSpace k)) := by
    rw [IsZLattice.span_top]
    trivial
  induction ha using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨b, rfl⟩ := hy
    exact lieMixedSpan_integer_scalar_mem G b hx
  | zero => simpa only [zero_smul] using (lieMixedSpan G).zero_mem
  | add y z _ _ hy hz => simpa only [add_smul] using (lieMixedSpan G).add_mem hy hz
  | smul r y _ hy => simpa only [smul_assoc] using (lieMixedSpan G).smul_mem r hy

def lieMixedModule
    {k : Type} [Field k] [NumberField k] {n : ℕ} (G : Lattices.Algebraic.MatrixAlgebraicGroup k n) :
    Submodule (mixedSpace k) (Matrix (Fin n) (Fin n) (mixedSpace k)) where
  carrier := lieMixedSpan G
  zero_mem' := (lieMixedSpan G).zero_mem
  add_mem' := (lieMixedSpan G).add_mem
  smul_mem' := fun a _ hx => lieMixedSpan_scalar_mem G a hx

end

/-! The Minkowski Lie space is the span over the Minkowski coefficient
algebra of the original rational Lie algebra. -/

open scoped Classical _root_.NumberField _root_.Matrix.Norms.Elementwise
open _root_.NumberField _root_.NumberField.mixedEmbedding

attribute [local instance] LieRing.ofAssociativeRing

def lieMixedRationalMap
    {k : Type} [Field k] [NumberField k] {n : ℕ} (G : Lattices.Algebraic.MatrixAlgebraicGroup k n) :
    Infinitesimal.Action.Construction.infinitesimalStabilizer G →ₗ[ℚ] Matrix (Fin n) (Fin n) (mixedSpace k) where
  toFun := lieMixedEmbedding G
  map_add' := (lieMixedEmbedding G).map_add
  map_smul' q A := by
    ext i j : 1
    change mixedEmbedding k (q • A.val i j) = q • mixedEmbedding k (A.val i j)
    exact (mixedEmbedding k).toRatAlgHom.toLinearMap.map_smul q _

theorem lieMixedEmbedding_mem_span
    {k : Type} [Field k] [NumberField k] {n : ℕ} (G : Lattices.Algebraic.MatrixAlgebraicGroup k n)
    (A : Infinitesimal.Action.Construction.infinitesimalStabilizer G) : lieMixedEmbedding G A ∈ lieMixedSpan G := by
  have hA : A ∈ Submodule.span ℚ (Lattices.Integral.Lie.Construction.integralLieLattice G : Set (Infinitesimal.Action.Construction.infinitesimalStabilizer G)) := by
    rw [integralLieLattice_full_rational]
    trivial
  change lieMixedRationalMap G A ∈ lieMixedSpan G
  induction hA using Submodule.span_induction with
  | mem x hx => exact Submodule.subset_span ⟨x, hx, rfl⟩
  | zero => simpa only [map_zero] using (lieMixedSpan G).zero_mem
  | add x y _ _ hx hy => simpa only [map_add] using (lieMixedSpan G).add_mem hx hy
  | smul q x _ hx =>
    rw [map_smul]
    simpa only [Rat.cast_smul_eq_qsmul] using (lieMixedSpan G).smul_mem (q : ℝ) hx

theorem lieMixedModule_eq_span
    {k : Type} [Field k] [NumberField k] {n : ℕ} (G : Lattices.Algebraic.MatrixAlgebraicGroup k n) :
    lieMixedModule G = Submodule.span (mixedSpace k) (Set.range (lieMixedEmbedding G)) := by
  apply le_antisymm
  · have h : lieMixedSpan G ≤
        (Submodule.span (mixedSpace k) (Set.range (lieMixedEmbedding G))).restrictScalars ℝ := by
      apply Submodule.span_le.mpr
      rintro _ ⟨A, _, rfl⟩
      exact Submodule.subset_span (Set.mem_range_self A)
    exact h
  · apply Submodule.span_le.mpr
    rintro _ ⟨A, rfl⟩
    exact lieMixedEmbedding_mem_span G A

theorem lieMixedModule_eq_matrix_span
    {k : Type} [Field k] [NumberField k] {n : ℕ} (G : Lattices.Algebraic.MatrixAlgebraicGroup k n) :
    lieMixedModule G = Submodule.span (mixedSpace k)
      ((fun A : Matrix (Fin n) (Fin n) k => A.map (mixedEmbedding k)) ''
        (Infinitesimal.Action.Construction.infinitesimalStabilizer G : Set (Matrix (Fin n) (Fin n) k))) := by
  rw [lieMixedModule_eq_span]
  congr 1
  ext x
  constructor
  · rintro ⟨A, rfl⟩
    exact ⟨A.val, A.property, rfl⟩
  · rintro ⟨A, hA, rfl⟩
    exact ⟨⟨A, hA⟩, rfl⟩

end

end OAI.NumberTheory.ArithmeticGroups.Lattices.Lie.MixedLattice.Construction
