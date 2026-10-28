import OAI.NumberTheory.PadicHodge.IntegralComparison.IteratedAffineCover
import OAI.NumberTheory.PadicHodge.IntegralComparison.ProperAffineCover
import OAI.NumberTheory.PadicHodge.IntegralComparison.MultiplicationCoverRefinement

/-! # Multiplication Infinite Cover -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.MultiplicationInfiniteCover

noncomputable section

/-! A genuine affine pro-étale cover of an abelian variety simultaneously
refines every prime-power multiplication cover. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry Opposite
open MonoidalCategory CartesianMonoidalCategory MonObj

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

universe u
variable (ℓ : ℕ) [Fact ℓ.Prime]
  {k : Type u} [Field k] [IsAlgClosed k]
  (A : Over (Spec (.of k))) [GrpObj A] [IsCommMonObj A]
  [Smooth A.hom] [IsProper A.hom] [GeometricallyIntegral A.hom]
  (hℓ : (ℓ : k) ≠ 0)

def multiplication (_h : (ℓ : k) ≠ 0) : A.left ⟶ A.left := ((𝟙 A : A ⟶ A) ^ ℓ).left

local instance multiplication_finite : IsFinite (multiplication ℓ A hℓ) := AlgebraicGeometry.FormalGeometry.Completion.Multiplication.Construction.multiplication_isFinite A ℓ hℓ
local instance multiplication_etale : Etale (multiplication ℓ A hℓ) := AlgebraicGeometry.FormalGeometry.Completion.Multiplication.Construction.multiplication_etale A ℓ hℓ
local instance multiplication_surjective : Surjective (multiplication ℓ A hℓ) := AlgebraicGeometry.FormalGeometry.Completion.Multiplication.Construction.multiplication_surjective A ℓ hℓ

local notation "μℓ" => OAI.NumberTheory.PadicHodge.IntegralComparison.MultiplicationInfiniteCover.multiplication ℓ A hℓ
local notation "𝒰" => OAI.NumberTheory.PadicHodge.IntegralComparison.ProperAffineCover.cover A.hom

def chart (i : (𝒰).I₀) : Scheme.{u} := IteratedAffineCover.point μℓ ((𝒰).f i)

instance chart_affine (i : (𝒰).I₀) : IsAffine (chart ℓ A hℓ i) :=
  inferInstanceAs (IsAffine (IteratedAffineCover.point μℓ ((𝒰).f i)))

def point : Scheme.{u} := ∐ (chart ℓ A hℓ)

instance point_affine : IsAffine (point ℓ A hℓ) := by unfold point; infer_instance

def projection (n : ℕ) : point ℓ A hℓ ⟶ A.left :=
  Sigma.desc (fun i => IteratedAffineCover.toBase μℓ ((𝒰).f i) n)

omit [Fact (Nat.Prime ℓ)] [IsAlgClosed k] [Smooth A.hom] [GeometricallyIntegral A.hom] in
theorem projection_step (n : ℕ) : projection ℓ A hℓ (n + 1) ≫ μℓ = projection ℓ A hℓ n := by
  unfold projection
  apply Sigma.hom_ext
  intro i
  rw [Sigma.ι_comp_desc_assoc, Sigma.ι_comp_desc]
  exact IteratedAffineCover.toBase_step μℓ ((𝒰).f i) n

omit [Fact (Nat.Prime ℓ)] [IsAlgClosed k] [Smooth A.hom] [GeometricallyIntegral A.hom] in
theorem projection_power (n : ℕ) :
    projection ℓ A hℓ n ≫ ((𝟙 A : A ⟶ A) ^ (ℓ ^ n)).left = projection ℓ A hℓ 0 := by
  induction n with
  | zero => simp only [pow_zero, pow_one, Over.id_left, Category.comp_id]
  | succ n ih =>
    have hs : projection ℓ A hℓ (n + 1) ≫ ((𝟙 A : A ⟶ A) ^ ℓ).left =
        projection ℓ A hℓ n := projection_step ℓ A hℓ n
    rw [← MultiplicationCoverRefinement.multiplication_comp ℓ n A, Over.comp_left,
      ← Category.assoc, hs, ih]

omit [Fact (Nat.Prime ℓ)] [IsAlgClosed k] in
theorem projection_zero_weaklyEtale : WeaklyEtale (projection ℓ A hℓ 0) := by
  apply IsZariskiLocalAtSource.sigmaDesc
  intro i
  let : WeaklyEtale (IteratedAffineCover.projection μℓ ((𝒰).f i) 0) :=
    IteratedAffineCover.projection_zero_weaklyEtale μℓ ((𝒰).f i)
  change WeaklyEtale (IteratedAffineCover.projection μℓ ((𝒰).f i) 0 ≫ (𝒰).f i)
  infer_instance

omit [Fact (Nat.Prime ℓ)] [IsAlgClosed k] in
theorem projection_zero_surjective : Surjective (projection ℓ A hℓ 0) := by
  apply Surjective.sigmaDesc_of_union_range_eq_univ
  apply Set.eq_univ_of_forall
  intro x
  obtain ⟨i, z, hz⟩ := (𝒰).exists_eq x
  let : Surjective (IteratedAffineCover.projection μℓ ((𝒰).f i) 0) :=
    IteratedAffineCover.projection_zero_surjective μℓ ((𝒰).f i)
  obtain ⟨y, hy⟩ := (IteratedAffineCover.projection μℓ ((𝒰).f i) 0).surjective z
  exact Set.mem_iUnion.mpr ⟨i, y, by
    change (𝒰).f i (IteratedAffineCover.projection μℓ ((𝒰).f i) 0 y) = x
    rw [hy]
    exact hz⟩

omit [Fact (Nat.Prime ℓ)] [IsAlgClosed k] [Smooth A.hom] [GeometricallyIntegral A.hom] in
theorem projection_zero_quasiCompact : QuasiCompact (projection ℓ A hℓ 0) := by
  let : QuasiSeparatedSpace A.left := quasiSeparatedSpace_of_quasiSeparated A.hom
  infer_instance

def cover : A.left.ProEt := by
  let : WeaklyEtale (projection ℓ A hℓ 0) := projection_zero_weaklyEtale ℓ A hℓ
  exact Scheme.ProEt.mk (projection ℓ A hℓ 0)

def coverMap (n : ℕ) : cover ℓ A hℓ ⟶ MultiplicationCoverCharacter.cover ℓ n A hℓ :=
  MorphismProperty.Over.homMk (projection ℓ A hℓ n) (projection_power ℓ A hℓ n)

omit [Fact (Nat.Prime ℓ)] [IsAlgClosed k] in
theorem coverMap_step (n : ℕ) : coverMap ℓ A hℓ (n + 1) ≫
    MultiplicationCoverRefinement.coverMap ℓ n A hℓ = coverMap ℓ A hℓ n := by
  apply MorphismProperty.Over.Hom.ext
  exact projection_step ℓ A hℓ n

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.MultiplicationInfiniteCover
