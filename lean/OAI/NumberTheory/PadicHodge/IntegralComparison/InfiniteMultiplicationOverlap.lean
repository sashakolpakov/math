import OAI.NumberTheory.PadicHodge.IntegralComparison.MultiplicationInfiniteCover

/-! # Infinite Multiplication Overlap -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.InfiniteMultiplicationOverlap

noncomputable section

/-! The actual overlap of the simultaneous multiplication cover and its
compatible maps to every finite multiplication overlap. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry Opposite
open MonoidalCategory CartesianMonoidalCategory MonObj

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

open OAI.NumberTheory.PadicHodge.IntegralComparison.MultiplicationInfiniteCover

universe u
variable (ℓ : ℕ) [Fact ℓ.Prime]
  {k : Type u} [Field k] [IsAlgClosed k]
  (A : Over (Spec (.of k))) [GrpObj A] [IsCommMonObj A]
  [Smooth A.hom] [IsProper A.hom] [GeometricallyIntegral A.hom]
  (hℓ : (ℓ : k) ≠ 0)

local notation "U" => OAI.NumberTheory.PadicHodge.IntegralComparison.MultiplicationInfiniteCover.cover ℓ A hℓ
local notation "g" => OAI.NumberTheory.PadicHodge.IntegralComparison.MultiplicationInfiniteCover.projection ℓ A hℓ 0

def overlap : A.left.ProEt := by
  let : WeaklyEtale g := MultiplicationInfiniteCover.projection_zero_weaklyEtale ℓ A hℓ
  exact Scheme.ProEt.mk (pullback.fst g g ≫ g)

local notation "D" => OAI.NumberTheory.PadicHodge.IntegralComparison.InfiniteMultiplicationOverlap.overlap ℓ A hℓ

def first : D ⟶ U := MorphismProperty.Over.homMk (pullback.fst g g) rfl

def second : D ⟶ U := MorphismProperty.Over.homMk (pullback.snd g g) pullback.condition.symm

def overlapMap (n : ℕ) : D ⟶ MultiplicationCoverCharacter.overlap ℓ n A hℓ :=
  MorphismProperty.Over.homMk
    (pullback.lift (pullback.fst g g ≫ MultiplicationInfiniteCover.projection ℓ A hℓ n)
      (pullback.snd g g ≫ MultiplicationInfiniteCover.projection ℓ A hℓ n) (by
        rw [Category.assoc, Category.assoc, MultiplicationInfiniteCover.projection_power]
        exact pullback.condition)) (by
          change _ ≫ (pullback.fst _ _ ≫ _) = _
          rw [← Category.assoc, pullback.lift_fst, Category.assoc, MultiplicationInfiniteCover.projection_power]
          rfl)

omit [Fact (Nat.Prime ℓ)] [IsAlgClosed k] in
theorem overlapMap_first (n : ℕ) : overlapMap ℓ A hℓ n ≫
    MultiplicationCoverCharacter.first ℓ n A hℓ = first ℓ A hℓ ≫ MultiplicationInfiniteCover.coverMap ℓ A hℓ n := by
  apply MorphismProperty.Over.Hom.ext
  exact pullback.lift_fst _ _ _

omit [Fact (Nat.Prime ℓ)] [IsAlgClosed k] in
theorem overlapMap_second (n : ℕ) : overlapMap ℓ A hℓ n ≫
    MultiplicationCoverCharacter.second ℓ n A hℓ = second ℓ A hℓ ≫ MultiplicationInfiniteCover.coverMap ℓ A hℓ n := by
  apply MorphismProperty.Over.Hom.ext
  exact pullback.lift_snd _ _ _

omit [Fact (Nat.Prime ℓ)] [IsAlgClosed k] in
theorem overlapMap_step (n : ℕ) : overlapMap ℓ A hℓ (n + 1) ≫
    MultiplicationCoverRefinement.overlapMap ℓ n A hℓ = overlapMap ℓ A hℓ n := by
  apply MorphismProperty.Over.Hom.ext
  apply pullback.hom_ext
  · change _ ≫ (MultiplicationCoverCharacter.first ℓ n A hℓ).left =
      _ ≫ (MultiplicationCoverCharacter.first ℓ n A hℓ).left
    have he := congrArg (fun f : D ⟶ MultiplicationCoverCharacter.cover ℓ n A hℓ => f.left)
      (show (overlapMap ℓ A hℓ (n + 1) ≫ MultiplicationCoverRefinement.overlapMap ℓ n A hℓ) ≫
          MultiplicationCoverCharacter.first ℓ n A hℓ =
        overlapMap ℓ A hℓ n ≫ MultiplicationCoverCharacter.first ℓ n A hℓ from by
          rw [Category.assoc, MultiplicationCoverRefinement.overlapMap_first,
            ← Category.assoc, overlapMap_first, Category.assoc, MultiplicationInfiniteCover.coverMap_step, overlapMap_first])
    exact he
  · change _ ≫ (MultiplicationCoverCharacter.second ℓ n A hℓ).left =
      _ ≫ (MultiplicationCoverCharacter.second ℓ n A hℓ).left
    have he := congrArg (fun f : D ⟶ MultiplicationCoverCharacter.cover ℓ n A hℓ => f.left)
      (show (overlapMap ℓ A hℓ (n + 1) ≫ MultiplicationCoverRefinement.overlapMap ℓ n A hℓ) ≫
          MultiplicationCoverCharacter.second ℓ n A hℓ =
        overlapMap ℓ A hℓ n ≫ MultiplicationCoverCharacter.second ℓ n A hℓ from by
          rw [Category.assoc, MultiplicationCoverRefinement.overlapMap_second,
            ← Category.assoc, overlapMap_second, Category.assoc, MultiplicationInfiniteCover.coverMap_step, overlapMap_second])
    exact he

def terminalIso : (⊤_ A.left.ProEt) ≅ Scheme.ProEt.mk (𝟙 A.left) :=
  terminalIsTerminal.uniqueUpToIso (AlgebraicGeometry.FormalGeometry.Completion.FiniteTorsor.GlobalSections.Construction.proEtaleIdentityIsTerminal A.left)

omit [IsAlgClosed k] [GrpObj A] [IsCommMonObj A] [Smooth A.hom] [IsProper A.hom] [GeometricallyIntegral A.hom] in
theorem terminal_iso_hom : (terminalIso A).hom.left = (⊤_ A.left.ProEt).hom :=
  (Category.comp_id _).symm.trans (MorphismProperty.Over.w (terminalIso A).hom)

omit [Fact (Nat.Prime ℓ)] in
omit [IsAlgClosed k] in
theorem terminal_from_eq : (terminal.from U).left =
    g ≫ (terminalIso A).inv.left := by
  apply (cancel_mono (terminalIso A).hom.left).mp
  rw [Category.assoc]
  have hi : (terminalIso A).inv.left ≫ (terminalIso A).hom.left = 𝟙 A.left :=
    congrArg (fun f : Scheme.ProEt.mk (𝟙 A.left) ⟶ Scheme.ProEt.mk (𝟙 A.left) => f.left)
      (terminalIso A).inv_hom_id
  rw [hi, Category.comp_id, terminal_iso_hom]
  exact MorphismProperty.Over.w (terminal.from U)

omit [Fact (Nat.Prime ℓ)] in
omit [IsAlgClosed k] in
theorem terminal_from_surjective : Surjective (terminal.from U).left := by
  rw [terminal_from_eq]
  let : Surjective g := MultiplicationInfiniteCover.projection_zero_surjective ℓ A hℓ
  infer_instance

omit [Fact (Nat.Prime ℓ)] in
omit [IsAlgClosed k] in
theorem terminal_from_quasiCompact : QuasiCompact (terminal.from U).left := by
  rw [terminal_from_eq]
  let : QuasiCompact g := MultiplicationInfiniteCover.projection_zero_quasiCompact ℓ A hℓ
  infer_instance

omit [Fact (Nat.Prime ℓ)] in
omit [IsAlgClosed k] in
theorem isPullback : IsPullback (first ℓ A hℓ).left (second ℓ A hℓ).left
    (terminal.from U).left (terminal.from U).left := by
  let e := ((Scheme.ProEt.forget A.left) ⋙ Over.forget A.left).mapIso (terminalIso A)
  refine (IsPullback.of_hasPullback g g).of_iso' (Iso.refl _) (Iso.refl _) (Iso.refl _) e
    (by simp only [Iso.refl_hom, Category.comp_id, Category.id_comp]; rfl)
    (by simp only [Iso.refl_hom, Category.comp_id, Category.id_comp]; rfl) ?_ ?_
  · change 𝟙 _ ≫ g = (terminal.from U).left ≫ (terminalIso A).hom.left
    rw [Category.id_comp, terminal_iso_hom]
    exact (MorphismProperty.Over.w (terminal.from U)).symm
  · change 𝟙 _ ≫ g = (terminal.from U).left ≫ (terminalIso A).hom.left
    rw [Category.id_comp, terminal_iso_hom]
    exact (MorphismProperty.Over.w (terminal.from U)).symm

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.InfiniteMultiplicationOverlap
