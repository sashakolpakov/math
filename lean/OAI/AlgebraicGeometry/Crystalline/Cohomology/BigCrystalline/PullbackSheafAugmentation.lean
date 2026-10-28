import OAI.AlgebraicGeometry.Crystalline.Cohomology.BigCrystalline.PullbackSheafTransport
import OAI.AlgebraicGeometry.Crystalline.Cohomology.Mapped.AugmentationZero

/-! # Pullback Sheaf Augmentation -/

namespace OAI.AlgebraicGeometry.Crystalline.Cohomology.BigCrystalline.PullbackSheafAugmentation.BigCrystallinePullbackSheafAugmentation

noncomputable section

/-! # The original geometric sheaf pullback preserves the frame augmentation -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

variable (p : ℕ) (W A B σ : Type u) [CommRing W] [CommRing A] [CommRing B]
  (J : Ideal W) (δ : DividedPowers J) (base : Spec (CommRingCat.of B) ⟶ Spec (CommRingCat.of W))
  (φ : B →+* A) (a : σ → B) [Fintype σ]

local notation "g" => Spec.map (CommRingCat.ofHom φ)
local notation "bA" => g ≫ base
local notation "F" => OAI.AlgebraicGeometry.Crystalline.Cohomology.BigCrystalline.PullbackSheafTransport.BigCrystallinePullbackSheafTransport.restriction p W A B J δ base φ
local notation "P" => OAI.AlgebraicGeometry.Crystalline.Cohomology.BigCrystalline.PullbackResolution.BigCrystallinePullbackResolution.restriction p W A B J δ base φ
local notation "S" => OAI.AlgebraicGeometry.Crystalline.Cohomology.BigCrystalline.FrameSheafResolution.BigCrystallineFrameSheafResolution.toSheaf p W A J δ bA
local notation "T" => OAI.AlgebraicGeometry.Crystalline.Cohomology.BigCrystalline.FrameSheafResolution.BigCrystallineFrameSheafResolution.toSheaf p W B J δ base
local notation "α" => OAI.AlgebraicGeometry.Crystalline.Cohomology.BigCrystalline.FrameResolution.BigCrystallineFrameResolution.augmentation (p := p) (J := J) (δ := δ) (base := base) a
local notation "β" => OAI.AlgebraicGeometry.Crystalline.Cohomology.BigCrystalline.FrameResolution.BigCrystallineFrameResolution.augmentation (p := p) (J := J) (δ := δ) (base := bA) (φ ∘ a)
local notation "α'" => OAI.AlgebraicGeometry.Crystalline.Cohomology.BigCrystalline.FrameSheafResolution.BigCrystallineFrameSheafResolution.augmentation p W B J δ base a
local notation "β'" => OAI.AlgebraicGeometry.Crystalline.Cohomology.BigCrystalline.FrameSheafResolution.BigCrystallineFrameSheafResolution.augmentation p W A J δ bA (φ ∘ a)
local notation "e" => OAI.AlgebraicGeometry.Crystalline.Cohomology.BigCrystalline.PullbackResolution.BigCrystallinePullbackResolution.iso p W A B σ J δ base φ a
local notation "s" => OAI.AlgebraicGeometry.Crystalline.Cohomology.BigCrystalline.PullbackAugmentation.BigCrystallinePullbackAugmentation.sourceIso p W A B J δ base φ

theorem source_zero : (α').f 0 = (T).map ((α).f 0) := by
  have h := Mapped.AugmentationZero.MappedAugmentationZero.normalized T α (FrameSheafResolution.BigCrystallineFrameSheafResolution.coefficientIso p W B J δ base)
  exact h.trans (Category.id_comp _)

theorem target_zero : (β').f 0 = (S).map ((β).f 0) := by
  have h := Mapped.AugmentationZero.MappedAugmentationZero.normalized S β (FrameSheafResolution.BigCrystallineFrameSheafResolution.coefficientIso p W A J δ bA)
  exact h.trans (Category.id_comp _)

theorem presheaf_zero : (P).map ((α).f 0) ≫ (e).hom.f 0 = (s).hom ≫ (β).f 0 := by
  have h := congrArg (fun f => f.f 0) (PullbackAugmentation.BigCrystallinePullbackAugmentation.square p W A B σ J δ base φ a)
  rw [HomologicalComplex.comp_f, HomologicalComplex.comp_f, CochainComplex.single₀_map_f_zero] at h
  have hm : (PullbackAugmentation.BigCrystallinePullbackAugmentation.augmentation p W A B σ J δ base φ a).f 0 =
      (P).map ((α).f 0) := Mapped.AugmentationZero.MappedAugmentationZero.mapped P α
  rw [hm] at h
  exact h

theorem square : (F).map ((α').f 0) ≫
      (PullbackSheafTransport.BigCrystallinePullbackSheafTransport.complexIso p W A B J δ base φ a).hom.f 0 =
    (PullbackSheafTransport.BigCrystallinePullbackSheafTransport.structureIso p W A B J δ base φ).hom ≫ (β').f 0 := by
  rw [source_zero, target_zero, PullbackSheafTransport.BigCrystallinePullbackSheafTransport.component]
  let G₀ := NumberTheory.PadicHodge.IntegralComparison.BigCrystallineCohomology.modulePresheaf (p := p) (J := J) (δ := δ) base
  let H₀ := NumberTheory.PadicHodge.IntegralComparison.BigCrystallineCohomology.modulePresheaf (p := p) (J := J) (δ := δ) bA
  let K₀ := (FrameResolution.BigCrystallineFrameResolution.complex (p := p) (J := J) (δ := δ) (base := base) a).X 0
  let L₀ := (FrameResolution.BigCrystallineFrameResolution.complex (p := p) (J := J) (δ := δ) (base := bA) (φ ∘ a)).X 0
  let b : G₀ ⟶ K₀ := (α).f 0
  let v : (P).obj K₀ ⟶ L₀ := (e).hom.f 0
  let w : (P).obj G₀ ⟶ H₀ := (s).hom
  let z : H₀ ⟶ L₀ := (β).f 0
  have hc : (F).map ((T).map b) ≫ (PullbackSheafTransport.BigCrystallinePullbackSheafTransport.comparisonIso p W A B J δ base φ).hom.app K₀ =
      (PullbackSheafTransport.BigCrystallinePullbackSheafTransport.comparisonIso p W A B J δ base φ).hom.app G₀ ≫ (S).map ((P).map b) :=
    (PullbackSheafTransport.BigCrystallinePullbackSheafTransport.comparisonIso p W A B J δ base φ).hom.naturality b
  have hp₀ : (P).map b ≫ v = w ≫ z := presheaf_zero p W A B σ J δ base φ a
  have hp : (S).map ((P).map b) ≫ (S).map v = (S).map w ≫ (S).map z :=
    ((S).map_comp ((P).map b) v).symm.trans ((congrArg (S).map hp₀).trans ((S).map_comp w z))
  change (F).map ((T).map b) ≫
      ((PullbackSheafTransport.BigCrystallinePullbackSheafTransport.comparisonIso p W A B J δ base φ).hom.app K₀ ≫ (S).map v) =
    ((PullbackSheafTransport.BigCrystallinePullbackSheafTransport.comparisonIso p W A B J δ base φ).hom.app G₀ ≫ (S).map w) ≫ (S).map z
  rw [← Category.assoc, hc, Category.assoc, hp, ← Category.assoc]

theorem original_square : (F).map ((α').f 0) ≫
      (PullbackSheafTransport.BigCrystallinePullbackSheafTransport.complexIso p W A B J δ base φ a).hom.f 0 =
    (NumberTheory.PadicHodge.IntegralComparison.BigCrystallineCohomology.structureTransport
      (p := p) (J := J) (δ := δ) (fY := base) g rfl).hom ≫ (β').f 0 := by
  rw [← PullbackSheafTransport.BigCrystallinePullbackSheafTransport.structureIso_original]
  exact square p W A B σ J δ base φ a

end

end OAI.AlgebraicGeometry.Crystalline.Cohomology.BigCrystalline.PullbackSheafAugmentation.BigCrystallinePullbackSheafAugmentation
