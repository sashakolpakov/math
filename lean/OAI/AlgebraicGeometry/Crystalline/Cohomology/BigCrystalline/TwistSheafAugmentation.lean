import OAI.AlgebraicGeometry.Crystalline.Cohomology.BigCrystalline.TwistSheafTransport
import OAI.AlgebraicGeometry.Crystalline.Cohomology.BigCrystalline.TwistAugmentation
import OAI.AlgebraicGeometry.Crystalline.Cohomology.Mapped.AugmentationZero

/-! # Twist Sheaf Augmentation -/

namespace OAI.AlgebraicGeometry.Crystalline.Cohomology.BigCrystalline.TwistSheafAugmentation.BigCrystallineTwistSheafAugmentation

noncomputable section

/-! # The original coefficient-twisted sheaf restriction preserves the frame augmentation -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

variable (p : ℕ) (W A σ : Type u) [CommRing W] [CommRing A]
  (J : Ideal W) (δ : DividedPowers J)
  (base base' : Spec (CommRingCat.of A) ⟶ Spec (CommRingCat.of W))
  (e : W ≃+* W) (he : DividedPowers.IsDPMorphism δ δ e.toRingHom)
  (he' : DividedPowers.IsDPMorphism δ δ e.symm.toRingHom)
  (h : base' = base ≫ Spec.map (CommRingCat.ofHom e.toRingHom))
  (a : σ → A) [Fintype σ] [LinearOrder σ]

local notation "F" => OAI.AlgebraicGeometry.Crystalline.Cohomology.BigCrystalline.TwistSheafTransport.BigCrystallineTwistSheafTransport.restriction p W A J δ base base' e he he' h
local notation "P" => OAI.AlgebraicGeometry.Crystalline.Cohomology.BigCrystalline.TwistResolution.BigCrystallineTwistResolution.restriction p W A J δ base base' e he h
local notation "S" => OAI.AlgebraicGeometry.Crystalline.Cohomology.BigCrystalline.FrameSheafResolution.BigCrystallineFrameSheafResolution.toSheaf p W A J δ base
local notation "T" => OAI.AlgebraicGeometry.Crystalline.Cohomology.BigCrystalline.FrameSheafResolution.BigCrystallineFrameSheafResolution.toSheaf p W A J δ base'
local notation "α" => OAI.AlgebraicGeometry.Crystalline.Cohomology.BigCrystalline.FrameResolution.BigCrystallineFrameResolution.augmentation (p := p) (J := J) (δ := δ) (base := base') a
local notation "β" => OAI.AlgebraicGeometry.Crystalline.Cohomology.BigCrystalline.FrameResolution.BigCrystallineFrameResolution.augmentation (p := p) (J := J) (δ := δ) (base := base) a
local notation "α'" => OAI.AlgebraicGeometry.Crystalline.Cohomology.BigCrystalline.FrameSheafResolution.BigCrystallineFrameSheafResolution.augmentation p W A J δ base' a
local notation "β'" => OAI.AlgebraicGeometry.Crystalline.Cohomology.BigCrystalline.FrameSheafResolution.BigCrystallineFrameSheafResolution.augmentation p W A J δ base a
local notation "i" => OAI.AlgebraicGeometry.Crystalline.Cohomology.BigCrystalline.TwistResolution.BigCrystallineTwistResolution.iso p W A J δ base base' e he h a
local notation "s" => OAI.AlgebraicGeometry.Crystalline.Cohomology.BigCrystalline.TwistAugmentation.BigCrystallineTwistAugmentation.sourceIso p W A J δ base base' e he h

omit [LinearOrder σ] in
theorem source_zero : (α').f 0 = (T).map ((α).f 0) := by
  have h := Mapped.AugmentationZero.MappedAugmentationZero.normalized T α (FrameSheafResolution.BigCrystallineFrameSheafResolution.coefficientIso p W A J δ base')
  exact h.trans (Category.id_comp _)

omit [LinearOrder σ] in
theorem target_zero : (β').f 0 = (S).map ((β).f 0) := by
  have h := Mapped.AugmentationZero.MappedAugmentationZero.normalized S β (FrameSheafResolution.BigCrystallineFrameSheafResolution.coefficientIso p W A J δ base)
  exact h.trans (Category.id_comp _)

theorem presheaf_zero : (P).map ((α).f 0) ≫ (i).hom.f 0 = (s).hom ≫ (β).f 0 := by
  have hp := congrArg (fun f => f.f 0)
    (TwistAugmentation.BigCrystallineTwistAugmentation.original p W A J δ base base' e he h a)
  rw [← Category.assoc, HomologicalComplex.comp_f, Mapped.AugmentationZero.MappedAugmentationZero.mapped] at hp
  rw [HomologicalComplex.comp_f, CochainComplex.single₀_map_f_zero] at hp
  exact hp

theorem square : (F).map ((α').f 0) ≫
      (TwistSheafTransport.BigCrystallineTwistSheafTransport.complexIso p W A J δ base base' e he he' h a).hom.f 0 =
    (TwistSheafTransport.BigCrystallineTwistSheafTransport.structureIso p W A J δ base base' e he he' h).hom ≫ (β').f 0 := by
  rw [source_zero, target_zero, TwistSheafTransport.BigCrystallineTwistSheafTransport.component]
  let G₀ := NumberTheory.PadicHodge.IntegralComparison.BigCrystallineCohomology.modulePresheaf (p := p) (J := J) (δ := δ) base'
  let H₀ := NumberTheory.PadicHodge.IntegralComparison.BigCrystallineCohomology.modulePresheaf (p := p) (J := J) (δ := δ) base
  let K₀ := (FrameResolution.BigCrystallineFrameResolution.complex (p := p) (J := J) (δ := δ) (base := base') a).X 0
  let L₀ := (FrameResolution.BigCrystallineFrameResolution.complex (p := p) (J := J) (δ := δ) (base := base) a).X 0
  let b : G₀ ⟶ K₀ := (α).f 0
  let v : (P).obj K₀ ⟶ L₀ := (i).hom.f 0
  let w : (P).obj G₀ ⟶ H₀ := (s).hom
  let z : H₀ ⟶ L₀ := (β).f 0
  have hc : (F).map ((T).map b) ≫ (TwistSheafTransport.BigCrystallineTwistSheafTransport.comparisonIso p W A J δ base base' e he he' h).hom.app K₀ =
      (TwistSheafTransport.BigCrystallineTwistSheafTransport.comparisonIso p W A J δ base base' e he he' h).hom.app G₀ ≫ (S).map ((P).map b) :=
    (TwistSheafTransport.BigCrystallineTwistSheafTransport.comparisonIso p W A J δ base base' e he he' h).hom.naturality b
  have hp₀ : (P).map b ≫ v = w ≫ z := presheaf_zero p W A σ J δ base base' e he h a
  have hp : (S).map ((P).map b) ≫ (S).map v = (S).map w ≫ (S).map z :=
    ((S).map_comp ((P).map b) v).symm.trans ((congrArg (S).map hp₀).trans ((S).map_comp w z))
  change (F).map ((T).map b) ≫
      ((TwistSheafTransport.BigCrystallineTwistSheafTransport.comparisonIso p W A J δ base base' e he he' h).hom.app K₀ ≫ (S).map v) =
    ((TwistSheafTransport.BigCrystallineTwistSheafTransport.comparisonIso p W A J δ base base' e he he' h).hom.app G₀ ≫ (S).map w) ≫ (S).map z
  rw [← Category.assoc, hc, Category.assoc, hp, ← Category.assoc]

theorem original_square : (F).map ((α').f 0) ≫
      (TwistSheafTransport.BigCrystallineTwistSheafTransport.complexIso p W A J δ base base' e he he' h a).hom.f 0 =
    (NumberTheory.PadicHodge.PeriodInvariants.CrystallineTwistCohomology.structureTransport
      (p := p) e he he' h).hom ≫ (β').f 0 := by
  rw [← TwistSheafTransport.BigCrystallineTwistSheafTransport.structureIso_original]
  exact square p W A σ J δ base base' e he he' h a

end

end OAI.AlgebraicGeometry.Crystalline.Cohomology.BigCrystalline.TwistSheafAugmentation.BigCrystallineTwistSheafAugmentation
