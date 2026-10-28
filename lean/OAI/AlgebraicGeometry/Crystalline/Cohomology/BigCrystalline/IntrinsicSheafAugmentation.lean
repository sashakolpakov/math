import OAI.AlgebraicGeometry.Crystalline.Cohomology.BigCrystalline.IntrinsicSheafResolution
import OAI.AlgebraicGeometry.Crystalline.Cohomology.Mapped.AugmentationZero

/-! # Intrinsic Sheaf Augmentation -/

namespace OAI.AlgebraicGeometry.Crystalline.Cohomology.BigCrystalline.IntrinsicSheafAugmentation.BigCrystallineIntrinsicSheafAugmentation

noncomputable section

/-! # The actual sheaf-resolution isomorphism preserves its structure-sheaf augmentation -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

variable (p : ℕ) [Fact p.Prime] (k B σ : Type u) [Field k] [CharP k p]
  [CommRing B] [Algebra k B] (a : σ → B) [Fintype σ]

local notation "W" => WittVector p k
local notation "X" => OAI.AlgebraicGeometry.Crystalline.Cohomology.AffineFrameCover.CrystallineAffineFrameCover.affineScheme k B
local notation "I" => Ideal.span {(p : W)}
local notation "γ" => OAI.AlgebraicGeometry.Crystalline.Cohomology.Witt.DividedPowers.WittDividedPowers.wittDividedPowers p k
local notation "bX" => OAI.NumberTheory.PadicHodge.IntegralComparison.Witt.Crystalline.wittStructureMap p k X
local notation "F" => OAI.AlgebraicGeometry.Crystalline.Cohomology.BigCrystalline.IntrinsicSheafTransport.BigCrystallineIntrinsicSheafTransport.restriction p k B
local notation "P" => OAI.AlgebraicGeometry.Crystalline.Cohomology.BigCrystalline.IntrinsicResolution.BigCrystallineIntrinsicResolution.restriction p k B
local notation "S" => OAI.AlgebraicGeometry.Crystalline.Cohomology.PolynomialSheafResolution.CrystallinePolynomialSheafResolution.toSheaf p k X
local notation "T" => OAI.AlgebraicGeometry.Crystalline.Cohomology.BigCrystalline.FrameSheafResolution.BigCrystallineFrameSheafResolution.toSheaf p W B I γ bX
local notation "α" => OAI.AlgebraicGeometry.Crystalline.Cohomology.BigCrystalline.FrameResolution.BigCrystallineFrameResolution.augmentation (p := p) (J := I) (δ := γ) (base := bX) a
local notation "β" => OAI.AlgebraicGeometry.Crystalline.Cohomology.CrystallineFrame.Resolution.CrystallineFrameResolution.augmentation p k B σ a
local notation "α'" => OAI.AlgebraicGeometry.Crystalline.Cohomology.BigCrystalline.FrameSheafResolution.BigCrystallineFrameSheafResolution.augmentation p W B I γ bX a
local notation "β'" => OAI.AlgebraicGeometry.Crystalline.Cohomology.CrystallineFrame.SheafResolution.CrystallineFrameSheafResolution.augmentation p k B σ a
local notation "e" => OAI.AlgebraicGeometry.Crystalline.Cohomology.BigCrystalline.IntrinsicResolution.BigCrystallineIntrinsicResolution.iso p k B σ a
local notation "s" => OAI.AlgebraicGeometry.Crystalline.Cohomology.BigCrystalline.IntrinsicAugmentation.BigCrystallineIntrinsicAugmentation.sourceIso p k B

theorem big_zero : (α').f 0 = (T).map ((α).f 0) := by
  have h := Mapped.AugmentationZero.MappedAugmentationZero.normalized T α (FrameSheafResolution.BigCrystallineFrameSheafResolution.coefficientIso p W B I γ bX)
  exact h.trans (Category.id_comp _)

theorem native_zero : (β').f 0 = (S).map ((β).f 0) := by
  have h := Mapped.AugmentationZero.MappedAugmentationZero.normalized S β (PolynomialSheafResolution.CrystallinePolynomialSheafResolution.coefficientIso p k X)
  exact h.trans (Category.id_comp _)

theorem presheaf_zero : (P).map ((α).f 0) ≫ (e).hom.f 0 = (s).hom ≫ (β).f 0 := by
  have h := congrArg (fun f => f.f 0) (IntrinsicAugmentation.BigCrystallineIntrinsicAugmentation.square p k B σ a)
  rw [HomologicalComplex.comp_f, HomologicalComplex.comp_f, CochainComplex.single₀_map_f_zero] at h
  have hm : (IntrinsicAugmentation.BigCrystallineIntrinsicAugmentation.augmentation p k B σ a).f 0 = (P).map ((α).f 0) :=
    Mapped.AugmentationZero.MappedAugmentationZero.mapped P α
  rw [hm] at h
  exact h

theorem square : (F).map ((α').f 0) ≫ (IntrinsicSheafResolution.BigCrystallineIntrinsicSheafResolution.iso p k B σ a).hom.f 0 =
    (IntrinsicSheafTransport.BigCrystallineIntrinsicSheafTransport.structureIso p k B).hom ≫ (β').f 0 := by
  rw [big_zero, native_zero, IntrinsicSheafResolution.BigCrystallineIntrinsicSheafResolution.component]
  let G₀ := NumberTheory.PadicHodge.IntegralComparison.BigCrystallineCohomology.modulePresheaf (p := p) (J := I) (δ := γ) bX
  let K₀ := (FrameResolution.BigCrystallineFrameResolution.complex (p := p) (J := I) (δ := γ) (base := bX) a).X 0
  let L₀ := (CrystallineFrame.Resolution.CrystallineFrameResolution.complex p k B σ a).X 0
  let b : G₀ ⟶ K₀ := (α).f 0
  let v : (P).obj K₀ ⟶ L₀ := (e).hom.f 0
  let w : (P).obj G₀ ⟶ Site.functions p k X := (s).hom
  let z : Site.functions p k X ⟶ L₀ := (β).f 0
  have hc : (F).map ((T).map b) ≫ (IntrinsicSheafTransport.BigCrystallineIntrinsicSheafTransport.comparisonIso p k B).hom.app K₀ =
      (IntrinsicSheafTransport.BigCrystallineIntrinsicSheafTransport.comparisonIso p k B).hom.app G₀ ≫ (S).map ((P).map b) :=
    (IntrinsicSheafTransport.BigCrystallineIntrinsicSheafTransport.comparisonIso p k B).hom.naturality b
  have hp₀ : (P).map b ≫ v = w ≫ z := presheaf_zero p k B σ a
  have hp : (S).map ((P).map b) ≫ (S).map v = (S).map w ≫ (S).map z :=
    ((S).map_comp ((P).map b) v).symm.trans ((congrArg (S).map hp₀).trans ((S).map_comp w z))
  change (F).map ((T).map b) ≫
      ((IntrinsicSheafTransport.BigCrystallineIntrinsicSheafTransport.comparisonIso p k B).hom.app K₀ ≫ (S).map v) =
    ((IntrinsicSheafTransport.BigCrystallineIntrinsicSheafTransport.comparisonIso p k B).hom.app G₀ ≫ (S).map w) ≫ (S).map z
  rw [← Category.assoc, hc, Category.assoc, hp, ← Category.assoc]

end

end OAI.AlgebraicGeometry.Crystalline.Cohomology.BigCrystalline.IntrinsicSheafAugmentation.BigCrystallineIntrinsicSheafAugmentation
