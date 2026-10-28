import OAI.AlgebraicGeometry.Crystalline.Cohomology.BigCrystalline.IntrinsicResolution
import OAI.AlgebraicGeometry.Crystalline.Cohomology.Koszul.AugmentationFormula
import OAI.NumberTheory.PadicHodge.GeometricComparison.SmallCrystallineSheafAdapter

/-! # Intrinsic Augmentation -/

namespace OAI.AlgebraicGeometry.Crystalline.Cohomology.BigCrystalline.IntrinsicAugmentation.BigCrystallineIntrinsicAugmentation

noncomputable section

/-! # The big-to-native frame isomorphism preserves the original augmentation -/

open _root_.CategoryTheory _root_.AlgebraicGeometry Opposite
open scoped TensorProduct

universe u

variable (p : ℕ) [Fact p.Prime] (k B σ : Type u) [Field k] [CharP k p]
  [CommRing B] [Algebra k B] (a : σ → B) [Fintype σ]

local notation "W" => WittVector p k
local notation "X" => OAI.AlgebraicGeometry.Crystalline.Cohomology.AffineFrameCover.CrystallineAffineFrameCover.affineScheme k B
local notation "I" => Ideal.span {(p : W)}
local notation "γ" => OAI.AlgebraicGeometry.Crystalline.Cohomology.Witt.DividedPowers.WittDividedPowers.wittDividedPowers p k
local notation "bX" => OAI.NumberTheory.PadicHodge.IntegralComparison.Witt.Crystalline.wittStructureMap p k X
local notation "Big" => OAI.AlgebraicGeometry.Crystalline.Cohomology.BigCrystalline.FrameLifts.BigCrystallineFrameLifts.Site p W B I γ bX
local notation "C" => OAI.AlgebraicGeometry.Crystalline.Cohomology.Site.Object p k X
local notation "j" => OAI.AlgebraicGeometry.Crystalline.Cohomology.BigCrystalline.IntrinsicLifts.BigCrystallineIntrinsicLifts.inclusion p k B
local notation "G" => OAI.NumberTheory.PadicHodge.IntegralComparison.BigCrystallineCohomology.modulePresheaf (p := p) (J := I) (δ := γ) bX
local notation "F" => OAI.AlgebraicGeometry.Crystalline.Cohomology.BigCrystalline.IntrinsicResolution.BigCrystallineIntrinsicResolution.restriction p k B
local notation "K" => OAI.AlgebraicGeometry.Crystalline.Cohomology.BigCrystalline.FrameResolution.BigCrystallineFrameResolution.complex (p := p) (J := I) (δ := γ) (base := bX) a
local notation "α" => OAI.AlgebraicGeometry.Crystalline.Cohomology.BigCrystalline.FrameResolution.BigCrystallineFrameResolution.augmentation (p := p) (J := I) (δ := γ) (base := bX) a
local notation "β" => OAI.AlgebraicGeometry.Crystalline.Cohomology.CrystallineFrame.Resolution.CrystallineFrameResolution.augmentation p k B σ a

def sourceIso : (F).obj G ≅ Site.functions p k X :=
  NumberTheory.PadicHodge.GeometricComparison.SmallCrystallineSheafAdapter.SmallCrystallineAdapter.presheafIso

theorem big_zero (Q : Bigᵒᵖ) (x : (G).obj Q) :
    (((α).f 0).app Q).hom x =
      algebraMap Q.unop.ring (DividedPowerAlgebra Q.unop.ring (σ →₀ Q.unop.ring)) x ⊗ₜ[W]
        (exteriorPower.zeroEquiv W (σ →₀ W)).symm 1 := by
  exact Koszul.AugmentationFormula.KoszulAugmentationFormula.zero W σ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Q x

theorem native_zero (Q : Cᵒᵖ) (x : (Site.functions p k X).obj Q) :
    (((β).f 0).app Q).hom x =
      algebraMap Q.unop.thickening.ring
        (DividedPowerAlgebra Q.unop.thickening.ring (σ →₀ Q.unop.thickening.ring)) x ⊗ₜ[W]
        (exteriorPower.zeroEquiv W (σ →₀ W)).symm 1 := by
  exact Koszul.AugmentationFormula.KoszulAugmentationFormula.zero W σ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Q x

def augmentation : (CochainComplex.single₀ (Cᵒᵖ ⥤ ModuleCat W)).obj ((F).obj G) ⟶
    ((F).mapHomologicalComplex (.up ℕ)).obj K :=
  (HomologicalComplex.singleMapHomologicalComplex F (.up ℕ) 0).inv.app G ≫
    ((F).mapHomologicalComplex (.up ℕ)).map α

theorem square : augmentation p k B σ a ≫ (IntrinsicResolution.BigCrystallineIntrinsicResolution.iso p k B σ a).hom =
    (CochainComplex.single₀ _).map (sourceIso p k B).hom ≫ β := by
  apply HomologicalComplex.from_single_hom_ext
  apply NatTrans.ext
  funext Q
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  change Q.unop.thickening.ring at x
  let m := TensorProduct.map (IntrinsicCoordinates.BigCrystallineIntrinsicCoordinates.component p k B σ a Q.unop).toLinearMap
    (LinearMap.id : Module.End W (⋀[W]^0 (σ →₀ W)))
  have hb := congrArg m (big_zero p k B σ a ((j).op.obj Q) x)
  have hn := native_zero p k B σ a Q x
  change TensorProduct.map (IntrinsicCoordinates.BigCrystallineIntrinsicCoordinates.component p k B σ a Q.unop).toLinearMap
      LinearMap.id ((((α).f 0).app ((j).op.obj Q)).hom x) = (((β).f 0).app Q).hom x
  refine hb.trans ((show m _ = _ from ?_).trans hn.symm)
  change IntrinsicCoordinates.BigCrystallineIntrinsicCoordinates.rawEquiv p k B σ a Q.unop
      (algebraMap Q.unop.thickening.ring _ x) ⊗ₜ[W] _ = algebraMap Q.unop.thickening.ring _ x ⊗ₜ[W] _
  rw [AlgEquiv.commutes]
  rfl

end

end OAI.AlgebraicGeometry.Crystalline.Cohomology.BigCrystalline.IntrinsicAugmentation.BigCrystallineIntrinsicAugmentation
