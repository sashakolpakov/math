import OAI.AlgebraicGeometry.Crystalline.Cohomology.BigCrystalline.IntrinsicSections
import OAI.AlgebraicGeometry.Crystalline.Cohomology.SheafSectionHomEquiv
import OAI.AlgebraicGeometry.Crystalline.Cohomology.ExtZero
import OAI.NumberTheory.PadicHodge.IntegralComparison.Ext.ZeroPresheafSections

/-! # Intrinsic Section Coordinates -/

namespace OAI.AlgebraicGeometry.Crystalline.Cohomology.BigCrystalline.IntrinsicSectionCoordinates.BigCrystallineIntrinsicSectionCoordinates

noncomputable section

/-! # The original big-to-native section map in actual presheaf coordinates -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

open _root_.CategoryTheory.Abelian

universe u

variable (p : ℕ) [Fact p.Prime] (k B σ : Type u) [Field k] [CharP k p]
  [CommRing B] [Algebra k B] (a : σ → B) [Fintype σ]

local notation "W" => WittVector p k
local notation "R" => OAI.AlgebraicGeometry.Crystalline.Cohomology.Site.CoefficientRing p k
local notation "X" => OAI.AlgebraicGeometry.Crystalline.Cohomology.AffineFrameCover.CrystallineAffineFrameCover.affineScheme k B
local notation "I" => Ideal.span {(p : W)}
local notation "γ" => OAI.AlgebraicGeometry.Crystalline.Cohomology.Witt.DividedPowers.WittDividedPowers.wittDividedPowers p k
local notation "bX" => OAI.NumberTheory.PadicHodge.IntegralComparison.Witt.Crystalline.wittStructureMap p k X
local notation "Big" => OAI.AlgebraicGeometry.Crystalline.Cohomology.BigCrystalline.FrameLifts.BigCrystallineFrameLifts.Site p W B I γ bX
local notation "C" => OAI.AlgebraicGeometry.Crystalline.Cohomology.Site.Object p k X
local notation "U" => OAI.NumberTheory.PadicHodge.IntegralComparison.BigCrystallineSite.Object.topology (p := p) (B := W) (J := I) (δ := γ) (f := bX)
local notation "T" => OAI.AlgebraicGeometry.Crystalline.Cohomology.Site.topology p k X
local notation "ι" => OAI.AlgebraicGeometry.Crystalline.Cohomology.BigCrystalline.IntrinsicLifts.BigCrystallineIntrinsicLifts.inclusion p k B
local notation "F" => OAI.AlgebraicGeometry.Crystalline.Cohomology.BigCrystalline.IntrinsicSheafTransport.BigCrystallineIntrinsicSheafTransport.restriction p k B
local notation "K" => OAI.AlgebraicGeometry.Crystalline.Cohomology.BigCrystalline.FrameSheafResolution.BigCrystallineFrameSheafResolution.complex p W B I γ bX a
local notation "L" => OAI.AlgebraicGeometry.Crystalline.Cohomology.CrystallineFrame.SheafResolution.CrystallineFrameSheafResolution.complex p k B σ a
local notation "A₀" => OAI.NumberTheory.PadicHodge.IntegralComparison.BigCrystallineCohomology.constantUnit (p := p) (J := I) (δ := γ) bX
local notation "A₁" => OAI.AlgebraicGeometry.Crystalline.Cohomology.Site.coefficientSheaf p k X

def sourceSections (n : ℕ) (x : A₀ ⟶ (K).X n) :
    (Functor.const Bigᵒᵖ).obj (ModuleCat.of R R) ⟶ ((K).X n).obj :=
  NumberTheory.PadicHodge.IntegralComparison.Ext.ZeroPresheafSections.homLinearEquiv R U ((K).X n) x

def targetSections (n : ℕ) (x : A₁ ⟶ (L).X n) :
    (Functor.const Cᵒᵖ).obj (ModuleCat.of R R) ⟶ ((L).X n).obj :=
  NumberTheory.PadicHodge.IntegralComparison.Ext.ZeroPresheafSections.homLinearEquiv R T ((L).X n) x

def transport (n : ℕ) (x : A₀ ⟶ (K).X n) : A₁ ⟶ (L).X n :=
  (IntrinsicSheafTransport.BigCrystallineIntrinsicSheafTransport.constantIso p k B).inv ≫ (F).map x ≫
    (IntrinsicSheafResolution.BigCrystallineIntrinsicSheafResolution.iso p k B σ a).hom.f n

theorem sections (n : ℕ) (x : A₀ ⟶ (K).X n) :
    targetSections p k B σ a n (transport p k B σ a n x) =
      Functor.whiskerLeft (ι).op (sourceSections p k B σ a n x) ≫
        ((IntrinsicSheafResolution.BigCrystallineIntrinsicSheafResolution.iso p k B σ a).hom.f n).hom :=
  SheafSectionHomEquiv.SheafSectionRestriction.homEquiv T U ι (ModuleCat.of R R) ((K).X n) ((L).X n) x
    ((IntrinsicSheafResolution.BigCrystallineIntrinsicSheafResolution.iso p k B σ a).hom.f n)

theorem map_mk (n : ℕ) (x : A₀ ⟶ (K).X n) :
    ((IntrinsicSections.BigCrystallineIntrinsicSections.map p k B σ a).f n).hom (Ext.mk₀ x) =
      Ext.mk₀ (transport p k B σ a n x) :=
  ExtZero.ExtZeroTransport.mk F (IntrinsicSheafTransport.BigCrystallineIntrinsicSheafTransport.constantIso p k B).inv
    ((IntrinsicSheafResolution.BigCrystallineIntrinsicSheafResolution.iso p k B σ a).hom.f n) x

end

end OAI.AlgebraicGeometry.Crystalline.Cohomology.BigCrystalline.IntrinsicSectionCoordinates.BigCrystallineIntrinsicSectionCoordinates
