import OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedSmooth.WittFormSections
import OAI.NumberTheory.PadicHodge.IntegralComparison.SmoothWitt.FrameMapVectors
import OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedFrame.Diagonal
import OAI.NumberTheory.PadicHodge.IntegralComparison.Module.PresheafSections
import OAI.NumberTheory.PadicHodge.IntegralComparison.RelativeFrame.FormNaturality

/-! # Witt Canonical Sections -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedSmooth.WittCanonicalSections

noncomputable section

/-!
# IntegralComparison: the canonical frame section map is bijective before coefficient lifting
-/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry Opposite

open OAI.NumberTheory.PadicHodge.IntegralComparison.BigCrystallineSite OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedCrystalline.Site OAI.NumberTheory.PadicHodge.IntegralComparison.Witt.Crystalline OAI.NumberTheory.PadicHodge.IntegralComparison.Crystalline.Presentation

universe u

variable (p : ℕ) [Fact p.Prime] (k A C σ : Type u) [Field k] [CharP k p]
  [CommRing A] [Algebra (WittVector p k) A] [Module.Flat (WittVector p k) A]
  [CommRing C] [Algebra k C] [LinearOrder σ] [Fintype σ]
  [Algebra (MvPolynomial σ (WittVector p k)) A]
  [IsScalarTower (WittVector p k) (MvPolynomial σ (WittVector p k)) A]
  [Algebra.Etale (MvPolynomial σ (WittVector p k)) A]
  (ρ : A →+* C) (hρ : Function.Surjective ρ) (hker : RingHom.ker ρ = Ideal.span {(p : A)})
  (hbase : ∀ w : WittVector p k, ρ (algebraMap (WittVector p k) A w) =
    algebraMap k C (WittVector.constantCoeff w)) (n : ℕ)

local notation "W" => WittVector p k
local notation "f" => OAI.NumberTheory.PadicHodge.IntegralComparison.Witt.Crystalline.wittStructureMap p k (OAI.NumberTheory.PadicHodge.IntegralComparison.Crystalline.Presentation.affineScheme k C)

local instance structureMap_separated : IsSeparated f :=
  WittFrameProduct.structureMap_separated p k C

local notation "F" => OAI.NumberTheory.PadicHodge.IntegralComparison.SmoothWitt.WittFrame.boundedFrame p k A C ρ hρ hker hbase n
local notation "Q" => OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedCrystalline.Site.inclusion (p := p) (J := Ideal.span {(p : W)})
  (δ := AlgebraicGeometry.Crystalline.Cohomology.Witt.DividedPowers.WittDividedPowers.wittDividedPowers p k) f n
local notation "H" => OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedFrame.Diagram.productDiagram F
local notation "π" => OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedFrame.Diagram.projection F
local notation "τ" => OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedFrame.Symbols.frameProjection F

def sectionMap (m : ℕ) := IntegralComparison.Module.PresheafSections.sectionMap W
  (RelativeFrame.FormMap.frameModule (F).obj m)
  (RelativeCrystalline.ModuleMaps.formsPresheaf H Q π m)
  (RelativeFrame.FormNaturality.mapPresheaf H Q π (F).obj τ m)

theorem inverse_section (m : ℕ) (ω : RelativeFrame.FormMap.frameModule (F).obj m) :
    WittFormSections.homLinearEquiv p k A C σ ρ hρ hker hbase n m (sectionMap p k A C ρ hρ hker hbase n m ω) = ω := by
  obtain ⟨v, rfl⟩ := (SmoothWitt.FrameFreeModule.linearEquiv p k A C σ ρ hρ hker hbase n m).surjective ω
  have ha := IntegralComparison.Module.PresheafSections.sectionMap_app_one W
    (RelativeFrame.FormMap.frameModule (F).obj m)
    (RelativeCrystalline.ModuleMaps.formsPresheaf H Q π m)
    (RelativeFrame.FormNaturality.mapPresheaf H Q π (F).obj τ m)
    (SmoothWitt.FrameFreeModule.linearEquiv p k A C σ ρ hρ hker hbase n m v) (op F)
  have hc := (congrArg (WittFormPresheaf.basis p k A C σ ρ hρ hker hbase n F m).equivFun
    (ha.trans (SmoothWitt.FrameMapVectors.map_vectors p k A C σ ρ hρ hker hbase n F m v))).trans
      ((WittFormPresheaf.basis p k A C σ ρ hρ hker hbase n F m).equivFun.apply_symm_apply
        (fun i => ((τ).app F).ringMap (v i)))
  have hd : (fun i => ((Q).map (prod.lift (𝟙 F) (𝟙 F))).ringMap
      ((WittFormPresheaf.basis p k A C σ ρ hρ hker hbase n F m).equivFun
        ((sectionMap p k A C ρ hρ hker hbase n m (SmoothWitt.FrameFreeModule.linearEquiv p k A C σ ρ hρ hker hbase n m v)).app (op F) (1 : W)) i)) = v := by
    funext i
    exact (congrArg (fun t => ((Q).map (prod.lift (𝟙 F) (𝟙 F))).ringMap (t i)) hc).trans
      (BoundedFrame.Diagonal.diagonal_ringMap F (v i))
  exact (WittFormSections.homLinearEquiv_apply p k A C σ ρ hρ hker hbase n m _).trans
    (congrArg (SmoothWitt.FrameFreeModule.linearEquiv p k A C σ ρ hρ hker hbase n m) hd)

include σ in
theorem sectionMap_bijective (m : ℕ) : Function.Bijective (sectionMap p k A C ρ hρ hker hbase n m) := by
  constructor
  · intro ω η h
    exact (inverse_section p k A C σ ρ hρ hker hbase n m ω).symm.trans
      ((congrArg (WittFormSections.homLinearEquiv p k A C σ ρ hρ hker hbase n m) h).trans
        (inverse_section p k A C σ ρ hρ hker hbase n m η))
  · intro a
    refine ⟨WittFormSections.homLinearEquiv p k A C σ ρ hρ hker hbase n m a, ?_⟩
    apply (WittFormSections.homLinearEquiv p k A C σ ρ hρ hker hbase n m).injective
    exact inverse_section p k A C σ ρ hρ hker hbase n m _

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedSmooth.WittCanonicalSections
