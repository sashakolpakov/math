import OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedEtale.ZeroFormSections
import OAI.NumberTheory.PadicHodge.IntegralComparison.EtaleZero.FrameMapVectors
import OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedFrame.Diagonal
import OAI.NumberTheory.PadicHodge.IntegralComparison.Module.PresheafSections
import OAI.NumberTheory.PadicHodge.IntegralComparison.RelativeFrame.FormNaturality

/-! # Zero Canonical Sections -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedEtale.ZeroCanonicalSections

noncomputable section

/-!
# IntegralComparison: the canonical frame section map is bijective before coefficient lifting
-/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry Opposite

open OAI.NumberTheory.PadicHodge.IntegralComparison.BigCrystallineSite OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedCrystalline.Site OAI.NumberTheory.PadicHodge.IntegralComparison.Witt.Crystalline OAI.NumberTheory.PadicHodge.IntegralComparison.Crystalline.Presentation

universe u

variable (p : ℕ) [Fact p.Prime] (k C σ : Type u) [Field k] [Fintype k] [CharP k p]
  [CommRing C] [Algebra k C] [LinearOrder σ] [Fintype σ]
  [Algebra (MvPolynomial σ k) C] [IsScalarTower k (MvPolynomial σ k) C]
  [Algebra.Etale (MvPolynomial σ k) C]

local notation "W" => WittVector p k
local notation "f" => OAI.NumberTheory.PadicHodge.IntegralComparison.Witt.Crystalline.wittStructureMap p k (OAI.NumberTheory.PadicHodge.IntegralComparison.Crystalline.Presentation.affineScheme k C)
local notation "F" => OAI.NumberTheory.PadicHodge.IntegralComparison.ZeroLevel.LevelFrame.boundedFrame p k C
local notation "Q" => OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedCrystalline.Site.inclusion (p := p) (J := Ideal.span {(p : W)})
  (δ := AlgebraicGeometry.Crystalline.Cohomology.Witt.DividedPowers.WittDividedPowers.wittDividedPowers p k) f 0
local notation "H" => OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedFrame.Diagram.productDiagram F
local notation "π" => OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedFrame.Diagram.projection F
local notation "τ" => OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedFrame.Symbols.frameProjection F

def sectionMap (m : ℕ) := Module.PresheafSections.sectionMap W
  (RelativeFrame.FormMap.frameModule (F).obj m)
  (RelativeCrystalline.ModuleMaps.formsPresheaf H Q π m)
  (RelativeFrame.FormNaturality.mapPresheaf H Q π (F).obj τ m)

theorem inverse_section (m : ℕ) (ω : RelativeFrame.FormMap.frameModule (F).obj m) :
    ZeroFormSections.homLinearEquiv p k C σ m (sectionMap p k C m ω) = ω := by
  obtain ⟨v, rfl⟩ := (EtaleZero.FrameFreeModule.linearEquiv p k C σ m).surjective ω
  have ha := Module.PresheafSections.sectionMap_app_one W
    (RelativeFrame.FormMap.frameModule (F).obj m)
    (RelativeCrystalline.ModuleMaps.formsPresheaf H Q π m)
    (RelativeFrame.FormNaturality.mapPresheaf H Q π (F).obj τ m)
    (EtaleZero.FrameFreeModule.linearEquiv p k C σ m v) (op F)
  have hc := (congrArg (ZeroFormPresheaf.basis p k C σ F m).equivFun
    (ha.trans (EtaleZero.FrameMapVectors.map_vectors p k C σ F m v))).trans
      ((ZeroFormPresheaf.basis p k C σ F m).equivFun.apply_symm_apply
        (fun i => ((τ).app F).ringMap (v i)))
  have hd : (fun i => ((Q).map (prod.lift (𝟙 F) (𝟙 F))).ringMap
      ((ZeroFormPresheaf.basis p k C σ F m).equivFun
        ((sectionMap p k C m (EtaleZero.FrameFreeModule.linearEquiv p k C σ m v)).app (op F) (1 : W)) i)) = v := by
    funext i
    exact (congrArg (fun t => ((Q).map (prod.lift (𝟙 F) (𝟙 F))).ringMap (t i)) hc).trans
      (BoundedFrame.Diagonal.diagonal_ringMap F (v i))
  exact (ZeroFormSections.homLinearEquiv_apply p k C σ m _).trans
    (congrArg (EtaleZero.FrameFreeModule.linearEquiv p k C σ m) hd)

include σ in
theorem sectionMap_bijective (m : ℕ) : Function.Bijective (sectionMap p k C m) := by
  constructor
  · intro ω η h
    exact (inverse_section p k C σ m ω).symm.trans
      ((congrArg (ZeroFormSections.homLinearEquiv p k C σ m) h).trans
        (inverse_section p k C σ m η))
  · intro a
    refine ⟨ZeroFormSections.homLinearEquiv p k C σ m a, ?_⟩
    apply (ZeroFormSections.homLinearEquiv p k C σ m).injective
    exact inverse_section p k C σ m _

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedEtale.ZeroCanonicalSections
