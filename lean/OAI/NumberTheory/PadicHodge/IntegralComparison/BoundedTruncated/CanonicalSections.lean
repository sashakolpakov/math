import OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedTruncated.FormSections
import OAI.NumberTheory.PadicHodge.IntegralComparison.Truncated.FrameMapVectors
import OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedFrame.Diagonal
import OAI.NumberTheory.PadicHodge.IntegralComparison.Module.PresheafSections
import OAI.NumberTheory.PadicHodge.IntegralComparison.RelativeFrame.FormNaturality

/-! # Canonical Sections -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedTruncated.CanonicalSections

noncomputable section

/-!
# IntegralComparison: the canonical frame section map is bijective before coefficient lifting
-/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry Opposite

open OAI.NumberTheory.PadicHodge.IntegralComparison.BigCrystallineSite OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedCrystalline.Site OAI.NumberTheory.PadicHodge.IntegralComparison.Witt.Crystalline OAI.NumberTheory.PadicHodge.IntegralComparison.Crystalline.Presentation

variable (p : ℕ) [Fact p.Prime] (k : Type) [Field k] [Fintype k] [CharP k p]
  (n : ℕ) (A C σ : Type) [CommRing A] [CommRing C]
  [Algebra (Truncated.Witt.Ring p k n) A]
  [Algebra.Smooth (Truncated.Witt.Ring p k n) A] [Algebra k C]
  [LinearOrder σ] [Fintype σ]
  [Algebra (MvPolynomial σ (Truncated.Witt.Ring p k n)) A]
  [IsScalarTower (Truncated.Witt.Ring p k n)
    (MvPolynomial σ (Truncated.Witt.Ring p k n)) A]
  [Algebra.Etale (MvPolynomial σ (Truncated.Witt.Ring p k n)) A]
  (ρ : A →+* C) (hρ : Function.Surjective ρ)
  (hker : RingHom.ker ρ = Ideal.span {(p : A)})
  (hbase : ∀ w : WittVector p k,
    ρ (algebraMap (Truncated.Witt.Ring p k n) A (Truncated.Witt.quotient p k n w)) =
      algebraMap k C (WittVector.constantCoeff w))

local notation "W" => WittVector p k
local notation "f" => OAI.NumberTheory.PadicHodge.IntegralComparison.Witt.Crystalline.wittStructureMap p k (OAI.NumberTheory.PadicHodge.IntegralComparison.Crystalline.Presentation.affineScheme k C)

local instance structureMap_separated : IsSeparated f :=
  FrameProduct.structureMap_separated p k C

local notation "F" => OAI.NumberTheory.PadicHodge.IntegralComparison.Truncated.SmoothFrame.boundedFrame p A C ρ hρ hker k n hbase
local notation "Q" => OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedCrystalline.Site.inclusion (p := p) (J := Ideal.span {(p : W)})
  (δ := AlgebraicGeometry.Crystalline.Cohomology.Witt.DividedPowers.WittDividedPowers.wittDividedPowers p k) f n
local notation "H" => OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedFrame.Diagram.productDiagram F
local notation "π" => OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedFrame.Diagram.projection F
local notation "τ" => OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedFrame.Symbols.frameProjection F

def sectionMap (m : ℕ) := Module.PresheafSections.sectionMap W
  (RelativeFrame.FormMap.frameModule (F).obj m)
  (RelativeCrystalline.ModuleMaps.formsPresheaf H Q π m)
  (RelativeFrame.FormNaturality.mapPresheaf H Q π (F).obj τ m)

omit [Fintype k] in
theorem inverse_section (m : ℕ) (ω : RelativeFrame.FormMap.frameModule (F).obj m) :
    FormSections.homLinearEquiv p k n A C σ ρ hρ hker hbase m (sectionMap p k n A C ρ hρ hker hbase m ω) = ω := by
  obtain ⟨v, rfl⟩ := (Truncated.FrameFreeModule.linearEquiv p k n A C σ ρ hρ hker hbase m).surjective ω
  have ha := Module.PresheafSections.sectionMap_app_one W
    (RelativeFrame.FormMap.frameModule (F).obj m)
    (RelativeCrystalline.ModuleMaps.formsPresheaf H Q π m)
    (RelativeFrame.FormNaturality.mapPresheaf H Q π (F).obj τ m)
    (Truncated.FrameFreeModule.linearEquiv p k n A C σ ρ hρ hker hbase m v) (op F)
  have hc := (congrArg (FormPresheaf.basis p k n A C σ ρ hρ hker hbase F m).equivFun
    (ha.trans (Truncated.FrameMapVectors.map_vectors p k n A C σ ρ hρ hker hbase F m v))).trans
      ((FormPresheaf.basis p k n A C σ ρ hρ hker hbase F m).equivFun.apply_symm_apply
        (fun i => ((τ).app F).ringMap (v i)))
  have hd : (fun i => ((Q).map (prod.lift (𝟙 F) (𝟙 F))).ringMap
      ((FormPresheaf.basis p k n A C σ ρ hρ hker hbase F m).equivFun
        ((sectionMap p k n A C ρ hρ hker hbase m (Truncated.FrameFreeModule.linearEquiv p k n A C σ ρ hρ hker hbase m v)).app (op F) (1 : W)) i)) = v := by
    funext i
    exact (congrArg (fun t => ((Q).map (prod.lift (𝟙 F) (𝟙 F))).ringMap (t i)) hc).trans
      (BoundedFrame.Diagonal.diagonal_ringMap F (v i))
  exact (FormSections.homLinearEquiv_apply p k n A C σ ρ hρ hker hbase m _).trans
    (congrArg (Truncated.FrameFreeModule.linearEquiv p k n A C σ ρ hρ hker hbase m) hd)

include σ in
omit [Fintype k] in
theorem sectionMap_bijective (m : ℕ) : Function.Bijective (sectionMap p k n A C ρ hρ hker hbase m) := by
  constructor
  · intro ω η h
    exact (inverse_section p k n A C σ ρ hρ hker hbase m ω).symm.trans
      ((congrArg (FormSections.homLinearEquiv p k n A C σ ρ hρ hker hbase m) h).trans
        (inverse_section p k n A C σ ρ hρ hker hbase m η))
  · intro a
    refine ⟨FormSections.homLinearEquiv p k n A C σ ρ hρ hker hbase m a, ?_⟩
    apply (FormSections.homLinearEquiv p k n A C σ ρ hρ hker hbase m).injective
    exact inverse_section p k n A C σ ρ hρ hker hbase m _

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedTruncated.CanonicalSections
