import OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.FrameFunctor
import OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.FrameClosed
import OAI.NumberTheory.PadicHodge.GeometricComparison.Crystalline.OpenFactor
import OAI.NumberTheory.PadicHodge.GeometricComparison.Crystalline.ClosedRange

/-! # Open Factor -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.OpenFactor

noncomputable section

/-! Incoming crystalline maps factor through smaller actual affine
frames whenever their special-fiber image lies in the smaller open. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open OAI.NumberTheory.PadicHodge.IntegralComparison.BigCrystallineSite

variable (p : ℕ) [Fact p.Prime] (k : Type) [Field k] [Fintype k] [CharP k p]
  (n : ℕ) (X : Over (Spec (CommRingCat.of (Truncated.Witt.Ring p k n)))) [Smooth X.hom]
  (Y : Over (Spec (CommRingCat.of k))) (f : Y.left ⟶ X.left)
  (hp : IsPullback f Y.hom X.hom
    (Spec.map (CommRingCat.ofHom (Truncated.Witt.reduction p k n))))
  (U V : X.left.Opens) (hU : IsAffineOpen U) (hV : IsAffineOpen V) (hUV : U ≤ V)

local notation "α" => OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.FrameFunctor.map p k n X Y f hp U V hU hV hUV

theorem ambient_open : IsOpenImmersion (BigCrystallineSite.Object.ambient.map (α).hom) := by
  let g := Spec.map (X.left.presheaf.map (homOfLE hUV).op)
  have he : BigCrystallineSite.Object.ambient.map (α).hom = g := by
    apply congrArg Spec.map
    apply CommRingCat.hom_ext
    ext a
    exact FrameFunctor.map_apply p k n X Y f hp U V hU hV hUV a
  rw [he]
  have hc : g ≫ hV.fromSpec = hU.fromSpec := hV.map_fromSpec hU (homOfLE hUV).op
  let : IsOpenImmersion (g ≫ hV.fromSpec) := hc.symm ▸ inferInstanceAs (IsOpenImmersion hU.fromSpec)
  exact IsOpenImmersion.of_comp g hV.fromSpec

variable (T : BigCrystallineSite.Object p (WittVector p k) (Ideal.span {(p : WittVector p k)})
    (AlgebraicGeometry.Crystalline.Cohomology.Witt.DividedPowers.WittDividedPowers.wittDividedPowers p k) (Witt.Crystalline.wittStructureMap p k Y))
  (β : T ⟶ (Truncated.AffineModelFrame.frame p k n X Y f hp V hV).obj)
  (h : Set.range T.mapToX ⊆ (f ⁻¹ᵁ U : Set Y.left))

include h in
theorem ambient_range : Set.range (BigCrystallineSite.Object.ambient.map β) ⊆ Set.range (BigCrystallineSite.Object.ambient.map (α).hom) := by
  let := FrameClosed.openImmersion p k n X Y f hp V hV
  apply GeometricComparison.Crystalline.ClosedRange.CrystallineClosedRange.ambient_range (α).hom β
  apply GeometricComparison.Crystalline.ClosedRange.CrystallineClosedRange.closed_range (α).hom β
    (Scheme.Hom.isOpenEmbedding (Truncated.AffineModelFrame.frame p k n X Y f hp V hV).obj.mapToX).injective
  rw [FrameClosed.range]
  exact h

include h in
theorem exists_factor :
    ∃ γ : T ⟶ (Truncated.AffineModelFrame.frame p k n X Y f hp U hU).obj, γ ≫ (α).hom = β := by
  let : IsOpenImmersion (BigCrystallineSite.Object.ambient.map (α).hom) := ambient_open p k n X Y f hp U V hU hV hUV
  exact GeometricComparison.Crystalline.OpenFactor.CrystallineOpenFactor.exists_factor (α).hom β
    (FrameClosed.ideal_generated p k n X Y f hp U hU)
    (ambient_range p k n X Y f hp U V hU hV hUV T β h)

def lift : T ⟶ (Truncated.AffineModelFrame.frame p k n X Y f hp U hU).obj :=
  (exists_factor p k n X Y f hp U V hU hV hUV T β h).choose

theorem lift_comp : lift p k n X Y f hp U V hU hV hUV T β h ≫ (α).hom = β :=
  (exists_factor p k n X Y f hp U V hU hV hUV T β h).choose_spec

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.OpenFactor
