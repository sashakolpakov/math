import OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.FrameAmbient
import OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.FrameClosed
import OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.FrameBaseIdeal
import OAI.NumberTheory.PadicHodge.GeometricComparison.Crystalline.OpenFactor
import OAI.NumberTheory.PadicHodge.GeometricComparison.Crystalline.ClosedRange
import OAI.NumberTheory.PadicHodge.GeometricComparison.Crystalline.AmbientFormula

/-! # Open Factor -/

namespace OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.OpenFactor.IntrinsicPadicOpenFactor

noncomputable section

/-! A map to a native affine frame factors through a smaller affine frame
when its original closed image lies in that smaller open. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

open OAI.NumberTheory.PadicHodge.IntegralComparison.BigCrystallineSite
variable (p : ℕ) [Fact p.Prime]
  (X : Over (Spec (CommRingCat.of ℤ_[p]))) [Smooth X.hom]
  (Y : Over (Spec (CommRingCat.of (ZMod p)))) (f : Y.left ⟶ X.left)
  (hp : IsPullback f Y.hom X.hom (Spec.map (CommRingCat.ofHom (PadicInt.toZMod : ℤ_[p] →+* ZMod p))))
  (n : ℕ) (U V : X.left.Opens) (hU : IsAffineOpen U) (hV : IsAffineOpen V) (hUV : U ≤ V)
  (T : IntegralComparison.BigCrystallineSite.Object p (WittVector p (ZMod p)) (Ideal.span {(p : WittVector p (ZMod p))})
    (AlgebraicGeometry.Crystalline.Cohomology.Witt.DividedPowers.WittDividedPowers.wittDividedPowers p (ZMod p))
    (IntegralComparison.Witt.Crystalline.wittStructureMap p (ZMod p) Y))
  (β : T ⟶ (ChartImage.IntrinsicPadicOpenFrame.frame p X Y f hp V hV n).obj)
  (h : Set.range T.mapToX ⊆ (f ⁻¹ᵁ U : Set Y.left))

local notation "α" => OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.PadicFrameRestriction.IntrinsicPadicFrameRestriction.map p X Y f hp U V hU hV hUV n

theorem ambient_open : IsOpenImmersion (IntegralComparison.BigCrystallineSite.Object.ambient.map
    (PadicFrameRestriction.IntrinsicPadicFrameRestriction.map p X Y f hp U V hU hV hUV n).hom) :=
  Crystalline.AmbientFormula.CrystallineAmbientFormula.openImmersion
    (PadicFrameRestriction.IntrinsicPadicFrameRestriction.map p X Y f hp U V hU hV hUV n)
    (FrameAmbient.IntrinsicPadicFrameAmbient.openImmersion p X Y f hp U V hU hV hUV n)

include h in
theorem ambient_range : Set.range (IntegralComparison.BigCrystallineSite.Object.ambient.map β) ⊆ Set.range (IntegralComparison.BigCrystallineSite.Object.ambient.map (α).hom) := by
  let := FrameClosed.IntrinsicPadicFrameClosed.openImmersion p X Y f hp n V hV
  apply Crystalline.ClosedRange.CrystallineClosedRange.ambient_range (α).hom β
  apply Crystalline.ClosedRange.CrystallineClosedRange.closed_range (α).hom β
    (Scheme.Hom.isOpenEmbedding (ChartImage.IntrinsicPadicOpenFrame.frame p X Y f hp V hV n).obj.mapToX).injective
  rw [FrameClosed.IntrinsicPadicFrameClosed.range]
  exact h

include h in
theorem exists_factor : ∃ γ : T ⟶ (ChartImage.IntrinsicPadicOpenFrame.frame p X Y f hp U hU n).obj, γ ≫ (α).hom = β := by
  let : IsOpenImmersion (IntegralComparison.BigCrystallineSite.Object.ambient.map (α).hom) := ambient_open p X Y f hp n U V hU hV hUV
  exact Crystalline.OpenFactor.CrystallineOpenFactor.exists_factor (α).hom β (FrameBaseIdeal.IntrinsicPadicFrameBaseIdeal.generated p X Y f hp n U hU)
    (ambient_range p X Y f hp n U V hU hV hUV T β h)

def lift : T ⟶ (ChartImage.IntrinsicPadicOpenFrame.frame p X Y f hp U hU n).obj :=
  (exists_factor p X Y f hp n U V hU hV hUV T β h).choose

theorem lift_comp : lift p X Y f hp n U V hU hV hUV T β h ≫ (α).hom = β :=
  (exists_factor p X Y f hp n U V hU hV hUV T β h).choose_spec

end

end OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.OpenFactor.IntrinsicPadicOpenFactor
