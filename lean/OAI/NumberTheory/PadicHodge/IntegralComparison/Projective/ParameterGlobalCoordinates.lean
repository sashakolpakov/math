import OAI.NumberTheory.PadicHodge.IntegralComparison.Projective.ParameterChart

/-! # Parameter Global Coordinates -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Projective.ParameterGlobalCoordinates

noncomputable section

/-! The original global adjunction in a prescribed genuine parameter
chart, retaining its exact cohomological degree transport. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.MvPolynomial

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u
open OAI.NumberTheory.PadicHodge.IntegralComparison.Projective.IntrinsicOverlap.Intrinsic
variable {R : Type u} [CommRing R] [IsNoetherianRing R] {n c g : ℕ}
attribute [local instance] MvPolynomial.gradedAlgebra
  ParameterChart.ambientAlgebra ParameterChart.coordinateOrder
variable (X : Over (Spec (CommRingCat.of R))) (f : X ⟶ IntrinsicOverlap.Intrinsic.model R n)
  [IsClosedImmersion f.left] [Smooth X.hom] [IsProper X.hom] [SmoothOfRelativeDimension g X.hom]
  (U : (IntrinsicOverlap.Intrinsic.space R n).Opens) (hU : IsAffineOpen U) (hc : c = n - g)
  (s : Fin c → Γ(IntrinsicOverlap.Intrinsic.space R n, U))
  (hs : Koszul.OrientedTopCohomology.ideal Γ(IntrinsicOverlap.Intrinsic.space R n, U) s = LocalAdjunction.ideal X f U hU)
  (hreg : RingTheory.Sequence.IsWeaklyRegular Γ(IntrinsicOverlap.Intrinsic.space R n, U) (List.ofFn s))
  (bI : Module.Basis (Fin c) (LocalAdjunction.quotient X f U hU) (LocalAdjunction.ideal X f U hU).Cotangent)
  (hI : ∀ a, bI a = (LocalAdjunction.ideal X f U hU).toCotangent
    (ConormalKoszulPurity.conormalVectors Γ(IntrinsicOverlap.Intrinsic.space R n, U) (LocalAdjunction.ideal X f U hU) s hs a))
  (bQ : Module.Basis (Fin g) (LocalAdjunction.quotient X f U hU) Ω[LocalAdjunction.quotient X f U hU⁄R])
  (τ : Type u) [Fintype τ]
  [Algebra (MvPolynomial τ R) (Intrinsic.SmoothClosedSections.ring R X (f.left ⁻¹ᵁ U))]
  [IsScalarTower R (MvPolynomial τ R) (Intrinsic.SmoothClosedSections.ring R X (f.left ⁻¹ᵁ U))]
  [Algebra.Etale (MvPolynomial τ R) (Intrinsic.SmoothClosedSections.ring R X (f.left ⁻¹ᵁ U))]
  (j : Fin (n + 1)) (B : ℕ) (hB : n + 1 ≤ B) (hg : g ≤ n)
  (i : Fin (n + 1)) (hUi : U ≤ AlgebraicGeometry.SheafCohomology.Projective.MvPolynomialClosure.MvPolynomial.coordinateOpen (R := R) i)

def iso : (LocalAdjunction.dual X f j B).homology c ≅ AdjunctionGluing.targetSheaf X f g :=
  eqToIso (congrArg (fun d => (LocalAdjunction.dual X f j B).homology d) hc) ≪≫
    AdjunctionGlobal.iso X f g j B hB hg

include hI in
theorem sections_hom :
    (Affine.ModuleExactSections.sections U).map (iso X f hc j B hB hg).hom =
    (LocalAdjunction.sectionIso X f j B hB U hU i hUi
      ((congrArg (fun d => d + g) hc).trans (Nat.sub_add_cancel hg)) s hs hreg bI bQ τ).hom := by
  have hd := AdjunctionGlobalCoordinates.data_sections X f g j B hB hg U hU
    (ParameterChart.data X f U hU hc s hs hreg bI hI bQ τ) i hUi
  have hl := ParameterChart.data_sectionIso X f U hU hc s hs hreg bI hI bQ τ
    j B hB hg i hUi
  dsimp only [iso, Iso.trans_hom]
  rw [Functor.map_comp, hd]
  exact congrArg Iso.hom hl

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Projective.ParameterGlobalCoordinates
