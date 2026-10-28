import OAI.NumberTheory.PadicHodge.IntegralComparison.Projective.AdjunctionGlobalCoordinates

/-! # Parameter Chart -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Projective.ParameterChart

noncomputable section

/-! Actual normal equations and finite étale coordinates determine
a genuine projective adjunction chart, with its original degree index. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.MvPolynomial

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u
open OAI.NumberTheory.PadicHodge.IntegralComparison.Projective.IntrinsicOverlap.Intrinsic
variable {R : Type u} [CommRing R] [IsNoetherianRing R] {n c g : ℕ}
attribute [local instance] MvPolynomial.gradedAlgebra
variable (X : Over (Spec (CommRingCat.of R))) (f : X ⟶ IntrinsicOverlap.Intrinsic.model R n)
  [IsClosedImmersion f.left] (U : (IntrinsicOverlap.Intrinsic.space R n).Opens) (hU : IsAffineOpen U)

local instance ambientAlgebra : Algebra R Γ(IntrinsicOverlap.Intrinsic.space R n, U) :=
  AlgebraicGeometry.Crystalline.Cohomology.AlgebraicForms.AlgebraicDeRham.sectionAlgebra R (IntrinsicOverlap.Intrinsic.model R n) U

variable (hc : c = n - g)
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

local instance coordinateOrder : LinearOrder τ :=
  LinearOrder.lift' (Fintype.equivFin τ) (Fintype.equivFin τ).injective

def data : AdjunctionCharts.Data X f g U hU := by
  subst c
  exact
    { equations := s
      generates := hs
      regular := hreg
      conormalBasis := bI
      conormalBasis_apply := hI
      quotientBasis := bQ
      coordinateIndex := τ
      finiteVariables := inferInstance
      coordinates := inferInstance
      coordinateTower := inferInstance
      coordinateEtale := inferInstance }

variable [Smooth X.hom] (j : Fin (n + 1)) (B : ℕ) (hB : n + 1 ≤ B)
  (hg : g ≤ n) (i : Fin (n + 1)) (hUi : U ≤ AlgebraicGeometry.SheafCohomology.Projective.MvPolynomialClosure.MvPolynomial.coordinateOpen (R := R) i)

theorem data_sectionIso :
    (Affine.ModuleExactSections.sections U).mapIso
      (eqToIso (congrArg (fun d => (LocalAdjunction.dual X f j B).homology d) hc)) ≪≫
        (data X f U hU hc s hs hreg bI hI bQ τ).sectionIso X f g i hUi j B hB hg =
    LocalAdjunction.sectionIso X f j B hB U hU i hUi
      ((congrArg (fun d => d + g) hc).trans (Nat.sub_add_cancel hg)) s hs hreg bI bQ τ := by
  subst c
  simp only [eqToIso_refl, Functor.mapIso_refl, Iso.refl_trans]
  rfl

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Projective.ParameterChart
