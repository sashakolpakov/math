import OAI.RepresentationTheory.Theta.Geometric.ClosedPureDolbeaultMap
import OAI.RepresentationTheory.Theta.Geometric.AntiholomorphicClosedRepresentative

/-! # Dolbeault Equiv -/

namespace OAI.RepresentationTheory.Theta.Geometric.Projective.DolbeaultEquiv

noncomputable section

/-! On the original projective manifold the Dolbeault quotient is the
complex vector space of actual globally closed antiholomorphic one-forms. -/

set_option backward.isDefEq.respectTransparency false
open _root_.TopologicalSpace
open scoped _root_.Manifold ContDiff

theorem closedType01ToDolbeault_injective (V : AlgebraicGeometry.Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety) :
    Function.Injective (ClosedPureDolbeaultMap.closedType01ToDolbeault V.analyticModel V.analyticSpace) := by
  apply (injective_iff_map_eq_zero _).mpr
  intro a ha
  change (Submodule.Quotient.mk (ClosedPureDolbeaultMap.closedType01ToDbarForm
    V.analyticModel V.analyticSpace a) : DolbeaultQuotient.DolbeaultOneSpace V.analyticModel V.analyticSpace) = 0 at ha
  obtain ⟨s, hs⟩ := (Submodule.Quotient.mk_eq_zero _).mp ha
  have H := congrArg (GlobalDolbeaultForms.closedDbarOneGlobal (E := V.analyticModel) (M := V.analyticSpace)) hs
  change GlobalDolbeaultForms.closedDbarOneGlobal (DolbeaultBoundary.globalDbarDerivative V.analyticModel V.analyticSpace s) =
    GlobalDolbeaultForms.closedDbarOneGlobal (ClosedPureDolbeaultMap.globalDbarClosedForm V.analyticModel V.analyticSpace a.val
      (ClosedPureDolbeaultMap.pureOne_dbar_zero_of_d_zero V.analyticModel V.analyticSpace a.val a.property)) at H
  rw [ClosedPureDolbeaultMap.closedDbarOneGlobal_derivative, ClosedPureDolbeaultMap.closedDbarOneGlobal_global] at H
  have hd : Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm.d
      (Analysis.DifferentialForms.Manifold.ManifoldBidegree.PureManifoldForm.dDoublePrime (GlobalDolbeaultForms.globalZeroPureForm
        (Analysis.DifferentialForms.Manifold.Open.SmoothOpenManifoldForm.toGlobal s.val))).val = 0 := by
    rw [H]
    exact a.property
  have hz := AntiholomorphicClosedRepresentative.closed_dbar_scalar_eq_zero V (Analysis.DifferentialForms.Manifold.Open.SmoothOpenManifoldForm.toGlobal s.val) hd
  apply Subtype.ext
  exact H.symm.trans hz

theorem closedType01ToDolbeault_surjective (V : AlgebraicGeometry.Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety) :
    Function.Surjective (ClosedPureDolbeaultMap.closedType01ToDolbeault V.analyticModel V.analyticSpace) := by
  intro c
  obtain ⟨a, rfl⟩ := (LinearMap.range (DolbeaultQuotient.globalDbarLinear
    V.analyticModel V.analyticSpace)).mkQ_surjective c
  obtain ⟨f, b, hb, hab⟩ := AntiholomorphicClosedRepresentative.exists_closed_antiholomorphic_representative V
    (GlobalDolbeaultForms.closedDbarOneGlobal a) (GlobalDolbeaultForms.closedDbarOneGlobal_dbar a)
  refine ⟨⟨b, hb⟩, ?_⟩
  change Submodule.Quotient.mk (ClosedPureDolbeaultMap.closedType01ToDbarForm
      V.analyticModel V.analyticSpace ⟨b, hb⟩) = Submodule.Quotient.mk a
  symm
  apply (Submodule.Quotient.eq _).mpr
  refine ⟨(2 : ℂ) • GlobalDolbeaultForms.globalZeroFormOnTop f, ?_⟩
  rw [map_smul]
  apply Subtype.ext
  apply Subtype.ext
  have hsub (u v : AlgebraicGeometry.DivisorClass.Chern.Open.ManifoldBidegree.AntiOpenManifoldForm V.analyticModel (⊤ : Opens V.analyticSpace) 1) :
      (u - v).val = u.val - v.val := by
    calc
      (u - v).val = (u + (-1 : ℂ) • v).val := by rw [neg_one_smul, sub_eq_add_neg]
      _ = u.val + (-1 : ℂ) • v.val := rfl
      _ = u.val - v.val :=
        (congrArg (fun w => u.val + w) (neg_one_smul ℂ v.val)).trans
          (sub_eq_add_neg u.val v.val).symm
  simp only [Submodule.coe_smul, Submodule.coe_sub, hsub]
  change (2 : ℂ) • (DolbeaultBoundary.globalDbarDerivative V.analyticModel V.analyticSpace
    (GlobalDolbeaultForms.globalZeroFormOnTop f)).val.val =
      a.val.val - Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm.onOpen ⊤ b.val
  rw [GlobalDolbeaultForms.globalZeroFormOnTop_dbar]
  have H := congrArg (fun w : Analysis.DifferentialForms.Manifold.ManifoldBidegree.PureManifoldForm V.analyticModel V.analyticSpace 0 1 =>
    Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm.onOpen ⊤ w.val) hab
  change Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm.onOpen ⊤ (GlobalDolbeaultForms.closedDbarOneGlobal a).val =
    Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm.onOpen ⊤ (b.val + (2 : ℂ) •
      (Analysis.DifferentialForms.Manifold.ManifoldBidegree.PureManifoldForm.dDoublePrime (AlgebraicGeometry.ComplexMultiplication.HodgeComparison.OneFormProjection.CM.Construction.zeroFormPure f)).val) at H
  rw [GlobalDolbeaultForms.closedDbarOneGlobal_onTop, map_add, map_smul] at H
  exact (eq_sub_iff_add_eq
    (a := (2 : ℂ) • Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm.onOpen ⊤
      (Analysis.DifferentialForms.Manifold.ManifoldBidegree.PureManifoldForm.dDoublePrime (AlgebraicGeometry.ComplexMultiplication.HodgeComparison.OneFormProjection.CM.Construction.zeroFormPure f)).val)
    (b := a.val.val) (c := Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm.onOpen ⊤ b.val)).mpr
      ((add_comm _ _).trans H.symm)

def projectiveDolbeaultEquiv (V : AlgebraicGeometry.Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety) :
    ClosedPureDolbeaultMap.ClosedType01Forms V.analyticModel V.analyticSpace ≃ₗ[ℂ]
      DolbeaultQuotient.DolbeaultOneSpace V.analyticModel V.analyticSpace :=
  LinearEquiv.ofBijective (ClosedPureDolbeaultMap.closedType01ToDolbeault V.analyticModel V.analyticSpace)
    ⟨closedType01ToDolbeault_injective V, closedType01ToDolbeault_surjective V⟩

theorem projectiveDolbeaultEquiv_apply (V : AlgebraicGeometry.Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety)
    (a : ClosedPureDolbeaultMap.ClosedType01Forms V.analyticModel V.analyticSpace) :
    projectiveDolbeaultEquiv V a =
      ClosedPureDolbeaultMap.closedType01ToDolbeault V.analyticModel V.analyticSpace a := rfl

def closedType01HolomorphicH1Equiv (V : AlgebraicGeometry.Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety) :
    ClosedPureDolbeaultMap.ClosedType01Forms V.analyticModel V.analyticSpace ≃+
      CategoryTheory.Sheaf.H (AlgebraicGeometry.DivisorClass.Chern.Holomorphic.Sheaves.holomorphicFunctionSheaf V.analyticModel V.analyticSpace) 1 :=
  (projectiveDolbeaultEquiv V).toAddEquiv.trans
    (DolbeaultQuotient.dolbeaultOneClassEquiv V.analyticModel V.analyticSpace)

theorem closedType01HolomorphicH1Equiv_apply (V : AlgebraicGeometry.Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety)
    (a : ClosedPureDolbeaultMap.ClosedType01Forms V.analyticModel V.analyticSpace) :
    closedType01HolomorphicH1Equiv V a = DolbeaultBoundary.holomorphicDbarClass V.analyticModel V.analyticSpace
      (ClosedPureDolbeaultMap.closedType01ToDbarForm V.analyticModel V.analyticSpace a) := rfl

end

end OAI.RepresentationTheory.Theta.Geometric.Projective.DolbeaultEquiv
