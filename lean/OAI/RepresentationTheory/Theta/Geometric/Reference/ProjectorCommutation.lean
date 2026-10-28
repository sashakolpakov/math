import OAI.RepresentationTheory.Theta.Geometric.CorrectedTraceProjector
import OAI.RepresentationTheory.Theta.Geometric.Rational.Projector
import OAI.RepresentationTheory.Theta.Geometric.Complexify
import OAI.RepresentationTheory.Theta.Geometric.Active.Cartan

/-! # Projector Commutation -/

namespace OAI.RepresentationTheory.Theta.Geometric.Reference.ProjectorCommutation

noncomputable section

/-! Full original active Hecke commutation with the actual component
projector on both algebraic forms and complexified rational Betti H1. -/
set_option backward.isDefEq.respectTransparency false
open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped TensorProduct
namespace ActiveHeckeThetaData
variable {E K : Type} [Field E] [NumberField E] [NumberField.IsCMField E]
    [Field K] [NumberField K] {s q : ℕ} [Fact q.Prime]
    {Index Ga MpR MpF MpA : Type} [Fintype Index] [DecidableEq Index]
    [Group Ga] [TopologicalSpace Ga] [IsTopologicalGroup Ga]
    [Group MpR] [Group MpF] [Group MpA]
    (D : Data.ActiveHeckeThetaData E K s q Index Ga MpR MpF MpA)
    (hg : D.pel.HasIntegralModelGeometry) (hgood : D.pel.IsGoodCompletelySplitPrime)
    (hIsogenyQuotient : D.pel.RealizesIsogenyQuotient) (A : TateComparison.Action D.pel)
    (hA : A.IsRealization D.pel hg hgood hIsogenyQuotient)
    (hdegree : Module.finrank ℚ E = 2 * s) (hs : 0 < s)
    (hc : D.HasFiniteCoordinates) (hArithmetic : DenseRange D.rationalFinite)
    (j : Fin D.pel.componentCount) (X : AlgebraicGeometry.Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety)
    (component : X.toOver ≅ D.componentComplex j) (cover : D.domain → X.analyticSpace)
    (hcover : D.IsPeriodUniformization X cover)
    (href : ∀ x, D.totalPeriodMap j X component cover x = D.referenceModuliMap hg x)

local notation "e" => OAI.RepresentationTheory.Theta.Geometric.Active.Algebra.Spherical.activeHeckeEquiv q D.pel.reference.distinguished
local notation "active" => OAI.RepresentationTheory.Theta.Geometric.Intrinsic.Action.activeHeckeMap q D.pel.reference.distinguished e

include hA hdegree hs hc hArithmetic hcover href in
theorem _root_.OAI.RepresentationTheory.Theta.Geometric.Data.ActiveHeckeThetaData.original_active_forms_projector_commute (T : SphericalGU.Spherical.SL3Hecke q) :
    (D.heckeRationalForms hg A (active T)).comp (D.ballFormsProjector j) =
      (D.ballFormsProjector j).comp (D.heckeRationalForms hg A (active T)) := by
  choose B hB hmatch using Active.Basis.Spherical.active_basis_matching q D.pel.reference.distinguished A.basis hA.basis
  let ρ := (D.heckeRationalForms hg A).comp (active).toLinearMap
  apply Complexify.linear_commutes_of_span ρ (D.ballFormsProjector j) B (Active.Cartan.Spherical.active_raw_span q B hB) _ T
  intro a
  change (D.heckeRationalForms hg A (active (B a))).comp (D.ballFormsProjector j) =
    (D.ballFormsProjector j).comp (D.heckeRationalForms hg A (active (B a)))
  rw [hmatch]
  exact D.activeForms_projector_commute hg hgood hIsogenyQuotient A hA hdegree hs hc hArithmetic
    j X component cover hcover href a

include hA hdegree hs hc hArithmetic hcover href in
theorem _root_.OAI.RepresentationTheory.Theta.Geometric.Data.ActiveHeckeThetaData.original_active_rationalH1_projector_commute (T : SphericalGU.Spherical.SL3Hecke q) :
    (A.cohomologyAction (active T)).comp (D.ballH1Projector j) =
      (D.ballH1Projector j).comp (A.cohomologyAction (active T)) :=
  D.rationalH1_projector_of_forms hg (A.algebraAction (active T))
    (D.heckeRationalForms hg A (active T)) (A.cohomologyAction (active T))
    (D.heckeRationalForms_spec hg A (active T)) (hA.cohomology (active T)) j
    (D.original_active_forms_projector_commute hg hgood hIsogenyQuotient A hA hdegree hs hc hArithmetic
      j X component cover hcover href T)

include hA hdegree hs hc hArithmetic hcover href in
theorem _root_.OAI.RepresentationTheory.Theta.Geometric.Data.ActiveHeckeThetaData.original_active_H1_projector_commute (h : ℂ ⊗[ℚ] SphericalGU.Spherical.SL3Hecke q) :
    (D.activeH1Complex A e h).comp (D.ballH1ComplexProjector j) =
      (D.ballH1ComplexProjector j).comp (D.activeH1Complex A e h) := by
  unfold Data.ActiveHeckeThetaData.activeH1Complex Data.ActiveHeckeThetaData.ballH1ComplexProjector
  apply Complexify.complexified_baseChange_commutes
  exact D.original_active_rationalH1_projector_commute hg hgood hIsogenyQuotient A hA hdegree hs hc hArithmetic
    j X component cover hcover href

end ActiveHeckeThetaData

end

end OAI.RepresentationTheory.Theta.Geometric.Reference.ProjectorCommutation
