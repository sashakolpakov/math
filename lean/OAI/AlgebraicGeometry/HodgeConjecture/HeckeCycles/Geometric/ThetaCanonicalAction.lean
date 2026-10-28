import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Geometric.ThetaBettiClass
import OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.CanonicalActiveEquiv

/-! # Theta Canonical Action -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Geometric.ThetaCanonicalAction.CM

noncomputable section

/-! The raw double-coset clauses determine the active equivalence of the
actual GeometricTheta witness. Its Betti covariance therefore uses the canonical
active inclusion required by the local spectral calculation. -/

open scoped TensorProduct

variable {E K : Type} [Field E] [NumberField E] [NumberField.IsCMField E]
  [Field K] [NumberField K] {s q : ℕ} [Fact q.Prime]
  {Index Ga MpR MpF MpA : Type} [Fintype Index] [DecidableEq Index]
  [Group Ga] [TopologicalSpace Ga] [Group MpR] [Group MpF] [Group MpA]
  (D : RepresentationTheory.Theta.Geometric.Data.ActiveHeckeThetaData E K s q Index Ga MpR MpF MpA)
  (hg : D.pel.HasIntegralModelGeometry) (hq : D.pel.IsGoodCompletelySplitPrime)
  (hIsogenyQuotient : D.pel.RealizesIsogenyQuotient) (W : ThetaWitness.CM.Witness D hg hq hIsogenyQuotient)

theorem active_eq : W.active = RepresentationTheory.Theta.Geometric.Active.Algebra.Spherical.activeHeckeEquiv q D.pel.reference.distinguished :=
  CMExtraction.CanonicalActiveEquiv.Local.activeHeckeEquiv_eq_of_raw_matching q D.pel.reference.distinguished
    W.action.basis W.realization.basis W.active W.raw

theorem covariance (h : ℂ ⊗[ℚ] RepresentationTheory.Theta.Geometric.SphericalGU.Spherical.SL3Hecke q) (φ : D.sphericalInputs) :
    D.activeH1Complex W.action (RepresentationTheory.Theta.Geometric.Active.Algebra.Spherical.activeHeckeEquiv q D.pel.reference.distinguished) h
        (ThetaBettiClass.CM.classMap D hg hq hIsogenyQuotient W φ) =
      ThetaBettiClass.CM.classMap D hg hq hIsogenyQuotient W (D.sphericalWeilComplex h φ) := by
  rw [← active_eq D hg hq hIsogenyQuotient W]
  exact ThetaBettiClass.CM.covariance D hg hq hIsogenyQuotient W h φ

theorem projector_commutes (h : ℂ ⊗[ℚ] RepresentationTheory.Theta.Geometric.SphericalGU.Spherical.SL3Hecke q) :
    (D.activeH1Complex W.action (RepresentationTheory.Theta.Geometric.Active.Algebra.Spherical.activeHeckeEquiv q D.pel.reference.distinguished) h).comp
        (D.ballH1ComplexProjector W.index) =
      (D.ballH1ComplexProjector W.index).comp
        (D.activeH1Complex W.action (RepresentationTheory.Theta.Geometric.Active.Algebra.Spherical.activeHeckeEquiv q D.pel.reference.distinguished) h) := by
  rw [← active_eq D hg hq hIsogenyQuotient W]
  exact W.projector h

end

end OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Geometric.ThetaCanonicalAction.CM
