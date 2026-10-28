import OAI.AlgebraicGeometry.Resolution.Blowups.TraceCompanionTransport
import OAI.AlgebraicGeometry.Resolution.Blowups.ControlPrefix.OrdinaryBound

/-! # Trace Companion Residual Drop -/

namespace OAI.AlgebraicGeometry.Resolution.Blowups

noncomputable section

/-! Exact common companion exponents retain the residual bound and give the terminal residual-order drop. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

theorem Smooth.ControlPrefix.Construction.SmoothControlPrefix.HasIncidenceTrace.companion_residual_drop
    {m b : ℕ} (hm : 0 < m) (hmb : m < b)
    {X Y : Scheme} {f : X ⟶ Foundations.Scheme.ProjectiveSpace.complexBase} [Smooth f] {g : Y ⟶ Foundations.Scheme.ProjectiveSpace.complexBase}
    {C : X.IdealSheafData} {K : Y.IdealSheafData}
    (P : Blowups.Smooth.ControlPrefix.Construction.SmoothControlPrefix (m * (b - m)) X f C Y g K)
    {β : Type} [Fintype β] (D : β → X.IdealSheafData) (T : Boundary.IncidenceTrace.Construction.BoundaryIncidenceTrace β)
    (hP : P.HasIncidenceTrace β D T) (J : X.IdealSheafData) (a : β → ℕ)
    (hC : C = Global.CompanionIdeal.Construction.globalCompanionIdeal J (Global.MixedBoundary.Construction.boundaryMonomialSheaf D a) m b)
    (hbound : Blowups.Smooth.DifferentialIdealSheaf.Construction.smoothDifferentialIdealSheaf f J m = ⊤) :
    letI : Smooth g := P.endpoint_smooth
    Blowups.Smooth.DifferentialIdealSheaf.Construction.smoothDifferentialIdealSheaf g K (m * (b - m) - 1) = ⊤ →
      Blowups.Smooth.DifferentialIdealSheaf.Construction.smoothDifferentialIdealSheaf g (P.transformIdeal J m) m = ⊤ ∧
      Blowups.Smooth.DifferentialIdealSheaf.Construction.smoothDifferentialIdealSheaf g
          (Global.MixedBoundary.Construction.boundaryMonomialSheaf (P.boundaryAtLength D T.length (hP.stepCount P D T)) (T.companionExponents a m b) *
            P.transformIdeal J m) (b - 1) ⊔
        Blowups.Smooth.DifferentialIdealSheaf.Construction.smoothDifferentialIdealSheaf g (P.transformIdeal J m) (m - 1) = ⊤ := by
  let : Smooth g := P.endpoint_smooth
  intro ht
  obtain ⟨R, Q, hR, hQ⟩ := hP.exists_companion_prefix hm hmb P D T J a hC
  have hbound' := R.endpoint_differential_bound hbound
  have hcomp := (hP.companion_transforms hm hmb P D T J a hC).1
  refine ⟨hbound', ?_⟩
  apply Global.CompanionIdeal.Construction.globalCompanionIdeal_terminal_residual_drop g (P.transformIdeal J m)
    (Global.MixedBoundary.Construction.boundaryMonomialSheaf (P.boundaryAtLength D T.length (hP.stepCount P D T)) (T.companionExponents a m b)) m b hm hmb hbound'
  rw [← hcomp]
  exact ht

end

end OAI.AlgebraicGeometry.Resolution.Blowups
