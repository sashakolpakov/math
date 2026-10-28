import OAI.AlgebraicGeometry.Resolution.Blowups.IncidenceTraceExponents
import OAI.AlgebraicGeometry.Resolution.Blowups.IncidenceTraceComposition
import OAI.AlgebraicGeometry.Resolution.Blowups.ControlPrefix.IdealTransforms
import OAI.AlgebraicGeometry.Resolution.Blowups.Uniform.WholePrefixCompanionTransport

/-! # Trace Companion Transport -/

namespace OAI.AlgebraicGeometry.Resolution.Blowups

noncomputable section

/-! Companion programs with a common trace produce one exact endpoint monomial exponent vector. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

theorem Smooth.ControlPrefix.Construction.SmoothControlPrefix.HasIncidenceTrace.companion_transforms
    {m b : ℕ} (hm : 0 < m) (hmb : m < b)
    {X Y : Scheme} {f : X ⟶ Foundations.Scheme.ProjectiveSpace.complexBase} {g : Y ⟶ Foundations.Scheme.ProjectiveSpace.complexBase}
    {C : X.IdealSheafData} {K : Y.IdealSheafData}
    (P : Blowups.Smooth.ControlPrefix.Construction.SmoothControlPrefix (m * (b - m)) X f C Y g K) :
    ∀ [Smooth f] {β : Type} [Fintype β] (D : β → X.IdealSheafData) (T : Boundary.IncidenceTrace.Construction.BoundaryIncidenceTrace β)
      (hP : P.HasIncidenceTrace β D T) (J : X.IdealSheafData) (a : β → ℕ),
      C = Global.CompanionIdeal.Construction.globalCompanionIdeal J (Global.MixedBoundary.Construction.boundaryMonomialSheaf D a) m b →
      K = Global.CompanionIdeal.Construction.globalCompanionIdeal (P.transformIdeal J m)
          (Global.MixedBoundary.Construction.boundaryMonomialSheaf (P.boundaryAtLength D T.length (hP.stepCount P D T)) (T.companionExponents a m b)) m b ∧
        P.transformIdeal (Global.MixedBoundary.Construction.boundaryMonomialSheaf D a * J) b =
          Global.MixedBoundary.Construction.boundaryMonomialSheaf (P.boundaryAtLength D T.length (hP.stepCount P D T)) (T.companionExponents a m b) *
            P.transformIdeal J m := by
  induction P with
  | stop =>
      intro _ β _ D T hP J a hC
      cases T with
      | stop => exact ⟨hC, rfl⟩
      | step => exact False.elim hP
  | @blowup X hX hNX f C I hI hc hp hs hbl Y g K tail ih =>
      intro hf β _ D T hP J a hC
      let : Smooth f := hf
      let : Smooth (I.subschemeι ≫ f) := hs
      let : Smooth (GlobalBlowup.Data.Construction.globalBlowupToBase I hI ≫ f) := hbl
      cases T with
      | stop => exact False.elim hP
      | step F rest =>
          obtain ⟨A, hF⟩ := hP.1
          let D' := CanonicalBoundaryTransform.Construction.globalBlowupCanonicalBoundary I hI D
          let a₁ := Boundary.MonomialSchedule.Construction.boundaryScheduleExponents a (b - m) F
          let J₁ := GlobalControlled.Ideal.Construction.globalBlowupControlledIdeal I J hI m
          obtain ⟨hJ, hM, _⟩ := Global.CompanionIdeal.Construction.globalCompanionIdeal_smooth_center_permissible
            f I J (Global.MixedBoundary.Construction.boundaryMonomialSheaf D a) m b hm hmb (hC ▸ hp)
          have hmon : GlobalControlled.Ideal.Construction.globalBlowupControlledIdeal I (Global.MixedBoundary.Construction.boundaryMonomialSheaf D a) hI (b - m) =
              Global.MixedBoundary.Construction.boundaryMonomialSheaf D' a₁ :=
            A.monomial_transform_uniform_incidence F (fun i _ => hF i) hI a (b - m) hM
          have hcomp : GlobalControlled.Ideal.Construction.globalBlowupControlledIdeal I C hI (m * (b - m)) =
              Global.CompanionIdeal.Construction.globalCompanionIdeal J₁ (Global.MixedBoundary.Construction.boundaryMonomialSheaf D' a₁) m b := by
            rw [hC, Global.CompanionTransform.Construction.globalBlowup_companion_transform I J (Global.MixedBoundary.Construction.boundaryMonomialSheaf D a) hI m b hJ hM, hmon]
          have hproduct : GlobalControlled.Ideal.Construction.globalBlowupControlledIdeal I (Global.MixedBoundary.Construction.boundaryMonomialSheaf D a * J) hI b =
              Global.MixedBoundary.Construction.boundaryMonomialSheaf D' a₁ * J₁ := by
            rw [Global.CompanionTransform.Construction.globalBlowup_companion_product_transform I (Global.MixedBoundary.Construction.boundaryMonomialSheaf D a) J hI m b (Nat.le_of_lt hmb) hM hJ, hmon]
          have htail : tail.HasIncidenceTrace (Option β) D' rest := hP.2
          have he : (Blowups.Smooth.ControlPrefix.Construction.SmoothControlPrefix.blowup I hI hc hp hs hbl tail).boundaryAtLength D (rest.length + 1)
              (hP.stepCount _ D (.step F rest)) = tail.boundaryAtLength D' rest.length (htail.stepCount tail D' rest) :=
            IncidenceTraceComposition.Construction.relabelBoundaryByLength_succ (hP.stepCount _ D (.step F rest)) (tail.canonicalBoundary D')
          change K = Global.CompanionIdeal.Construction.globalCompanionIdeal (tail.transformIdeal J₁ m)
              (Global.MixedBoundary.Construction.boundaryMonomialSheaf ((Blowups.Smooth.ControlPrefix.Construction.SmoothControlPrefix.blowup I hI hc hp hs hbl tail).boundaryAtLength D (rest.length + 1)
                (hP.stepCount _ D (.step F rest))) (rest.companionExponents a₁ m b)) m b ∧
            tail.transformIdeal (GlobalControlled.Ideal.Construction.globalBlowupControlledIdeal I (Global.MixedBoundary.Construction.boundaryMonomialSheaf D a * J) hI b) b =
              Global.MixedBoundary.Construction.boundaryMonomialSheaf ((Blowups.Smooth.ControlPrefix.Construction.SmoothControlPrefix.blowup I hI hc hp hs hbl tail).boundaryAtLength D (rest.length + 1)
                (hP.stepCount _ D (.step F rest))) (rest.companionExponents a₁ m b) * tail.transformIdeal J₁ m
          rw [he, hproduct]
          exact ih D' rest htail J₁ a₁ hcomp

theorem Smooth.ControlPrefix.Construction.SmoothControlPrefix.HasIncidenceTrace.exists_companion_prefix
    {m b : ℕ} (hm : 0 < m) (hmb : m < b)
    {X Y : Scheme} {f : X ⟶ Foundations.Scheme.ProjectiveSpace.complexBase} [Smooth f] {g : Y ⟶ Foundations.Scheme.ProjectiveSpace.complexBase}
    {C : X.IdealSheafData} {K : Y.IdealSheafData}
    (P : Blowups.Smooth.ControlPrefix.Construction.SmoothControlPrefix (m * (b - m)) X f C Y g K)
    {β : Type} [Fintype β] (D : β → X.IdealSheafData) (T : Boundary.IncidenceTrace.Construction.BoundaryIncidenceTrace β)
    (hP : P.HasIncidenceTrace β D T) (J : X.IdealSheafData) (a : β → ℕ)
    (hC : C = Global.CompanionIdeal.Construction.globalCompanionIdeal J (Global.MixedBoundary.Construction.boundaryMonomialSheaf D a) m b) :
    ∃ (R : Blowups.Smooth.ControlPrefix.Construction.SmoothControlPrefix m X f J Y g (P.transformIdeal J m))
      (Q : Blowups.Smooth.ControlPrefix.Construction.SmoothControlPrefix b X f (Global.MixedBoundary.Construction.boundaryMonomialSheaf D a * J) Y g
        (Global.MixedBoundary.Construction.boundaryMonomialSheaf (P.boundaryAtLength D T.length (hP.stepCount P D T)) (T.companionExponents a m b) *
          P.transformIdeal J m)),
      Blowups.Smooth.ControlPrefix.Construction.SmoothControlPrefix.SameBlowups (m * (b - m)) m P R ∧ Blowups.Smooth.ControlPrefix.Construction.SmoothControlPrefix.SameBlowups (m * (b - m)) b P Q := by
  obtain ⟨J', a', R, Q, hR, hQ, hK⟩ := P.exists_companion_same_blowups hm hmb β D
    (hP.uniformBoundaryCompatible P D T) J a hC
  have hres := hR.transformIdeal
  subst J'
  have htransforms := hP.companion_transforms hm hmb P D T J a hC
  have hnext : ∃ S : Blowups.Smooth.ControlPrefix.Construction.SmoothControlPrefix b X f (Global.MixedBoundary.Construction.boundaryMonomialSheaf D a * J) Y g
      (Global.MixedBoundary.Construction.boundaryMonomialSheaf (P.boundaryAtLength D T.length (hP.stepCount P D T)) (T.companionExponents a m b) *
        P.transformIdeal J m), Blowups.Smooth.ControlPrefix.Construction.SmoothControlPrefix.SameBlowups (m * (b - m)) b P S := by
    rw [← htransforms.2, hQ.transformIdeal]
    exact ⟨Q, hQ⟩
  obtain ⟨S, hS⟩ := hnext
  exact ⟨R, S, hR, hS⟩

end

end OAI.AlgebraicGeometry.Resolution.Blowups
