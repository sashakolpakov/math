import OAI.AlgebraicGeometry.Resolution.Blowups.IncidenceTraceExponents
import OAI.AlgebraicGeometry.Resolution.Blowups.IncidenceTraceComposition
import OAI.AlgebraicGeometry.Resolution.Blowups.ControlPrefix.IdealTransforms
import OAI.AlgebraicGeometry.Resolution.Blowups.Uniform.WholePrefixResidualTransport

/-! # Trace Residual Transport -/

namespace OAI.AlgebraicGeometry.Resolution.Blowups

noncomputable section

/-! A common incidence trace gives one exact residual exponent vector for every geometric realization. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

theorem Smooth.ControlPrefix.Construction.SmoothControlPrefix.HasIncidenceTrace.residual_transform
    {m : ℕ} {X Y : Scheme} {f : X ⟶ Foundations.Scheme.ProjectiveSpace.complexBase} {g : Y ⟶ Foundations.Scheme.ProjectiveSpace.complexBase}
    {J : X.IdealSheafData} {K : Y.IdealSheafData} (P : Smooth.ControlPrefix.Construction.SmoothControlPrefix m X f J Y g K)
    (b : ℕ) (hbm : b ≤ m) :
    ∀ {β : Type} [Fintype β] (D : β → X.IdealSheafData) (T : Boundary.IncidenceTrace.Construction.BoundaryIncidenceTrace β)
      (hP : P.HasIncidenceTrace β D T) (a : β → ℕ),
      P.transformIdeal (Global.MixedBoundary.Construction.boundaryMonomialSheaf D a * J) b =
        Global.MixedBoundary.Construction.boundaryMonomialSheaf (P.boundaryAtLength D T.length (hP.stepCount P D T)) (T.residualExponents a m b) * K := by
  induction P with
  | stop =>
      intro β _ D T hP a
      cases T with
      | stop => rfl
      | step => exact False.elim hP
  | @blowup X hX hNX f J I hI hm hp hs hbl Y g K tail ih =>
      intro β _ D T hP a
      cases T with
      | stop => exact False.elim hP
      | step F rest =>
          obtain ⟨A, hF⟩ := hP.1
          let D' := CanonicalBoundaryTransform.Construction.globalBlowupCanonicalBoundary I hI D
          let a₁ := ResidualBoundaryMonomialUpdate.Construction.residualBoundaryMonomialExponents F a m b
          have hM : Global.MixedBoundary.Construction.boundaryMonomialSheaf D a ≤ I ^ (b - m) := by
            rw [Nat.sub_eq_zero_of_le hbm, pow_zero, Scheme.IdealSheafData.one_eq_top]
            exact le_top
          have hfirst : GlobalControlled.Ideal.Construction.globalBlowupControlledIdeal I (Global.MixedBoundary.Construction.boundaryMonomialSheaf D a * J) hI b =
              Global.MixedBoundary.Construction.boundaryMonomialSheaf D' a₁ * GlobalControlled.Ideal.Construction.globalBlowupControlledIdeal I J hI m :=
            A.residual_product_uniform_incidence F (fun i _ => hF i) J hI a m b hM hp
          have htail : tail.HasIncidenceTrace (Option β) D' rest := hP.2
          have he : (Smooth.ControlPrefix.Construction.SmoothControlPrefix.blowup I hI hm hp hs hbl tail).boundaryAtLength D (rest.length + 1)
              (hP.stepCount _ D (.step F rest)) =
              tail.boundaryAtLength D' rest.length (htail.stepCount tail D' rest) :=
            IncidenceTraceComposition.Construction.relabelBoundaryByLength_succ (hP.stepCount _ D (.step F rest)) (tail.canonicalBoundary D')
          change tail.transformIdeal (GlobalControlled.Ideal.Construction.globalBlowupControlledIdeal I (Global.MixedBoundary.Construction.boundaryMonomialSheaf D a * J) hI b) b =
            Global.MixedBoundary.Construction.boundaryMonomialSheaf ((Smooth.ControlPrefix.Construction.SmoothControlPrefix.blowup I hI hm hp hs hbl tail).boundaryAtLength D (rest.length + 1)
              (hP.stepCount _ D (.step F rest))) (rest.residualExponents a₁ m b) * K
          rw [hfirst, he]
          exact ih D' rest htail a₁

theorem Smooth.ControlPrefix.Construction.SmoothControlPrefix.HasIncidenceTrace.exists_lower_control_prefix
    {m : ℕ} {X Y : Scheme} {f : X ⟶ Foundations.Scheme.ProjectiveSpace.complexBase} {g : Y ⟶ Foundations.Scheme.ProjectiveSpace.complexBase}
    {J : X.IdealSheafData} {K : Y.IdealSheafData} (P : Smooth.ControlPrefix.Construction.SmoothControlPrefix m X f J Y g K)
    (b : ℕ) (hb : 0 < b) (hbm : b ≤ m) {β : Type} [Fintype β]
    (D : β → X.IdealSheafData) (T : Boundary.IncidenceTrace.Construction.BoundaryIncidenceTrace β) (hP : P.HasIncidenceTrace β D T) (a : β → ℕ) :
    ∃ Q : Smooth.ControlPrefix.Construction.SmoothControlPrefix b X f (Global.MixedBoundary.Construction.boundaryMonomialSheaf D a * J) Y g
        (Global.MixedBoundary.Construction.boundaryMonomialSheaf (P.boundaryAtLength D T.length (hP.stepCount P D T)) (T.residualExponents a m b) * K),
      Smooth.ControlPrefix.Construction.SmoothControlPrefix.SameBlowups m b P Q := by
  obtain ⟨a', Q, hQ⟩ := P.exists_lower_control_same_blowups b hb hbm β D
    (hP.uniformBoundaryCompatible P D T) a
  have htransform := hP.residual_transform P b hbm D T a
  rw [← htransform, hQ.transformIdeal]
  exact ⟨Q, hQ⟩

end

end OAI.AlgebraicGeometry.Resolution.Blowups
