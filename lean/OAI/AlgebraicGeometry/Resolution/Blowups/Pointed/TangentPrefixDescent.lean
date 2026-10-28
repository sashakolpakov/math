import OAI.AlgebraicGeometry.Resolution.Blowups.Pointed.TangentPrefixCenters
import OAI.AlgebraicGeometry.Resolution.Blowups.Pointed.TangentPrefixTail
import OAI.AlgebraicGeometry.Resolution.Blowups.ControlPrefix.ComparisonCoherence

/-! # Tangent Prefix Descent -/

namespace OAI.AlgebraicGeometry.Resolution.Blowups

noncomputable section

section

/-! Whole actual programs descend from pointed tangent comparisons, preserving every center and endpoint map. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

theorem Smooth.ControlPrefix.Construction.SmoothControlPrefix.exists_etaleComparison_of_pointed_tangent
    {n : ℕ} {X Y : Scheme} {f : X ⟶ Foundations.Scheme.ProjectiveSpace.complexBase} {g : Y ⟶ Foundations.Scheme.ProjectiveSpace.complexBase}
    {J : X.IdealSheafData} {K : Y.IdealSheafData} (P : Blowups.Smooth.ControlPrefix.Construction.SmoothControlPrefix (n + 1) X f J Y g K) :
    ∀ [Smooth f] {Z : Scheme} {h : Z ⟶ Foundations.Scheme.ProjectiveSpace.complexBase} {L : Z.IdealSheafData}
      (Q : Blowups.Smooth.ControlPrefix.Construction.SmoothControlPrefix (n + 1) X f J Z h L), P.stepCount = Q.stepCount →
      P.PointedTangentComparison Q → ∃ r : Z ⟶ Y, P.EtaleComparison Q (𝟙 X) r := by
  induction P with
  | stop =>
      intro hf Z h L Q hN H
      cases Q with
      | stop => exact ⟨𝟙 _, inferInstance, Category.id_comp _, Scheme.IdealSheafData.comap_id _, rfl⟩
      | blowup => exact False.elim (Nat.noConfusion hN)
  | @blowup X hX hNX f J I hI hn hp hs hbl Y g K tail ih =>
      intro hf Z h L Q hN H
      let : Smooth f := hf
      cases Q with
      | stop => exact False.elim (Nat.noConfusion hN)
      | blowup I' hI' hn' hp' hs' hbl' rest =>
          have he := Blowups.Smooth.ControlPrefix.Construction.SmoothControlPrefix.PointedTangentComparison.head_centers_eq I hI hn hp hs hbl tail
            I' hI' hn' hp' hs' hbl' rest H
          subst I'
          let : Smooth (GlobalBlowup.Data.Construction.globalBlowupToBase I hI ≫ f) := hbl
          have htail := Blowups.Smooth.ControlPrefix.Construction.SmoothControlPrefix.PointedTangentComparison.tail I hI hn hp hs hbl tail rest H
          have hcount : tail.stepCount = rest.stepCount := Nat.add_right_cancel hN
          obtain ⟨r, hr⟩ := ih rest hcount htail
          refine ⟨r, (Blowups.Smooth.ControlPrefix.Construction.SmoothControlPrefix.etaleComparison_blowup_iff I hI hn hp hs hbl tail I hI hn hp hs hbl rest (𝟙 X) r).mpr
            ⟨inferInstance, Category.id_comp _, Scheme.IdealSheafData.comap_id _,
              Scheme.IdealSheafData.comap_id I, ?_⟩⟩
          rw [GlobalBlowup.MapComposition.Construction.globalBlowupMapTo_id]
          exact hr

end

/-! Pointed tangent comparisons determine the entire program up to its unique endpoint isomorphism. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

theorem Smooth.ControlPrefix.Construction.SmoothControlPrefix.exists_endpointIso_of_pointed_tangent
    {n : ℕ} {X Y Z : Scheme} {f : X ⟶ Foundations.Scheme.ProjectiveSpace.complexBase} [Smooth f]
    {g : Y ⟶ Foundations.Scheme.ProjectiveSpace.complexBase} {h : Z ⟶ Foundations.Scheme.ProjectiveSpace.complexBase}
    {J : X.IdealSheafData} {K : Y.IdealSheafData} {L : Z.IdealSheafData}
    (P : Blowups.Smooth.ControlPrefix.Construction.SmoothControlPrefix (n + 1) X f J Y g K) (Q : Blowups.Smooth.ControlPrefix.Construction.SmoothControlPrefix (n + 1) X f J Z h L)
    (hN : P.stepCount = Q.stepCount) (H : P.PointedTangentComparison Q) :
    ∃ e : Z ≅ Y, P.EtaleComparison Q (𝟙 X) e.hom ∧
      ∀ r : Z ⟶ Y, P.EtaleComparison Q (𝟙 X) r → r = e.hom := by
  obtain ⟨r, hr⟩ := P.exists_etaleComparison_of_pointed_tangent Q hN H
  let : IsIso r := (hr.endpoint_pullback P Q (𝟙 X) r).2.1.isIso_fst_of_isIso
  exact ⟨asIso r, hr, fun s hs => hs.endpoint_unique P Q (𝟙 X) s r hr⟩

end

end OAI.AlgebraicGeometry.Resolution.Blowups
