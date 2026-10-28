import OAI.AlgebraicGeometry.Resolution.Blowups.ProtectedPatternChart
import OAI.AlgebraicGeometry.Resolution.Blowups.ControlPrefix.ComparisonHeads
import OAI.AlgebraicGeometry.Resolution.Blowups.ControlPrefix.ComparisonFactorizationTo
import OAI.AlgebraicGeometry.Resolution.Blowups.IdealSheaf.UnitOpenRestriction
import OAI.AlgebraicGeometry.Resolution.Blowups.Global.PrincipalBlowup
import OAI.AlgebraicGeometry.Resolution.Blowups.GlobalBlowup.OpenComparison

/-! # Protected Pattern Chart Step -/

namespace OAI.AlgebraicGeometry.Resolution.Blowups.ProtectedPatternChartStep.Construction

noncomputable section

section

/-! An empty protected center transports each pointed common-program chart to the actual next blowup. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

theorem exists_protected_pattern_chart_after_empty_step
    {X Y : Scheme} [IsIntegral X] [IsLocallyNoetherian X]
    {f : X ⟶ Foundations.Scheme.ProjectiveSpace.complexBase} {g : Y ⟶ Foundations.Scheme.ProjectiveSpace.complexBase} {J : X.IdealSheafData} {K : Y.IdealSheafData}
    (C : X.IdealSheafData) (hC : C ≠ ⊥) (hp : J ≤ C ^ 1)
    (hs : Smooth (C.subschemeι ≫ f)) (hbl : Smooth (GlobalBlowup.Data.Construction.globalBlowupToBase C hC ≫ f))
    (tail : Blowups.Smooth.ControlPrefix.Construction.SmoothControlPrefix 1 (GlobalBlowup.Data.Construction.globalBlowup C hC) (GlobalBlowup.Data.Construction.globalBlowupToBase C hC ≫ f)
      (GlobalControlled.Ideal.Construction.globalBlowupControlledIdeal C J hC 1) Y g K)
    (O : X.Opens) (hO : C.comap O.ι = ⊤)
    (A : ProtectedPatternChart.Construction.ProtectedPatternProgramChart (.blowup C hC (by decide) hp hs hbl tail) O) :
    ∃ (B : ProtectedPatternChart.Construction.ProtectedPatternProgramChart tail (GlobalBlowup.Data.Construction.globalBlowupToBase C hC ⁻¹ᵁ O)) (p : B.source ⟶ A.source),
      IsPullback B.map p (GlobalBlowup.Data.Construction.globalBlowupToBase C hC) A.map := by
  rcases A with ⟨S, s, L, hS, hNS, point, hpoint, j, hj, hcontained,
    V, v, M, hV, hNV, W, w, N, Q, hpattern, T, t, B, R, r, hglobal, a, u, hmodel⟩
  let : IsIntegral S := hS
  let : IsLocallyNoetherian S := hNS
  let : IsIntegral V := hV
  let : IsLocallyNoetherian V := hNV
  let : IsOpenImmersion j := hj
  have hCj : C.comap j = ⊤ := IdealSheaf.UnitOpenRestriction.Construction.idealSheaf_comap_top_of_image_in_open C O hO j hcontained
  obtain ⟨_, _, E, hE, hbE, hpE, hsE, hblE, rest, heR⟩ :=
    hglobal.exists_blowup C hC (by decide) hp hs hbl tail R j r
  subst R
  obtain ⟨_, _, _, hCE, htail⟩ := (Blowups.Smooth.ControlPrefix.Construction.SmoothControlPrefix.etaleComparison_blowup_iff
    C hC (by decide) hp hs hbl tail E hE hbE hpE hsE hblE rest j r).mp hglobal
  have hEtop : E = ⊤ := hCE.symm.trans hCj
  cases Q with
  | stop => exact False.elim hmodel
  | blowup D hD hbD hpD hsD hblD modelTail =>
      obtain ⟨ha, _, hML, hDE, hmodelTail⟩ := (Blowups.Smooth.ControlPrefix.Construction.SmoothControlPrefix.etaleComparison_blowup_iff
        D hD hbD hpD hsD hblD modelTail E hE hbE hpE hsE hblE rest a u).mp hmodel
      let : Etale a := ha
      have hempty : D = ⊤ ∧ modelTail.UnitUntilWhole := by
        rcases hpattern with hwhole | hempty
        · have hLtop : L = ⊤ := hML.symm.trans
            ((congrArg (fun I => I.comap a) hwhole.symm).trans (hDE.trans hEtop))
          rw [hLtop, Scheme.IdealSheafData.support_top] at hpoint
          exact False.elim hpoint
        · exact hempty
      rcases hempty with ⟨rfl, hmodelPattern⟩
      subst hEtop
      let π := GlobalBlowup.Data.Construction.globalBlowupToBase C hC
      let πS := GlobalBlowup.Data.Construction.globalBlowupToBase (⊤ : S.IdealSheafData) hE
      let : IsIso πS := Global.PrincipalBlowup.Construction.globalBlowupToBase_isIso_of_locallyPrincipal ⊤ hE (Locally.PrincipalIdealSheaf.Construction.LocallyPrincipalIdealSheaf.top S)
      let j' := GlobalBlowup.SpecifiedMap.Construction.globalBlowupMapTo j C ⊤ hCE hC hE
      let a' := GlobalBlowup.SpecifiedMap.Construction.globalBlowupMapTo a ⊤ ⊤ hDE hD hE
      have hj' : IsOpenImmersion j' := GlobalBlowup.OpenComparison.Construction.globalBlowupMapTo_isOpenImmersion j C ⊤ hCE hC hE
      have hcontained' (z : GlobalBlowup.Data.Construction.globalBlowup (⊤ : S.IdealSheafData) hE) : j' z ∈ π ⁻¹ᵁ O := by
        have he := congrArg (fun q => q z) (GlobalBlowup.SpecifiedMap.Construction.globalBlowupMapTo_over j C ⊤ hCE hC hE)
        change π (j' z) = j (πS z) at he
        change π (j' z) ∈ O
        rw [he]
        exact hcontained (πS z)
      have hpoint' : inv πS point ∈ (GlobalControlled.Ideal.Construction.globalBlowupControlledIdeal ⊤ L hE 1).support := by
        rw [Global.PrincipalBlowup.Construction.globalBlowupControlledIdeal_top_center, Scheme.IdealSheafData.support_comap]
        change πS (inv πS point) ∈ L.support
        have he := congrArg (fun q => q point) (IsIso.inv_hom_id πS)
        change πS (inv πS point) = point at he
        rwa [he]
      let A' : ProtectedPatternChart.Construction.ProtectedPatternProgramChart tail (π ⁻¹ᵁ O) :=
        { source := GlobalBlowup.Data.Construction.globalBlowup (⊤ : S.IdealSheafData) hE
          structureMap := πS ≫ s
          ideal := GlobalControlled.Ideal.Construction.globalBlowupControlledIdeal ⊤ L hE 1
          integral := inferInstance
          noetherian := inferInstance
          point := inv πS point
          pointMarked := hpoint'
          map := j'
          isOpenImmersion := hj'
          contained := hcontained'
          modelSource := GlobalBlowup.Data.Construction.globalBlowup (⊤ : V.IdealSheafData) hD
          modelStructureMap := GlobalBlowup.Data.Construction.globalBlowupToBase ⊤ hD ≫ v
          modelIdeal := GlobalControlled.Ideal.Construction.globalBlowupControlledIdeal ⊤ M hD 1
          modelIntegral := inferInstance
          modelNoetherian := inferInstance
          modelEndpoint := W
          modelEndStructureMap := w
          modelEndIdeal := N
          modelProgram := modelTail
          modelPattern := hmodelPattern
          commonEndpoint := T
          commonEndStructureMap := t
          commonEndIdeal := B
          commonProgram := rest
          globalEndMap := r
          globalComparison := htail
          modelMap := a'
          modelEndMap := u
          modelComparison := hmodelTail }
      exact ⟨A', πS, GlobalBlowup.EtalePullback.Construction.globalBlowupMapTo_etale_isPullback j C ⊤ hCE hC hE⟩

end

/-! The entire protected pattern cover survives an actual blowup whose center is empty on the protected open. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

theorem exists_protected_pattern_cover_after_empty_step
    {X Y : Scheme} [IsIntegral X] [IsLocallyNoetherian X]
    {f : X ⟶ Foundations.Scheme.ProjectiveSpace.complexBase} {g : Y ⟶ Foundations.Scheme.ProjectiveSpace.complexBase} {J : X.IdealSheafData} {K : Y.IdealSheafData}
    (C : X.IdealSheafData) (hC : C ≠ ⊥) (hp : J ≤ C ^ 1)
    (hs : Smooth (C.subschemeι ≫ f)) (hbl : Smooth (GlobalBlowup.Data.Construction.globalBlowupToBase C hC ≫ f))
    (tail : Blowups.Smooth.ControlPrefix.Construction.SmoothControlPrefix 1 (GlobalBlowup.Data.Construction.globalBlowup C hC) (GlobalBlowup.Data.Construction.globalBlowupToBase C hC ≫ f)
      (GlobalControlled.Ideal.Construction.globalBlowupControlledIdeal C J hC 1) Y g K)
    (O : X.Opens) (hO : C.comap O.ι = ⊤)
    (A : ProtectedPatternChart.Construction.ProtectedPatternProgramCover (.blowup C hC (by decide) hp hs hbl tail) O) :
    Nonempty (ProtectedPatternChart.Construction.ProtectedPatternProgramCover tail (GlobalBlowup.Data.Construction.globalBlowupToBase C hC ⁻¹ᵁ O)) := by
  choose B p hpb using fun i => exists_protected_pattern_chart_after_empty_step C hC hp hs hbl tail O hO (A.chart i)
  refine ⟨{ indices := A.indices, chart := B, cover := ?_ }⟩
  intro x hx hxO
  have hsupport := Scheme.IdealSheafData.support_antitone
    (GlobalControlled.Ideal.Construction.totalIdeal_le_controlledIdealSheaf C J 1 (GlobalBlowup.Data.Construction.globalBlowupToBase C hC))
  rw [Scheme.IdealSheafData.support_comap] at hsupport
  have hxJ : GlobalBlowup.Data.Construction.globalBlowupToBase C hC x ∈ J.support := hsupport hx
  obtain ⟨i, y, hy⟩ := A.cover (GlobalBlowup.Data.Construction.globalBlowupToBase C hC x) hxJ hxO
  obtain ⟨z, hz, _⟩ := Scheme.exists_preimage_of_isPullback (hpb i) x y hy.symm
  exact ⟨i, z, hz⟩

end

end OAI.AlgebraicGeometry.Resolution.Blowups.ProtectedPatternChartStep.Construction
