import OAI.AlgebraicGeometry.Resolution.Blowups.Open.ComparisonAt
import OAI.AlgebraicGeometry.Resolution.Blowups.TerminalSourcePrefixComparison
import OAI.AlgebraicGeometry.Resolution.Blowups.Global.ResidualNeighborhood

/-! # Compatibility Order Complement -/

namespace OAI.AlgebraicGeometry.Resolution.Blowups

noncomputable section

/-! Open compatibility only needs construction on the order support; its complement is automatic. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

theorem Smooth.ControlPrefix.Construction.SmoothControlPrefix.openComparisonAt_of_not_mem_order
    {n : ℕ} {X U V Y Z : Scheme} [IsIntegral U] [IsLocallyNoetherian U]
    (f : X ⟶ Foundations.Scheme.ProjectiveSpace.complexBase) [Smooth f] (J : X.IdealSheafData)
    (j : U ⟶ X) (l : V ⟶ X) [IsOpenImmersion j] [IsOpenImmersion l]
    {g : Y ⟶ Foundations.Scheme.ProjectiveSpace.complexBase} {h : Z ⟶ Foundations.Scheme.ProjectiveSpace.complexBase} {K : Y.IdealSheafData} {L : Z.IdealSheafData}
    (P : Blowups.Smooth.ControlPrefix.Construction.SmoothControlPrefix (n + 1) U (j ≫ f) (J.comap j) Y g K)
    (Q : Blowups.Smooth.ControlPrefix.Construction.SmoothControlPrefix (n + 1) V (l ≫ f) (J.comap l) Z h L)
    (hN : P.stepCount = Q.stepCount) (x : U) (y : V) (hxy : j x = l y)
    (hx : j x ∉ (Blowups.Smooth.DifferentialIdealSheaf.Construction.smoothDifferentialIdealSheaf f J n).support) : P.OpenComparisonAt Q j l x y := by
  obtain ⟨z, hzx, hzy⟩ := Scheme.exists_preimage_of_isPullback (IsPullback.of_hasPullback j l) x y hxy
  let : Nonempty ↥(pullback j l : Scheme) := ⟨z⟩
  let : IsIntegral (pullback j l) := isIntegral_of_isOpenImmersion (pullback.fst j l)
  let : IsLocallyNoetherian (pullback j l) := LocallyOfFiniteType.isLocallyNoetherian (pullback.fst j l)
  let q : pullback j l ⟶ X := pullback.fst j l ≫ j
  let v := q ≫ f
  let B := J.comap q
  let O : Scheme.Opens (pullback j l) := (Blowups.Smooth.DifferentialIdealSheaf.Construction.smoothDifferentialIdealSheaf v B n).support.compl
  have hz : z ∈ O := by
    change z ∉ (Blowups.Smooth.DifferentialIdealSheaf.Construction.smoothDifferentialIdealSheaf (q ≫ f) (J.comap q) n).support
    rw [← Blowups.Smooth.GlobalCoefficientEtalePullback.Construction.smoothDifferentialIdealSheaf_comap_etale, Scheme.IdealSheafData.support_comap]
    change j (pullback.fst j l z) ∉ (Blowups.Smooth.DifferentialIdealSheaf.Construction.smoothDifferentialIdealSheaf f J n).support
    rwa [hzx]
  let : Nonempty O.toScheme := ⟨⟨z, hz⟩⟩
  let : IsIntegral O.toScheme := isIntegral_of_isOpenImmersion O.ι
  let : IsLocallyNoetherian O.toScheme := LocallyOfFiniteType.isLocallyNoetherian O.ι
  let a := O.ι ≫ pullback.fst j l
  let b := O.ι ≫ pullback.snd j l
  have hcomm : a ≫ j = b ≫ l := by
    dsimp only [a, b]
    rw [Category.assoc, Category.assoc, pullback.condition]
  have haf : a ≫ (j ≫ f) = O.ι ≫ v := by simp only [a, v, q, Category.assoc]
  have hbf : b ≫ (l ≫ f) = O.ι ≫ v := by rw [← Category.assoc, ← hcomm, Category.assoc, haf]
  have haJ : (J.comap j).comap a = B.comap O.ι := by
    simp only [a, B, q, ← Scheme.IdealSheafData.comap_comp, Category.assoc]
  have hbJ : (J.comap l).comap b = B.comap O.ι := by
    rw [← Scheme.IdealSheafData.comap_comp, ← hcomm, Scheme.IdealSheafData.comap_comp, haJ]
  have ht : Blowups.Smooth.DifferentialIdealSheaf.Construction.smoothDifferentialIdealSheaf (O.ι ≫ v) (B.comap O.ι) n = ⊤ := by
    rw [← Blowups.Smooth.DifferentialSheafRestriction.Construction.smoothDifferentialIdealSheaf_comap_open]
    exact Global.ResidualNeighborhood.Construction.idealSheaf_comap_supportComplement_eq_top _
  obtain ⟨W, w, M, R, r, s, hr, hs⟩ := P.exists_common_program_of_terminal_source Q hN
    (O.ι ≫ v) (B.comap O.ι) ht a b haf hbf haJ hbJ
  exact ⟨O.toScheme, W, O.ι ≫ v, w, B.comap O.ι, M, R, a, b, r, s, ⟨z, hz⟩,
    hzx, hzy, hcomm, hr, hs⟩

theorem Smooth.ControlPrefix.Construction.SmoothControlPrefix.openCompatible_of_order_comparisons
    {n : ℕ} {X U V Y Z : Scheme} [IsIntegral U] [IsLocallyNoetherian U]
    (f : X ⟶ Foundations.Scheme.ProjectiveSpace.complexBase) [Smooth f] (J : X.IdealSheafData)
    (j : U ⟶ X) (l : V ⟶ X) [IsOpenImmersion j] [IsOpenImmersion l]
    {g : Y ⟶ Foundations.Scheme.ProjectiveSpace.complexBase} {h : Z ⟶ Foundations.Scheme.ProjectiveSpace.complexBase} {K : Y.IdealSheafData} {L : Z.IdealSheafData}
    (P : Blowups.Smooth.ControlPrefix.Construction.SmoothControlPrefix (n + 1) U (j ≫ f) (J.comap j) Y g K)
    (Q : Blowups.Smooth.ControlPrefix.Construction.SmoothControlPrefix (n + 1) V (l ≫ f) (J.comap l) Z h L)
    (hN : P.stepCount = Q.stepCount)
    (H : ∀ (x : U) (y : V), j x = l y → j x ∈ (Blowups.Smooth.DifferentialIdealSheaf.Construction.smoothDifferentialIdealSheaf f J n).support →
      P.OpenComparisonAt Q j l x y) : P.OpenCompatible Q j l := by
  intro x y hxy
  by_cases hx : j x ∈ (Blowups.Smooth.DifferentialIdealSheaf.Construction.smoothDifferentialIdealSheaf f J n).support
  · exact H x y hxy hx
  · exact Blowups.Smooth.ControlPrefix.Construction.SmoothControlPrefix.openComparisonAt_of_not_mem_order f J j l P Q hN x y hxy hx

end

end OAI.AlgebraicGeometry.Resolution.Blowups
