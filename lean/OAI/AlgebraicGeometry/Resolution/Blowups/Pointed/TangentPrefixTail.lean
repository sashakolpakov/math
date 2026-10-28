import OAI.AlgebraicGeometry.Resolution.Blowups.Pointed.TangentPrefixComparison
import OAI.AlgebraicGeometry.Resolution.Blowups.ControlPrefix.DifferentialPullback
import OAI.AlgebraicGeometry.Resolution.Blowups.ControlPrefix.ComparisonFactorizationTo

/-! # Tangent Prefix Tail -/

namespace OAI.AlgebraicGeometry.Resolution.Blowups

noncomputable section

open OAI.AlgebraicGeometry.Resolution.Blowups.Smooth.ControlPrefix.Construction.SmoothControlPrefix

/-! The pointed common-prefix comparison survives the first actual blowup once the centers agree. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

theorem Smooth.ControlPrefix.Construction.SmoothControlPrefix.PointedTangentComparison.tail
    {n : ℕ} {X Y Z : Scheme} [IsIntegral X] [IsLocallyNoetherian X]
    {f : X ⟶ Foundations.Scheme.ProjectiveSpace.complexBase} [Smooth f] {g : Y ⟶ Foundations.Scheme.ProjectiveSpace.complexBase} {h : Z ⟶ Foundations.Scheme.ProjectiveSpace.complexBase}
    {J : X.IdealSheafData} {K : Y.IdealSheafData} {L : Z.IdealSheafData}
    (I : X.IdealSheafData) (hI : I ≠ ⊥) (hn : 0 < n + 1) (hp : J ≤ I ^ (n + 1))
    (hs : Smooth (I.subschemeι ≫ f)) (hbl : Smooth (GlobalBlowup.Data.Construction.globalBlowupToBase I hI ≫ f))
    (P : Blowups.Smooth.ControlPrefix.Construction.SmoothControlPrefix (n + 1) (GlobalBlowup.Data.Construction.globalBlowup I hI) (GlobalBlowup.Data.Construction.globalBlowupToBase I hI ≫ f)
      (GlobalControlled.Ideal.Construction.globalBlowupControlledIdeal I J hI (n + 1)) Y g K)
    (Q : Blowups.Smooth.ControlPrefix.Construction.SmoothControlPrefix (n + 1) (GlobalBlowup.Data.Construction.globalBlowup I hI) (GlobalBlowup.Data.Construction.globalBlowupToBase I hI ≫ f)
      (GlobalControlled.Ideal.Construction.globalBlowupControlledIdeal I J hI (n + 1)) Z h L)
    (H : (blowup I hI hn hp hs hbl P).PointedTangentComparison (blowup I hI hn hp hs hbl Q)) :
    letI := hbl
    P.PointedTangentComparison Q := by
  let : Smooth (GlobalBlowup.Data.Construction.globalBlowupToBase I hI ≫ f) := hbl
  intro x hx
  have hpres := Scheme.IdealSheafData.support_antitone
    (Global.SequenceDifferentialPullback.Construction.globalBlowup_differential_total_le_controlled f I J hI (n + 1) n (Nat.le_succ n) hp)
  rw [Scheme.IdealSheafData.support_comap] at hpres
  obtain ⟨V, W, v, w, B, C, T, a, b, r, s, y, hy, hc, ha, hb⟩ := H (GlobalBlowup.Data.Construction.globalBlowupToBase I hI x) (hpres hx)
  obtain ⟨hV, hNV, E, hE, hnE, hpE, hsE, hblE, rest, hT⟩ :=
    Blowups.Smooth.ControlPrefix.Construction.SmoothControlPrefix.EtaleComparison.exists_blowup I hI hn hp hs hbl P T a r ha
  let : IsIntegral V := hV
  let : IsLocallyNoetherian V := hNV
  subst T
  obtain ⟨hae, haf, _, hIa, hta⟩ :=
    (Blowups.Smooth.ControlPrefix.Construction.SmoothControlPrefix.etaleComparison_blowup_iff I hI hn hp hs hbl P E hE hnE hpE hsE hblE rest a r).mp ha
  obtain ⟨hbe, hbf, _, hIb, htb⟩ :=
    (Blowups.Smooth.ControlPrefix.Construction.SmoothControlPrefix.etaleComparison_blowup_iff I hI hn hp hs hbl Q E hE hnE hpE hsE hblE rest b s).mp hb
  let : Etale a := hae
  let : Etale b := hbe
  have hnext := IdealSheaf.CongruentMaps.Construction.IdealSheafCongruent.globalBlowupMapTo f v a b haf hbf I J E hIa hIb hI hE n hp hc
  obtain ⟨z, hz, _⟩ := Scheme.exists_preimage_of_isPullback
    (GlobalBlowup.EtalePullback.Construction.globalBlowupMapTo_etale_isPullback a I E hIa hI hE) x y hy.symm
  exact ⟨GlobalBlowup.Data.Construction.globalBlowup E hE, W, GlobalBlowup.Data.Construction.globalBlowupToBase E hE ≫ v, w,
    GlobalControlled.Ideal.Construction.globalBlowupControlledIdeal E B hE (n + 1), C, rest,
    GlobalBlowup.SpecifiedMap.Construction.globalBlowupMapTo a I E hIa hI hE, GlobalBlowup.SpecifiedMap.Construction.globalBlowupMapTo b I E hIb hI hE,
    r, s, z, hz, hnext, hta, htb⟩

end

end OAI.AlgebraicGeometry.Resolution.Blowups
