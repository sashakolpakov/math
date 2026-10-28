import OAI.AlgebraicGeometry.Resolution.Blowups.Pointed.TangentPrefixComparison
import OAI.AlgebraicGeometry.Resolution.Blowups.PermissibleCenterTangentDescent
import OAI.AlgebraicGeometry.Resolution.Blowups.ControlPrefix.ComparisonFactorizationTo

/-! # Tangent Prefix Centers -/

namespace OAI.AlgebraicGeometry.Resolution.Blowups

noncomputable section

open OAI.AlgebraicGeometry.Resolution.Blowups.Smooth.ControlPrefix.Construction.SmoothControlPrefix

/-! Pointed common actual prefixes force equality of the first smooth center ideals. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

theorem Smooth.ControlPrefix.Construction.SmoothControlPrefix.PointedTangentComparison.head_centers_eq
    {n : ℕ} {X Y Z : Scheme} [IsIntegral X] [IsLocallyNoetherian X]
    {f : X ⟶ Foundations.Scheme.ProjectiveSpace.complexBase} [Smooth f] {g : Y ⟶ Foundations.Scheme.ProjectiveSpace.complexBase} {h : Z ⟶ Foundations.Scheme.ProjectiveSpace.complexBase}
    {J : X.IdealSheafData} {K : Y.IdealSheafData} {L : Z.IdealSheafData}
    (I : X.IdealSheafData) (hI : I ≠ ⊥) (hn : 0 < n + 1) (hp : J ≤ I ^ (n + 1))
    (hs : Smooth (I.subschemeι ≫ f)) (hbl : Smooth (GlobalBlowup.Data.Construction.globalBlowupToBase I hI ≫ f))
    (P : Blowups.Smooth.ControlPrefix.Construction.SmoothControlPrefix (n + 1) (GlobalBlowup.Data.Construction.globalBlowup I hI) (GlobalBlowup.Data.Construction.globalBlowupToBase I hI ≫ f)
      (GlobalControlled.Ideal.Construction.globalBlowupControlledIdeal I J hI (n + 1)) Y g K)
    (I' : X.IdealSheafData) (hI' : I' ≠ ⊥) (hn' : 0 < n + 1) (hp' : J ≤ I' ^ (n + 1))
    (hs' : Smooth (I'.subschemeι ≫ f)) (hbl' : Smooth (GlobalBlowup.Data.Construction.globalBlowupToBase I' hI' ≫ f))
    (Q : Blowups.Smooth.ControlPrefix.Construction.SmoothControlPrefix (n + 1) (GlobalBlowup.Data.Construction.globalBlowup I' hI') (GlobalBlowup.Data.Construction.globalBlowupToBase I' hI' ≫ f)
      (GlobalControlled.Ideal.Construction.globalBlowupControlledIdeal I' J hI' (n + 1)) Z h L)
    (H : (blowup I hI hn hp hs hbl P).PointedTangentComparison (blowup I' hI' hn' hp' hs' hbl' Q)) :
    I = I' := by
  let : Smooth (I.subschemeι ≫ f) := hs
  let : Smooth (I'.subschemeι ≫ f) := hs'
  apply PermissibleCenterTangentDescent.Construction.permissible_centers_eq_of_pointed_tangent_comparisons f J I I' n hp hp'
  intro x hx
  obtain ⟨V, W, v, w, B, C, T, a, b, r, s, y, hy, hc, ha, hb⟩ := H x hx
  obtain ⟨hV, hNV, E, hE, hnE, hpE, hsE, hblE, rest, hT⟩ :=
    Blowups.Smooth.ControlPrefix.Construction.SmoothControlPrefix.EtaleComparison.exists_blowup I hI hn hp hs hbl P T a r ha
  let : IsIntegral V := hV
  let : IsLocallyNoetherian V := hNV
  subst T
  obtain ⟨_, _, _, hIa, _⟩ :=
    (Blowups.Smooth.ControlPrefix.Construction.SmoothControlPrefix.etaleComparison_blowup_iff I hI hn hp hs hbl P E hE hnE hpE hsE hblE rest a r).mp ha
  obtain ⟨_, _, _, hIb, _⟩ :=
    (Blowups.Smooth.ControlPrefix.Construction.SmoothControlPrefix.etaleComparison_blowup_iff I' hI' hn' hp' hs' hbl' Q E hE hnE hpE hsE hblE rest b s).mp hb
  exact ⟨V, a, b, y, hy, hc, hIa.trans hIb.symm⟩

end

end OAI.AlgebraicGeometry.Resolution.Blowups
