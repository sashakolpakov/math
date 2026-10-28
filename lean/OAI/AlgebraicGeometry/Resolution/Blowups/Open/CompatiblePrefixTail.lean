import OAI.AlgebraicGeometry.Resolution.Blowups.Open.ComparisonAt
import OAI.AlgebraicGeometry.Resolution.Blowups.GlobalBlowup.MapComposition
import OAI.AlgebraicGeometry.Resolution.Blowups.GlobalBlowup.OpenComparison

/-! # Compatible Prefix Tail -/

namespace OAI.AlgebraicGeometry.Resolution.Blowups

noncomputable section

open OAI.AlgebraicGeometry.Resolution.Blowups.Smooth.ControlPrefix.Construction.SmoothControlPrefix

/-! Pointed overlap compatibility survives the actual blowup of a glued center. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

theorem Smooth.ControlPrefix.Construction.SmoothControlPrefix.OpenCompatible.tail
    {b : ℕ} {X U V Y Z : Scheme} [IsIntegral X] [IsLocallyNoetherian X]
    [IsIntegral U] [IsLocallyNoetherian U] [IsIntegral V] [IsLocallyNoetherian V]
    {f : U ⟶ Foundations.Scheme.ProjectiveSpace.complexBase} {g : V ⟶ Foundations.Scheme.ProjectiveSpace.complexBase} {h : Y ⟶ Foundations.Scheme.ProjectiveSpace.complexBase} {k : Z ⟶ Foundations.Scheme.ProjectiveSpace.complexBase}
    {J : U.IdealSheafData} {L : V.IdealSheafData} {M : Y.IdealSheafData} {N : Z.IdealSheafData}
    (I : U.IdealSheafData) (hI : I ≠ ⊥) (hb : 0 < b) (hp : J ≤ I ^ b)
    (hs : Smooth (I.subschemeι ≫ f)) (hbl : Smooth (GlobalBlowup.Data.Construction.globalBlowupToBase I hI ≫ f))
    (P : Blowups.Smooth.ControlPrefix.Construction.SmoothControlPrefix b (GlobalBlowup.Data.Construction.globalBlowup I hI) (GlobalBlowup.Data.Construction.globalBlowupToBase I hI ≫ f)
      (GlobalControlled.Ideal.Construction.globalBlowupControlledIdeal I J hI b) Y h M)
    (C : V.IdealSheafData) (hC : C ≠ ⊥) (hc : 0 < b) (hpC : L ≤ C ^ b)
    (hsC : Smooth (C.subschemeι ≫ g)) (hblC : Smooth (GlobalBlowup.Data.Construction.globalBlowupToBase C hC ≫ g))
    (Q : Blowups.Smooth.ControlPrefix.Construction.SmoothControlPrefix b (GlobalBlowup.Data.Construction.globalBlowup C hC) (GlobalBlowup.Data.Construction.globalBlowupToBase C hC ≫ g)
      (GlobalControlled.Ideal.Construction.globalBlowupControlledIdeal C L hC b) Z k N)
    (j : U ⟶ X) (l : V ⟶ X) [IsOpenImmersion j] [IsOpenImmersion l]
    (D : X.IdealSheafData) (hD : D ≠ ⊥) (hj : D.comap j = I) (hl : D.comap l = C)
    (H : (blowup I hI hb hp hs hbl P).OpenCompatible (blowup C hC hc hpC hsC hblC Q) j l) :
    P.OpenCompatible Q (GlobalBlowup.SpecifiedMap.Construction.globalBlowupMapTo j D I hj hD hI) (GlobalBlowup.SpecifiedMap.Construction.globalBlowupMapTo l D C hl hD hC) := by
  intro x y hxy
  have hbase : j (GlobalBlowup.Data.Construction.globalBlowupToBase I hI x) = l (GlobalBlowup.Data.Construction.globalBlowupToBase C hC y) := by
    have he := congrArg (GlobalBlowup.Data.Construction.globalBlowupToBase D hD) hxy
    change (GlobalBlowup.SpecifiedMap.Construction.globalBlowupMapTo j D I hj hD hI ≫ GlobalBlowup.Data.Construction.globalBlowupToBase D hD) x =
      (GlobalBlowup.SpecifiedMap.Construction.globalBlowupMapTo l D C hl hD hC ≫ GlobalBlowup.Data.Construction.globalBlowupToBase D hD) y at he
    simpa only [GlobalBlowup.SpecifiedMap.Construction.globalBlowupMapTo_over, Scheme.Hom.comp_apply] using he
  obtain ⟨S, T, s, t, A, B, R, a, c, r, v, z, hx, hy, hcomm, ha, hc'⟩ :=
    H (GlobalBlowup.Data.Construction.globalBlowupToBase I hI x) (GlobalBlowup.Data.Construction.globalBlowupToBase C hC y) hbase
  obtain ⟨hS, hNS, E, hE, hbE, hpE, hsE, hblE, rest, hR⟩ :=
    Blowups.Smooth.ControlPrefix.Construction.SmoothControlPrefix.EtaleComparison.exists_blowup I hI hb hp hs hbl P R a r ha
  let : IsIntegral S := hS
  let : IsLocallyNoetherian S := hNS
  subst R
  obtain ⟨hae, _, _, he, hta⟩ :=
    (Blowups.Smooth.ControlPrefix.Construction.SmoothControlPrefix.etaleComparison_blowup_iff I hI hb hp hs hbl P E hE hbE hpE hsE hblE rest a r).mp ha
  obtain ⟨hce, _, _, he', htc⟩ :=
    (Blowups.Smooth.ControlPrefix.Construction.SmoothControlPrefix.etaleComparison_blowup_iff C hC hc hpC hsC hblC Q E hE hbE hpE hsE hblE rest c v).mp hc'
  let : Etale a := hae
  let : Etale c := hce
  have hcomp : GlobalBlowup.SpecifiedMap.Construction.globalBlowupMapTo a I E he hI hE ≫ GlobalBlowup.SpecifiedMap.Construction.globalBlowupMapTo j D I hj hD hI =
      GlobalBlowup.SpecifiedMap.Construction.globalBlowupMapTo c C E he' hC hE ≫ GlobalBlowup.SpecifiedMap.Construction.globalBlowupMapTo l D C hl hD hC := by
    have hja : D.comap (a ≫ j) = E := by rw [Scheme.IdealSheafData.comap_comp, hj, he]
    have hlc : D.comap (c ≫ l) = E := by rw [Scheme.IdealSheafData.comap_comp, hl, he']
    rw [GlobalBlowup.MapComposition.Construction.globalBlowupMapTo_comp j a D I E hj he hja hD hI hE,
      GlobalBlowup.MapComposition.Construction.globalBlowupMapTo_comp l c D C E hl he' hlc hD hC hE]
    congr 1
  obtain ⟨w, hw, _⟩ := Scheme.exists_preimage_of_isPullback
    (GlobalBlowup.EtalePullback.Construction.globalBlowupMapTo_etale_isPullback a I E he hI hE) x z hx.symm
  have hwy : GlobalBlowup.SpecifiedMap.Construction.globalBlowupMapTo c C E he' hC hE w = y := by
    apply (GlobalBlowup.SpecifiedMap.Construction.globalBlowupMapTo l D C hl hD hC).isOpenEmbedding.injective
    have hew := congrArg (fun q : GlobalBlowup.Data.Construction.globalBlowup E hE ⟶ GlobalBlowup.Data.Construction.globalBlowup D hD => q w) hcomp
    change GlobalBlowup.SpecifiedMap.Construction.globalBlowupMapTo j D I hj hD hI (GlobalBlowup.SpecifiedMap.Construction.globalBlowupMapTo a I E he hI hE w) =
      GlobalBlowup.SpecifiedMap.Construction.globalBlowupMapTo l D C hl hD hC (GlobalBlowup.SpecifiedMap.Construction.globalBlowupMapTo c C E he' hC hE w) at hew
    rw [hw] at hew
    exact hew.symm.trans hxy
  exact ⟨GlobalBlowup.Data.Construction.globalBlowup E hE, T, GlobalBlowup.Data.Construction.globalBlowupToBase E hE ≫ s, t,
    GlobalControlled.Ideal.Construction.globalBlowupControlledIdeal E A hE b, B, rest,
    GlobalBlowup.SpecifiedMap.Construction.globalBlowupMapTo a I E he hI hE, GlobalBlowup.SpecifiedMap.Construction.globalBlowupMapTo c C E he' hC hE,
    r, v, w, hw, hwy, hcomp, hta, htc⟩

end

end OAI.AlgebraicGeometry.Resolution.Blowups
