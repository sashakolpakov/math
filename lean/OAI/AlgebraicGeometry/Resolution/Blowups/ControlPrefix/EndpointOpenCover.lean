import OAI.AlgebraicGeometry.Resolution.Blowups.ControlPrefix.ComparisonOpen

/-! # Endpoint Open Cover -/

namespace OAI.AlgebraicGeometry.Resolution.Blowups

noncomputable section

/-! The actual endpoints of open restrictions cover a program endpoint and detect its terminal order. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

theorem Smooth.ControlPrefix.Construction.SmoothControlPrefix.EtaleComparison.endpoint_isOpenImmersion
    {b : ℕ} {X Y V W : Scheme} {f : X ⟶ Foundations.Scheme.ProjectiveSpace.complexBase} {g : Y ⟶ Foundations.Scheme.ProjectiveSpace.complexBase}
    {h : V ⟶ Foundations.Scheme.ProjectiveSpace.complexBase} {k : W ⟶ Foundations.Scheme.ProjectiveSpace.complexBase}
    {J : X.IdealSheafData} {K : Y.IdealSheafData} {L : V.IdealSheafData} {M : W.IdealSheafData}
    (P : Blowups.Smooth.ControlPrefix.Construction.SmoothControlPrefix b X f J Y g K) (Q : Blowups.Smooth.ControlPrefix.Construction.SmoothControlPrefix b V h L W k M)
    (q : V ⟶ X) [IsOpenImmersion q] (r : W ⟶ Y) (hc : P.EtaleComparison Q q r) :
    IsOpenImmersion r :=
  MorphismProperty.of_isPullback (P := @IsOpenImmersion) (hc.endpoint_pullback P Q q r).2.1.flip inferInstance

def Smooth.ControlPrefix.Construction.SmoothControlPrefix.endpointOpenCover
    {b : ℕ} {X Y : Scheme} {f : X ⟶ Foundations.Scheme.ProjectiveSpace.complexBase} {g : Y ⟶ Foundations.Scheme.ProjectiveSpace.complexBase}
    {J : X.IdealSheafData} {K : Y.IdealSheafData} (P : Blowups.Smooth.ControlPrefix.Construction.SmoothControlPrefix b X f J Y g K)
    {ι : Type} (U : ι → Scheme) (j : ∀ i, U i ⟶ X) [∀ i, IsOpenImmersion (j i)]
    (hcover : ∀ x : X, ∃ i y, j i y = x)
    (h : ∀ i, U i ⟶ Foundations.Scheme.ProjectiveSpace.complexBase) (L : ∀ i, (U i).IdealSheafData)
    (V : ι → Scheme) (k : ∀ i, V i ⟶ Foundations.Scheme.ProjectiveSpace.complexBase) (M : ∀ i, (V i).IdealSheafData)
    (Q : ∀ i, Blowups.Smooth.ControlPrefix.Construction.SmoothControlPrefix b (U i) (h i) (L i) (V i) (k i) (M i))
    (r : ∀ i, V i ⟶ Y) (hc : ∀ i, P.EtaleComparison (Q i) (j i) (r i)) : Y.OpenCover := by
  let : ∀ i, IsOpenImmersion (r i) := fun i => (hc i).endpoint_isOpenImmersion P (Q i) (j i) (r i)
  apply Scheme.Cover.mkOfCovers ι V r
  intro x
  obtain ⟨i, y, hy⟩ := hcover (P.toBase x)
  obtain ⟨z, hz, _⟩ := Scheme.exists_preimage_of_isPullback
    ((hc i).endpoint_pullback P (Q i) (j i) (r i)).2.1 x y hy.symm
  exact ⟨i, z, hz⟩

theorem Smooth.ControlPrefix.Construction.SmoothControlPrefix.terminal_order_of_open_comparisons
    {b : ℕ} {X Y : Scheme} {f : X ⟶ Foundations.Scheme.ProjectiveSpace.complexBase} {g : Y ⟶ Foundations.Scheme.ProjectiveSpace.complexBase}
    {J : X.IdealSheafData} {K : Y.IdealSheafData} (P : Blowups.Smooth.ControlPrefix.Construction.SmoothControlPrefix b X f J Y g K)
    {ι : Type} (U : ι → Scheme) (j : ∀ i, U i ⟶ X) [∀ i, IsOpenImmersion (j i)]
    (hcover : ∀ x : X, ∃ i y, j i y = x)
    (h : ∀ i, U i ⟶ Foundations.Scheme.ProjectiveSpace.complexBase) (L : ∀ i, (U i).IdealSheafData)
    (V : ι → Scheme) (k : ∀ i, V i ⟶ Foundations.Scheme.ProjectiveSpace.complexBase) (M : ∀ i, (V i).IdealSheafData)
    (Q : ∀ i, Blowups.Smooth.ControlPrefix.Construction.SmoothControlPrefix b (U i) (h i) (L i) (V i) (k i) (M i))
    (r : ∀ i, V i ⟶ Y) (hc : ∀ i, P.EtaleComparison (Q i) (j i) (r i)) (n : ℕ) :
    letI : Smooth g := P.endpoint_smooth
    letI : ∀ i, Smooth (k i) := fun i => (Q i).endpoint_smooth
    (∀ i, Blowups.Smooth.DifferentialIdealSheaf.Construction.smoothDifferentialIdealSheaf (k i) (M i) n = ⊤) →
      Blowups.Smooth.DifferentialIdealSheaf.Construction.smoothDifferentialIdealSheaf g K n = ⊤ := by
  let : Smooth g := P.endpoint_smooth
  let : ∀ i, Smooth (k i) := fun i => (Q i).endpoint_smooth
  intro ht
  apply DifferentialUnitGluing.Construction.idealSheaf_eq_top_of_openCover _ (P.endpointOpenCover U j hcover h L V k M Q r hc)
  intro i
  change ι at i
  change (Blowups.Smooth.DifferentialIdealSheaf.Construction.smoothDifferentialIdealSheaf g K n).comap (r i) = ⊤
  obtain ⟨hr, _, hK⟩ := (hc i).endpoint_pullback P (Q i) (j i) (r i)
  let : Etale (r i) := hr
  have he := Blowups.Smooth.GlobalCoefficientEtalePullback.Construction.smoothDifferentialIdealSheaf_comap_etale g K n (r i)
  rw [hK] at he
  exact he.trans ((DifferentialUnitGluing.Construction.smoothDifferentialIdealSheaf_structure_congr (r i ≫ g) (k i)
    ((hc i).endpoint_structure P (Q i) (j i) (r i)) (M i) n).trans (ht i))

end

end OAI.AlgebraicGeometry.Resolution.Blowups
