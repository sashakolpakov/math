import OAI.AlgebraicGeometry.Resolution.Blowups.Surface.ControlFinitePrograms
import OAI.AlgebraicGeometry.Resolution.Blowups.Surface.ResidualProgramEtalePullback

/-! # Control Program System -/

namespace OAI

noncomputable section

namespace AlgebraicGeometry.Resolution.Blowups.Uniform.ControlProgramSystem.Construction

/-! A dimension-indexed interface records actual finite programs, common schedules, and full étale naturality. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

structure UniformControlProgramSystem (d : ℕ) where
  Schedule : (b : ℕ) → (β : Type) → [Fintype β] → [DecidableEq β] → Type 1
  incidenceTrace : ∀ {b : ℕ} {β : Type} [Fintype β] [DecidableEq β], Schedule b β → Boundary.IncidenceTrace.Construction.BoundaryIncidenceTrace β
  Program : ∀ {b : ℕ} {β : Type} [Fintype β] [DecidableEq β], Schedule b β →
    ∀ {X Y : Scheme} (f : X ⟶ Foundations.Scheme.ProjectiveSpace.complexBase) [Smooth f] (J : X.IdealSheafData) (_D : β → X.IdealSheafData)
      {g : Y ⟶ Foundations.Scheme.ProjectiveSpace.complexBase} {K : Y.IdealSheafData}, Blowups.Smooth.ControlPrefix.Construction.SmoothControlPrefix b X f J Y g K → Prop
  hasTrace : ∀ {b : ℕ} {β : Type} [Fintype β] [DecidableEq β] {s : Schedule b β}
    {X Y : Scheme} {f : X ⟶ Foundations.Scheme.ProjectiveSpace.complexBase} [Smooth f] {J : X.IdealSheafData} {D : β → X.IdealSheafData}
    {g : Y ⟶ Foundations.Scheme.ProjectiveSpace.complexBase} {K : Y.IdealSheafData} {P : Blowups.Smooth.ControlPrefix.Construction.SmoothControlPrefix b X f J Y g K},
    Program s f J D P → P.HasIncidenceTrace β D (incidenceTrace s)
  terminal : ∀ {b : ℕ}, 0 < b → ∀ {β : Type} [Fintype β] [DecidableEq β] {s : Schedule b β}
    {X Y : Scheme} {f : X ⟶ Foundations.Scheme.ProjectiveSpace.complexBase} [Smooth f] {J : X.IdealSheafData} {D : β → X.IdealSheafData}
    {g : Y ⟶ Foundations.Scheme.ProjectiveSpace.complexBase} {K : Y.IdealSheafData} {P : Blowups.Smooth.ControlPrefix.Construction.SmoothControlPrefix b X f J Y g K},
    Program s f J D P → letI : Smooth g := P.endpoint_smooth; Blowups.Smooth.DifferentialIdealSheaf.Construction.smoothDifferentialIdealSheaf g K (b - 1) = ⊤
  finitePrograms : ∀ (b : ℕ), 0 < b → ∀ {β ι : Type} [Fintype β] [DecidableEq β] [Fintype ι]
    (X : ι → Scheme) [∀ i, IsIntegral (X i)] [∀ i, IsLocallyNoetherian (X i)] [∀ i, CompactSpace (X i)]
    (f : ∀ i, X i ⟶ Foundations.Scheme.ProjectiveSpace.complexBase) [∀ i, Smooth (f i)] (J : ∀ i, (X i).IdealSheafData),
    (∀ i, J i ≠ ⊥) → (∀ i, topologicalKrullDim (X i) ≤ d) →
    ∀ (D : ∀ i, β → (X i).IdealSheafData), (∀ i, Global.MonomialBoundaryAtlas.Construction.GlobalMonomialBoundaryAtlas (f i) (D i) [Finset.univ]) →
    ∃ s : Schedule b β, ∀ i, ∃ (Y : Scheme) (g : Y ⟶ Foundations.Scheme.ProjectiveSpace.complexBase) (K : Y.IdealSheafData)
      (P : Blowups.Smooth.ControlPrefix.Construction.SmoothControlPrefix b (X i) (f i) (J i) Y g K), Program s (f i) (J i) (D i) P
  comparison : ∀ {b : ℕ} {β : Type} [Fintype β] [DecidableEq β] {s : Schedule b β}
    {X Y V W : Scheme} {f : X ⟶ Foundations.Scheme.ProjectiveSpace.complexBase} [Smooth f] {h : V ⟶ Foundations.Scheme.ProjectiveSpace.complexBase} [Smooth h]
    {J : X.IdealSheafData} {L : V.IdealSheafData} {D : β → X.IdealSheafData} {E : β → V.IdealSheafData}
    {g : Y ⟶ Foundations.Scheme.ProjectiveSpace.complexBase} {k : W ⟶ Foundations.Scheme.ProjectiveSpace.complexBase} {K : Y.IdealSheafData} {M : W.IdealSheafData}
    {P : Blowups.Smooth.ControlPrefix.Construction.SmoothControlPrefix b X f J Y g K} {Q : Blowups.Smooth.ControlPrefix.Construction.SmoothControlPrefix b V h L W k M},
    Program s f J D P → Program s h L E Q → ∀ (q : V ⟶ X) [Etale q],
    q ≫ f = h → J.comap q = L → (∀ l, (D l).comap q = E l) →
      ∃ r : W ⟶ Y, P.EtaleComparison Q q r
  pullback : ∀ {b : ℕ}, 0 < b → ∀ {β : Type} [Fintype β] [DecidableEq β] {s : Schedule b β}
    {X Y : Scheme} {f : X ⟶ Foundations.Scheme.ProjectiveSpace.complexBase} [Smooth f] {J : X.IdealSheafData} {D : β → X.IdealSheafData}
    {g : Y ⟶ Foundations.Scheme.ProjectiveSpace.complexBase} {K : Y.IdealSheafData} {P : Blowups.Smooth.ControlPrefix.Construction.SmoothControlPrefix b X f J Y g K},
    Program s f J D P → ∀ (V : Scheme) [IsIntegral V] [IsLocallyNoetherian V] [CompactSpace V],
    topologicalKrullDim V ≤ d → ∀ (h : V ⟶ Foundations.Scheme.ProjectiveSpace.complexBase) [Smooth h] (L : V.IdealSheafData), L ≠ ⊥ →
    ∀ (E : β → V.IdealSheafData) (q : V ⟶ X) [Etale q], q ≫ f = h → J.comap q = L →
    (∀ l, (D l).comap q = E l) →
    ∃ (W : Scheme) (k : W ⟶ Foundations.Scheme.ProjectiveSpace.complexBase) (M : W.IdealSheafData)
      (Q : Blowups.Smooth.ControlPrefix.Construction.SmoothControlPrefix b V h L W k M) (r : W ⟶ Y), Program s h L E Q ∧ P.EtaleComparison Q q r

end AlgebraicGeometry.Resolution.Blowups.Uniform.ControlProgramSystem.Construction

namespace AlgebraicGeometry.Resolution.Blowups.Uniform.ControlProgramSystem.Construction.UniformControlProgramSystem

/-! A uniform program system constructs common actual programs on every matching integral étale chart in its dimension. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

theorem exists_common_etale_pullback {d : ℕ} (C : UniformControlProgramSystem d)
    {b : ℕ} (hb : 0 < b) {β : Type} [Fintype β] [DecidableEq β] {s : C.Schedule b β}
    {X Y X' Y' : Scheme} {f : X ⟶ Foundations.Scheme.ProjectiveSpace.complexBase} [Smooth f] {g : Y ⟶ Foundations.Scheme.ProjectiveSpace.complexBase}
    {f' : X' ⟶ Foundations.Scheme.ProjectiveSpace.complexBase} [Smooth f'] {g' : Y' ⟶ Foundations.Scheme.ProjectiveSpace.complexBase}
    {J : X.IdealSheafData} {K : Y.IdealSheafData} {D : β → X.IdealSheafData}
    {J' : X'.IdealSheafData} {K' : Y'.IdealSheafData} {D' : β → X'.IdealSheafData}
    {P : Blowups.Smooth.ControlPrefix.Construction.SmoothControlPrefix b X f J Y g K} {P' : Blowups.Smooth.ControlPrefix.Construction.SmoothControlPrefix b X' f' J' Y' g' K'}
    (H : C.Program s f J D P) (H' : C.Program s f' J' D' P')
    (V : Scheme) [IsIntegral V] [IsLocallyNoetherian V] [CompactSpace V] (hdV : topologicalKrullDim V ≤ d)
    (h : V ⟶ Foundations.Scheme.ProjectiveSpace.complexBase) [Smooth h] (L : V.IdealSheafData) (hL : L ≠ ⊥)
    (E : β → V.IdealSheafData) (q : V ⟶ X) [Etale q] (q' : V ⟶ X') [Etale q']
    (hf : q ≫ f = h) (hf' : q' ≫ f' = h) (hJ : J.comap q = L) (hJ' : J'.comap q' = L)
    (hD : ∀ l, (D l).comap q = E l) (hD' : ∀ l, (D' l).comap q' = E l) :
    ∃ (W : Scheme) (k : W ⟶ Foundations.Scheme.ProjectiveSpace.complexBase) (M : W.IdealSheafData)
      (Q : Blowups.Smooth.ControlPrefix.Construction.SmoothControlPrefix b V h L W k M) (r : W ⟶ Y) (r' : W ⟶ Y'),
      C.Program s h L E Q ∧ P.EtaleComparison Q q r ∧ P'.EtaleComparison Q q' r' := by
  obtain ⟨W, k, M, Q, r, T, hc⟩ := C.pullback hb H V hdV h L hL E q hf hJ hD
  obtain ⟨W', k', M', Q', r', T', hc'⟩ := C.pullback hb H' V hdV h L hL E q' hf' hJ' hD'
  obtain ⟨t, ht⟩ := C.comparison T' T (𝟙 V) (Category.id_comp h)
    (Scheme.IdealSheafData.comap_id L) (fun l => Scheme.IdealSheafData.comap_id (E l))
  refine ⟨W, k, M, Q, r, t ≫ r', T, hc, ?_⟩
  simpa only [Category.id_comp] using hc'.comp P' Q' q' r' Q (𝟙 V) t ht

end AlgebraicGeometry.Resolution.Blowups.Uniform.ControlProgramSystem.Construction.UniformControlProgramSystem

end

end OAI
