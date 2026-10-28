import OAI.AlgebraicGeometry.Resolution.Blowups.ControlPrefix.CanonicalBoundaryAtlas
import OAI.AlgebraicGeometry.Resolution.Blowups.ControlPrefix.CanonicalBoundaryNaturality

/-! # Fixed Labels -/

namespace OAI.AlgebraicGeometry.Resolution.Blowups

noncomputable section

/-! A common prescribed length gives literally the same endpoint label type on all comparison charts. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

def ControlPrefix.FixedLabels.Construction.relabelBoundaryByLength {n N : ℕ} {β T : Type} (h : n = N)
    (u : ControlPrefix.CanonicalLabels.Construction.iteratedBoundaryLabels n β → T) : ControlPrefix.CanonicalLabels.Construction.iteratedBoundaryLabels N β → T := h ▸ u

theorem ControlPrefix.FixedLabels.Construction.relabelBoundaryByLength_map {n N : ℕ} {β T U : Type} (h : n = N)
    (u : ControlPrefix.CanonicalLabels.Construction.iteratedBoundaryLabels n β → T) (φ : T → U) :
    (fun l => φ (ControlPrefix.FixedLabels.Construction.relabelBoundaryByLength h u l)) = ControlPrefix.FixedLabels.Construction.relabelBoundaryByLength h (fun l => φ (u l)) := by
  cases h
  rfl

theorem ControlPrefix.FixedLabels.Construction.relabelBoundaryByLength_eq_of_heq {n m N : ℕ} {β T : Type}
    (hn : n = N) (hm : m = N) (u : ControlPrefix.CanonicalLabels.Construction.iteratedBoundaryLabels n β → T)
    (v : ControlPrefix.CanonicalLabels.Construction.iteratedBoundaryLabels m β → T) (h : HEq u v) :
    ControlPrefix.FixedLabels.Construction.relabelBoundaryByLength hn u = ControlPrefix.FixedLabels.Construction.relabelBoundaryByLength hm v := by
  cases hn
  cases hm
  exact eq_of_heq h

variable {b : ℕ} {X Y : Scheme} {f : X ⟶ Foundations.Scheme.ProjectiveSpace.complexBase} {g : Y ⟶ Foundations.Scheme.ProjectiveSpace.complexBase}
    {J : X.IdealSheafData} {K : Y.IdealSheafData}

def Smooth.ControlPrefix.Construction.SmoothControlPrefix.boundaryAtLength (P : Smooth.ControlPrefix.Construction.SmoothControlPrefix b X f J Y g K) {β : Type}
    (D : β → X.IdealSheafData) (N : ℕ) (hN : P.stepCount = N) : ControlPrefix.CanonicalLabels.Construction.iteratedBoundaryLabels N β → Y.IdealSheafData :=
  ControlPrefix.FixedLabels.Construction.relabelBoundaryByLength hN (P.canonicalBoundary D)

theorem Smooth.ControlPrefix.Construction.SmoothControlPrefix.boundaryAtLength_atlas (P : Smooth.ControlPrefix.Construction.SmoothControlPrefix b X f J Y g K) {β : Type} [Fintype β]
    (D : β → X.IdealSheafData) (hP : P.boundaryCompatible β D) (N : ℕ) (hN : P.stepCount = N) :
    Nonempty (Global.MonomialBoundaryAtlas.Construction.GlobalMonomialBoundaryAtlas g (P.boundaryAtLength D N hN) [Finset.univ]) := by
  subst N
  exact P.canonicalBoundary_atlas D hP

theorem Smooth.ControlPrefix.Construction.SmoothControlPrefix.exists_fixed_length_logarithmic_bound
    [IsIntegral X] [IsLocallyNoetherian X] [CompactSpace X]
    (P : Smooth.ControlPrefix.Construction.SmoothControlPrefix b X f J Y g K) {β : Type} [Fintype β]
    (D : β → X.IdealSheafData) (hP : P.boundaryCompatible β D)
    (G : GlobalBoundary.ModelAtlas.Construction.GlobalBoundaryModelAtlas f D) (hG : G.logarithmicIdeal J b = ⊤) (N : ℕ) (hN : P.stepCount = N) :
    ∃ G' : GlobalBoundary.ModelAtlas.Construction.GlobalBoundaryModelAtlas g (P.boundaryAtLength D N hN), G'.logarithmicIdeal K b = ⊤ := by
  subst N
  exact P.exists_canonical_logarithmic_bound D hP G hG

theorem Smooth.ControlPrefix.Construction.SmoothControlPrefix.exists_endpoint_fixed_boundary_pullback
    (P : Smooth.ControlPrefix.Construction.SmoothControlPrefix b X f J Y g K) (centers : List X.IdealSheafData) (hP : P.followsCenters centers)
    {V W : Scheme} {h : V ⟶ Foundations.Scheme.ProjectiveSpace.complexBase} {k : W ⟶ Foundations.Scheme.ProjectiveSpace.complexBase}
    {L : V.IdealSheafData} {M : W.IdealSheafData}
    (Q : Smooth.ControlPrefix.Construction.SmoothControlPrefix b V h L W k M) (q : V ⟶ X) [Etale q]
    (hstructure : q ≫ f = h) (hJ : J.comap q = L)
    (hQ : Q.followsCenters (centers.map (fun C => C.comap q)))
    (β : Type) (D : β → X.IdealSheafData) (E : β → V.IdealSheafData) (hD : ∀ l, (D l).comap q = E l)
    (N : ℕ) (hPN : P.stepCount = N) (hQN : Q.stepCount = N) :
    ∃ r : W ⟶ Y, Etale r ∧ IsPullback r Q.toBase P.toBase q ∧ K.comap r = M ∧
      (fun l => (P.boundaryAtLength D N hPN l).comap r) = Q.boundaryAtLength E N hQN := by
  obtain ⟨r, hr, hpb, hK, hboundary⟩ := P.exists_endpoint_canonical_boundary_pullback
    centers hP Q q hstructure hJ hQ β D E hD
  refine ⟨r, hr, hpb, hK, ?_⟩
  unfold Smooth.ControlPrefix.Construction.SmoothControlPrefix.boundaryAtLength
  exact (ControlPrefix.FixedLabels.Construction.relabelBoundaryByLength_map hPN (P.canonicalBoundary D) (fun I : Y.IdealSheafData => I.comap r)).trans
    (ControlPrefix.FixedLabels.Construction.relabelBoundaryByLength_eq_of_heq hPN hQN _ _ hboundary)

end

end OAI.AlgebraicGeometry.Resolution.Blowups
