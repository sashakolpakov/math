import OAI.AlgebraicGeometry.HilbertScheme.Presentations.Noetherian.StalkFactorization
import Mathlib.AlgebraicGeometry.IdealSheaf.Functorial
import Mathlib.Topology.Separation.Basic

/-! # Closed Stalk Detection -/

namespace OAI.AlgebraicGeometry.HilbertScheme.Presentations.Ideal.ClosedStalkDetection

noncomputable section

/-! On a quasi-compact locally Noetherian scheme, an ideal sheaf is zero
if its pullback to every closed-point local spectrum is zero. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace

universe u
variable {X : Scheme.{u}} [IsLocallyNoetherian X]

theorem ideal_eq_bot_of_localSpectra (I : X.IdealSheafData)
    (h : ∀ x : X, I.comap (X.fromSpecStalk x) = ⊥) : I = ⊥ := by
  obtain ⟨g, hg, _⟩ := Noetherian.StalkFactorization.lift_of_fromSpecStalk (𝟙 X) I.subschemeι (fun x => by
    have hx : I.subschemeι.ker ≤ (X.fromSpecStalk x).ker := by
      rw [I.ker_subschemeι]
      rw [← Scheme.IdealSheafData.map_bot (X.fromSpecStalk x),
        Scheme.IdealSheafData.le_map_iff_comap_le, h x]
    refine ⟨IsClosedImmersion.lift I.subschemeι (X.fromSpecStalk x) hx, ?_⟩
    simpa only [Category.comp_id] using IsClosedImmersion.lift_fac _ _ hx)
  have hi : I ≤ (𝟙 X : X ⟶ X).ker := by
    have hi' := I.ker_subschemeι.symm.le.trans (Scheme.Hom.le_ker_comp g I.subschemeι)
    rwa [hg] at hi'
  exact bot_unique (hi.trans_eq (𝟙 X : X ⟶ X).ker_eq_bot_of_isIso)

theorem ideal_eq_bot_of_closed_localSpectra [CompactSpace X] (I : X.IdealSheafData)
    (h : ∀ x : X, IsClosed ({x} : Set X) → I.comap (X.fromSpecStalk x) = ⊥) : I = ⊥ := by
  apply ideal_eq_bot_of_localSpectra I
  intro x
  obtain ⟨y, hy, hyc⟩ := isClosed_closure.exists_closed_singleton
    (Set.singleton_nonempty x).closure
  have hxy : x ⤳ y := specializes_iff_mem_closure.mpr hy
  rw [← Scheme.SpecMap_stalkSpecializes_fromSpecStalk hxy,
    Scheme.IdealSheafData.comap_comp, h y hyc, Scheme.IdealSheafData.comap_bot]

end

end OAI.AlgebraicGeometry.HilbertScheme.Presentations.Ideal.ClosedStalkDetection
