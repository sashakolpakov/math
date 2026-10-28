import OAI.AlgebraicGeometry.Comparison.Betti.TotalComplexZeroCoordinates
import OAI.AlgebraicGeometry.SheafCohomology.Cech.UpNatHorizontalEdge
import Mathlib.Algebra.Homology.QuasiIso

/-! # Total Complex Degree Zero -/

namespace OAI.AlgebraicGeometry.Comparison.Betti.TotalComplexDegreeZero

noncomputable section

/-! The augmented-row total-complex comparison is a quasi-isomorphism also in degree zero. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.HomologicalComplex _root_.HomologicalComplex₂

variable {C : Type*} [Category* C] [Abelian C]
  (K : HomologicalComplex₂ C (.up ℕ) (.up ℕ)) [K.HasTotal (.up ℕ)]
  (A : CochainComplex C ℕ) (e : ∀ q, A.X q ⟶ (K.X q).X 0)
  (he : ∀ q q', (ComplexShape.up ℕ).Rel q q' → e q ≫ (K.d q q').f 0 = A.d q q' ≫ e q')
  (w : ∀ q, e q ≫ (K.X q).d 0 1 = 0)

theorem horizontal_edge_quasiIsoAt_zero
    (haug : (ShortComplex.mk (e 0) ((K.X 0).d 0 1) (w 0)).Exact)
    (hmono : ∀ q, Mono (e q)) : QuasiIsoAt ((SheafCohomology.Cech.UpNatHorizontalEdge.HomologicalComplex₂.totalUpNatHorizontalEdge K) A e he w) 0 := by
  let T := K.total (.up ℕ)
  let E := (SheafCohomology.Cech.UpNatHorizontalEdge.HomologicalComplex₂.totalUpNatHorizontalEdge K) A e he w
  have : Mono (e 0) := hmono 0
  have : Mono (e 1) := hmono 1
  have : Mono (ShortComplex.mk (e 0) ((K.X 0).d 0 1) (w 0)).f := hmono 0
  have hk : (T.iCycles 0 ≫ (SheafCohomology.Cech.UpNatLowDegrees.HomologicalComplex₂.πTotalUpNat K) 0 0 0) ≫ (K.X 0).d 0 1 = 0 := by
    rw [Category.assoc, ← TotalComplexZeroCoordinates.total_d_zero_horizontal, ← Category.assoc, T.iCycles_d, zero_comp]
  obtain ⟨l, hl⟩ := haug.lift' (T.iCycles 0 ≫ (SheafCohomology.Cech.UpNatLowDegrees.HomologicalComplex₂.πTotalUpNat K) 0 0 0) hk
  have hw : l ≫ A.d 0 1 = 0 := by
    apply (cancel_mono (e 1)).mp
    rw [zero_comp, Category.assoc, ← he 0 1 rfl, ← Category.assoc, hl,
      Category.assoc, ← TotalComplexZeroCoordinates.total_d_zero_vertical, ← Category.assoc, T.iCycles_d, zero_comp]
  let r := A.liftCycles l 1 (by simp) hw
  have hr : r ≫ A.iCycles 0 = l := A.liftCycles_i l 1 (by simp) hw
  have : Mono (E.f 0) := inferInstanceAs (Mono (e 0 ≫ K.ιTotal (.up ℕ) 0 0 0 rfl))
  have : Mono (cyclesMap E 0) := inferInstance
  have hright : r ≫ cyclesMap E 0 = 𝟙 (T.cycles 0) := by
    apply (cancel_mono (T.iCycles 0)).mp
    rw [Category.id_comp, Category.assoc, cyclesMap_i, ← Category.assoc, hr]
    change l ≫ (e 0 ≫ K.ιTotal (.up ℕ) 0 0 0 rfl) = T.iCycles 0
    rw [← Category.assoc, hl, Category.assoc, (SheafCohomology.Cech.UpNatLowDegrees.HomologicalComplex₂.totalUpNat_zero_decomposition K), Category.comp_id]
  have hleft : cyclesMap E 0 ≫ r = 𝟙 (A.cycles 0) := by
    apply (cancel_mono (cyclesMap E 0)).mp
    rw [Category.assoc, hright, Category.comp_id, Category.id_comp]
  have : IsIso (cyclesMap E 0) := ⟨⟨r, hleft, hright⟩⟩
  rw [quasiIsoAt_iff_isIso_homologyMap]
  have : IsIso (A.homologyπ 0 ≫ homologyMap E 0) := by
    rw [homologyπ_naturality]
    infer_instance
  exact IsIso.of_isIso_comp_left (A.homologyπ 0) (homologyMap E 0)

end

end OAI.AlgebraicGeometry.Comparison.Betti.TotalComplexDegreeZero
