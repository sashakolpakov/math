import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.External.AcyclicEuler

/-! # Compact External Acyclic Euler -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.CompactExternalAcyclicEuler

noncomputable section

/-! Compact factors supply the finite affine frame covers needed for the
external Euler product formula. -/
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.TopologicalSpace _root_.AlgebraicGeometry
universe u

theorem fieldExternal_euler_of_positive_vanishing_of_compact
    {k : Type u} [Field k] {X Y P : Scheme.{u}}
    [X.IsSeparated] [Y.IsSeparated] [P.IsSeparated] [CompactSpace X] [CompactSpace Y]
    {a : P ⟶ X} {b : P ⟶ Y} {f : X ⟶ Spec (.of k)} {g : Y ⟶ Spec (.of k)}
    (H : IsPullback a b f g) (L : Line.Bundles.LineBundle X) (N : Line.Bundles.LineBundle Y)
    (hL : ∀ q, Subsingleton (Zariski.Cohomology.ZariskiCohomology.H L.sheaf (q + 1)))
    (hN : ∀ q, Subsingleton (Zariski.Cohomology.ZariskiCohomology.H N.sheaf (q + 1))) :
    CohomologyEulerCharacteristic.coefficientEulerCharacteristic (b ≫ g) (((L.pullback a).tensor (N.pullback b)).sheaf) =
      CohomologyEulerCharacteristic.coefficientEulerCharacteristic f L.sheaf * CohomologyEulerCharacteristic.coefficientEulerCharacteristic g N.sheaf := by
  obtain ⟨r, V, haV, heV, hcoverV⟩ := L.exists_finite_affine_frames
  obtain ⟨s, U, haU, heU, hcoverU⟩ := N.exists_finite_affine_frames
  let V' : ULift.{u} (Fin r) → X.Opens := fun i => V i.down
  let U' : ULift.{u} (Fin s) → Y.Opens := fun i => U i.down
  have hV : iSup V' = ⊤ := by
    apply le_antisymm le_top
    intro x _
    obtain ⟨i, hi⟩ := hcoverV x
    exact Opens.mem_iSup.mpr ⟨⟨i⟩, hi⟩
  have hU : iSup U' = ⊤ := by
    apply le_antisymm le_top
    intro x _
    obtain ⟨i, hi⟩ := hcoverU x
    exact Opens.mem_iSup.mpr ⟨⟨i⟩, hi⟩
  exact External.AcyclicEuler.fieldExternal_euler_of_positive_vanishing H L N V' hV
    (fun i => haV i.down) (fun i => heV i.down) U'
    (fun i => haU i.down) (fun i => heU i.down) hU hL hN

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.CompactExternalAcyclicEuler
