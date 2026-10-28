import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Field.ExternalFirstCohomology
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Affine.Frames
import Mathlib.AlgebraicGeometry.Morphisms.Proper

/-! # Field External First Cohomology -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Proper.FieldExternalFirstCohomology

noncomputable section

/-! Properness supplies the finite affine frame covers in the external-product first-cohomology vanishing theorem. -/
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.TopologicalSpace _root_.AlgebraicGeometry
universe u

theorem properFieldExternalTensor_firstCohomology_vanish
    {k : Type u} [Field k] {X Y P : Scheme.{u}}
    {a : P ⟶ X} {b : P ⟶ Y} {f : X ⟶ Spec (.of k)} {g : Y ⟶ Spec (.of k)}
    (H : IsPullback a b f g) [IsProper f] [IsProper g]
    (L : Line.Bundles.LineBundle X) (N : Line.Bundles.LineBundle Y) (n : ℕ)
    (hL : ∀ r, r < n + 1 → Subsingleton (Zariski.Cohomology.ZariskiCohomology.H L.sheaf r))
    (hN : Subsingleton Γ(N.sheaf, ⊤)) :
    Subsingleton (Zariski.Cohomology.ZariskiCohomology.H (((L.pullback a).tensor (N.pullback b)).sheaf) (n + 1)) := by
  have : X.IsSeparated := ⟨by rw [← terminal.comp_from f]; infer_instance⟩
  have : Y.IsSeparated := ⟨by rw [← terminal.comp_from g]; infer_instance⟩
  have : IsProper a := MorphismProperty.of_isPullback H.flip inferInstance
  have : P.IsSeparated := ⟨by rw [← terminal.comp_from (a ≫ f)]; infer_instance⟩
  have : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace f
  have : CompactSpace Y := QuasiCompact.compactSpace_of_compactSpace g
  obtain ⟨v, V, haV, heV, hcoverV⟩ := L.exists_finite_affine_frames
  obtain ⟨w, U, haU, heU, hcoverU⟩ := N.exists_finite_affine_frames
  let V' : ULift.{u} (Fin v) → X.Opens := fun i => V i.down
  let U' : ULift.{u} (Fin w) → Y.Opens := fun i => U i.down
  have hV' : iSup V' = ⊤ := by
    apply top_unique
    intro x _
    obtain ⟨i, hi⟩ := hcoverV x
    exact Opens.mem_iSup.mpr ⟨⟨i⟩, hi⟩
  have hU' : iSup U' = ⊤ := by
    apply top_unique
    intro y _
    obtain ⟨i, hi⟩ := hcoverU y
    exact Opens.mem_iSup.mpr ⟨⟨i⟩, hi⟩
  exact HilbertConstruction.Field.ExternalFirstCohomology.fieldExternalTensor_firstCohomology_vanish H L N
    V' hV' (fun i => haV i.down) (fun i => heV i.down)
    U' hU' (fun i => haU i.down) (fun i => heU i.down) n hL hN

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Proper.FieldExternalFirstCohomology
