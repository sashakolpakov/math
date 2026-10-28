import OAI.RepresentationTheory.Theta.Geometric.Pullback.FrameComposition
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Line.Bundles

/-! # Line Bundle Field Triviality -/

namespace OAI.RepresentationTheory.Theta.Geometric.LineBundleFieldTriviality

noncomputable section

/-! Actual line bundles over a field are trivial; this supplies the
identity-fiber normalization required in the native polarization formula. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

theorem lineBundle_trivial_of_subsingleton {X : Scheme} [Nonempty X] [Subsingleton X]
    (L : AlgebraicGeometry.AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle X) : Nonempty (L.sheaf ≅ AlgebraicGeometry.AbelianModuli.HilbertConstruction.Line.Bundles.structureModule X) := by
  obtain ⟨x⟩ := ‹Nonempty X›
  obtain ⟨U, hx, ⟨e⟩⟩ := L.locallyTrivial x
  have hU : U = ⊤ := by
    apply top_unique
    intro y _
    exact (Subsingleton.elim x y) ▸ hx
  have : IsIso U.ι := by
    rw [hU, ← Scheme.topIso_hom]
    infer_instance
  let p : (Scheme.Modules.pullback (inv U.ι)).obj ((Scheme.Modules.pullback U.ι).obj L.sheaf) ≅ L.sheaf :=
    (Scheme.Modules.pullbackComp (inv U.ι) U.ι).app L.sheaf ≪≫
      (Scheme.Modules.pullbackCongr (IsIso.inv_hom_id U.ι)).app L.sheaf ≪≫
      (Scheme.Modules.pullbackId X).app L.sheaf
  exact ⟨p.symm ≪≫ (Scheme.Modules.pullback (inv U.ι)).mapIso e ≪≫ AlgebraicGeometry.AbelianModuli.HilbertConstruction.Line.Bundles.structureModulePullbackIso (inv U.ι)⟩

theorem lineBundle_over_field_trivial (K : Type) [Field K] (L : AlgebraicGeometry.AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle (Spec (.of K))) :
    Nonempty (L.sheaf ≅ AlgebraicGeometry.AbelianModuli.HilbertConstruction.Line.Bundles.structureModule (Spec (.of K))) :=
  lineBundle_trivial_of_subsingleton L

end

end OAI.RepresentationTheory.Theta.Geometric.LineBundleFieldTriviality
