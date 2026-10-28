import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Affine.Frames
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.MixedKoszulPullbackComplex

/-! # Line Bundle Common Frames -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Finite.LineBundleCommonFrames

noncomputable section

/-! A finite list of line bundles admits simultaneous frames on an
affine neighborhood of every point. This applies to the coefficient
bundle and all bundles in a mixed Koszul complex. -/
open _root_.CategoryTheory _root_.AlgebraicGeometry
universe u

variable {X : Scheme.{u}}

theorem finiteLineBundles_common_frame (ls : List (Line.Bundles.LineBundle X)) (x : X) :
    ∃ U : X.Opens, x ∈ U ∧ ∀ L ∈ ls,
      Nonempty ((Scheme.Modules.pullback U.ι).obj L.sheaf ≅ Line.Bundles.structureModule U.toScheme) := by
  induction ls with
  | nil => exact ⟨⊤, trivial, by simp⟩
  | cons L ls ih =>
    obtain ⟨U, hxU, e⟩ := ih
    obtain ⟨V, hxV, ⟨f⟩⟩ := L.locallyTrivial x
    refine ⟨U ⊓ V, ⟨hxU, hxV⟩, ?_⟩
    intro M hM
    rcases List.mem_cons.mp hM with rfl | hM
    · exact ⟨M.frameRestrict inf_le_right f⟩
    · exact ⟨M.frameRestrict inf_le_left (Classical.choice (e M hM))⟩

theorem finiteLineBundles_common_affine_frame (ls : List (Line.Bundles.LineBundle X)) (x : X) :
    ∃ U : X.Opens, x ∈ U ∧ IsAffineOpen U ∧ ∀ L ∈ ls,
      Nonempty ((Scheme.Modules.pullback U.ι).obj L.sheaf ≅ Line.Bundles.structureModule U.toScheme) := by
  obtain ⟨V, hxV, e⟩ := finiteLineBundles_common_frame ls x
  obtain ⟨_, ⟨U : X.Opens, hU, rfl⟩, hxU, hUV⟩ :=
    X.isBasis_affineOpens.exists_subset_of_mem_open hxV V.isOpen
  exact ⟨U, hxU, hU, fun L hL =>
    ⟨L.frameRestrict hUV (Classical.choice (e L hL))⟩⟩

theorem mixedKoszul_common_affine_frame (M : Line.Bundles.LineBundle X)
    (bs : List (LineBundleKoszulComplex.LineBundleSection X)) (x : X) :
    ∃ U : X.Opens, x ∈ U ∧ IsAffineOpen U ∧
      Nonempty ((M.pullback U.ι).sheaf ≅ Line.Bundles.structureModule U.toScheme) ∧
      ∀ b ∈ bs.map (MixedKoszulPullbackComplex.pullbackLineBundleSection U.ι),
        Nonempty (b.1.sheaf ≅ Line.Bundles.structureModule U.toScheme) := by
  obtain ⟨U, hxU, hU, e⟩ := finiteLineBundles_common_affine_frame (M :: bs.map Sigma.fst) x
  refine ⟨U, hxU, hU, e M (by simp), ?_⟩
  intro b hb
  obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hb
  exact e a.1 (List.mem_cons_of_mem _ (List.mem_map.mpr ⟨a, ha, rfl⟩))

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Finite.LineBundleCommonFrames
