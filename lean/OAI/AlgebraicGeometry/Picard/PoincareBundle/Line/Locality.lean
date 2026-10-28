import OAI.AlgebraicGeometry.Picard.PoincareBundle.Line.Bundles

/-! # Locality -/

namespace OAI.AlgebraicGeometry.Picard.PoincareBundle.Line.Locality

noncomputable section

/-!
# Local detection of line bundles for PoincareBundle
-/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

/-- A trivialization on an open subset of an open subscheme gives a
trivialization on its image in the ambient scheme. -/
def imageTrivialization {X : Scheme.{u}} (M : X.Modules)
    (U : X.Opens) (V : Scheme.Opens U)
    (e : (Scheme.Modules.pullback V.ι).obj ((Scheme.Modules.pullback U.ι).obj M) ≅
      Bundles.unitLine V) :
    (Scheme.Modules.pullback (U.ι ''ᵁ V).ι).obj M ≅
      Bundles.unitLine (U.ι ''ᵁ V) := by
  let a := (U.ι.isoImage V).inv
  exact (Scheme.Modules.pullbackCongr (U.ι.isoImage_inv_ι V).symm).app M ≪≫
    ((Scheme.Modules.pullbackComp a (V.ι ≫ U.ι)).app M).symm ≪≫
    (Scheme.Modules.pullback a).mapIso
      (((Scheme.Modules.pullbackComp V.ι U.ι).app M).symm ≪≫ e) ≪≫
    Bundles.pullbackUnitIso a

/-- Local rank one can be checked on an open neighborhood of every point. -/
theorem isLine_of_locally_isLine {X : Scheme.{u}} (M : X.Modules)
    (h : ∀ x : X, ∃ U : X.Opens, x ∈ U ∧
      Bundles.IsLine ((Scheme.Modules.pullback U.ι).obj M)) :
    Bundles.IsLine M := by
  intro x
  obtain ⟨U, hx, hU⟩ := h x
  obtain ⟨V, hxV, ⟨e⟩⟩ := hU ⟨x, hx⟩
  refine ⟨U.ι ''ᵁ V, ?_, ⟨imageTrivialization M U V e⟩⟩
  exact ⟨⟨x, hx⟩, hxV, rfl⟩

end

end OAI.AlgebraicGeometry.Picard.PoincareBundle.Line.Locality
