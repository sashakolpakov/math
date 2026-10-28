import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Scalar.Nonvanishing
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Tensor.LineBundles

/-! # Zero Sections -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction

noncomputable section

/-! The zero section of an algebraic line bundle has empty nonvanishing open. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

universe u

variable {X Y : Scheme.{u}}

@[simp]
theorem ZeroSections.pullbackSection_zero (f : X ⟶ Y) (L : Y.Modules) :
    Ample.LineBundles.pullbackSection f (0 : Line.Bundles.structureModule Y ⟶ L) = 0 := by
  simp only [Ample.LineBundles.pullbackSection, Functor.map_zero, comp_zero]

@[simp]
theorem ZeroSections.frameCoordinate_zero {L : X.Modules} (s : Line.Bundles.structureModule X ⟶ L) [IsIso s] :
    Frame.Coordinates.frameCoordinate s 0 = 0 := by
  change Frame.Coordinates.structureModuleEndValue X ((0 : Line.Bundles.structureModule X ⟶ L) ≫ inv s) = 0
  rw [zero_comp]
  exact map_zero (Frame.Coordinates.structureModuleEndValue X)

/-- In a globally trivialized line bundle, the zero section is nowhere a frame. -/
theorem ZeroSections.sectionNonvanishing_zero_of_frame {L : X.Modules} (e : L ≅ Line.Bundles.structureModule X) :
    Ample.LineBundles.sectionNonvanishing (0 : Line.Bundles.structureModule X ⟶ L) = ⊥ :=
  (Scalar.Nonvanishing.sectionNonvanishing_frameCoordinate e.inv 0).trans
    ((congrArg X.basicOpen (ZeroSections.frameCoordinate_zero e.inv)).trans (X.basicOpen_zero ⊤))

/-- The zero section of any line bundle has empty nonvanishing open. -/
@[simp]
theorem Line.Bundles.LineBundle.sectionNonvanishing_zero (L : Line.Bundles.LineBundle X) :
    Ample.LineBundles.sectionNonvanishing (0 : Line.Bundles.structureModule X ⟶ L.sheaf) = ⊥ := by
  apply le_bot_iff.mp
  intro x hx
  obtain ⟨U, hxU, ⟨e⟩⟩ := L.locallyTrivial x
  have he : Ample.LineBundles.sectionNonvanishing (Ample.LineBundles.pullbackSection U.ι (0 : Line.Bundles.structureModule X ⟶ L.sheaf)) = ⊥ :=
    (congrArg (fun s : Line.Bundles.structureModule U.toScheme ⟶ (Scheme.Modules.pullback U.ι).obj L.sheaf =>
      Ample.LineBundles.sectionNonvanishing s) (ZeroSections.pullbackSection_zero U.ι L.sheaf)).trans
        (ZeroSections.sectionNonvanishing_zero_of_frame e)
  have hy : (⟨x, hxU⟩ : U.toScheme) ∈
      Ample.LineBundles.sectionNonvanishing (Ample.LineBundles.pullbackSection U.ι (0 : Line.Bundles.structureModule X ⟶ L.sheaf)) :=
    (Section.Nonvanishing.sectionNonvanishing_pullback U.ι (0 : Line.Bundles.structureModule X ⟶ L.sheaf)).symm ▸ hx
  have hfalse : (⟨x, hxU⟩ : U.toScheme) ∈ (⊥ : U.toScheme.Opens) := he ▸ hy
  exact hfalse.elim

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction
