import OAI.AlgebraicGeometry.Quotients.FiniteDescent.ProperFunctionsEq
import OAI.AlgebraicGeometry.Quotients.FiniteDescent.ReducedSectionsEq
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Section.PowerLocus
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Global.Sections
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Scalar.Nonvanishing
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.ZeroSections

/-! # Torsion Line -/

namespace OAI.AlgebraicGeometry.Quotients.FiniteDescent.TorsionLine.Construction.TorsionLineBundle

/-!
# Sections of torsion line bundles on proper schemes

For an actual line bundle whose positive tensor power is trivial, a section
is either nowhere a frame or a frame everywhere. The proof uses the
constructed tensor-power section and the field of global functions.
-/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

theorem nonvanishing_eq_bot_or_top {K : Type u} [Field K]
    (X : Over (Spec (.of K))) [IsProper X.hom] [ConnectedSpace X.left] [IsReduced X.left]
    (L : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle X.left) (n : ℕ) (hn : 0 < n)
    (e : (L.tensorPower n).sheaf ≅ AbelianModuli.HilbertConstruction.Line.Bundles.structureModule X.left)
    (s : AbelianModuli.HilbertConstruction.Line.Bundles.structureModule X.left ⟶ L.sheaf) :
    AbelianModuli.HilbertConstruction.Ample.LineBundles.sectionNonvanishing s = ⊥ ∨ AbelianModuli.HilbertConstruction.Ample.LineBundles.sectionNonvanishing s = ⊤ := by
  let t : End (AbelianModuli.HilbertConstruction.Line.Bundles.structureModule X.left) := AbelianModuli.HilbertConstruction.TensorPower.Maps.tensorPowerSection s n ≫ e.hom
  have ht : AbelianModuli.HilbertConstruction.Ample.LineBundles.sectionNonvanishing t = AbelianModuli.HilbertConstruction.Ample.LineBundles.sectionNonvanishing s :=
    (AbelianModuli.HilbertConstruction.Ample.Powers.sectionNonvanishing_comp_iso (AbelianModuli.HilbertConstruction.TensorPower.Maps.tensorPowerSection s n) e).trans
      (AbelianModuli.HilbertConstruction.Section.PowerLocus.sectionNonvanishing_tensorPowerSection s n hn)
  have hscalar := ProperFunctionsEq.Construction.ProperFunctions.section_eq_zero_or_isUnit X (AbelianModuli.HilbertConstruction.Frame.Coordinates.structureModuleEndValue X.left t)
  rw [← ht, AbelianModuli.HilbertConstruction.Scalar.Nonvanishing.sectionNonvanishing_scalar]
  rcases hscalar with hz | hu
  · exact Or.inl (hz ▸ X.left.basicOpen_zero ⊤)
  · exact Or.inr (X.left.basicOpen_of_isUnit hu)

/-- A torsion line bundle with a section nonvanishing somewhere is
trivialized by that section. -/
theorem isIso_of_nonempty_nonvanishing {K : Type u} [Field K]
    (X : Over (Spec (.of K))) [IsProper X.hom] [ConnectedSpace X.left] [IsReduced X.left]
    (L : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle X.left) (n : ℕ) (hn : 0 < n)
    (e : (L.tensorPower n).sheaf ≅ AbelianModuli.HilbertConstruction.Line.Bundles.structureModule X.left)
    (s : AbelianModuli.HilbertConstruction.Line.Bundles.structureModule X.left ⟶ L.sheaf)
    (hs : (AbelianModuli.HilbertConstruction.Ample.LineBundles.sectionNonvanishing s : Set X.left).Nonempty) : IsIso s := by
  have htop : AbelianModuli.HilbertConstruction.Ample.LineBundles.sectionNonvanishing s = ⊤ :=
    (nonvanishing_eq_bot_or_top X L n hn e s).resolve_left (by
      intro hbot
      obtain ⟨x, hx⟩ := hs
      rw [hbot] at hx
      exact hx.elim)
  exact (AbelianModuli.HilbertConstruction.Section.Frames.isIso_iff_sectionNonvanishing_eq_top s).mpr htop

/-- Every nonzero section of a torsion line bundle on a reduced proper
connected scheme trivializes the line bundle. -/
theorem isIso_of_ne_zero {K : Type u} [Field K]
    (X : Over (Spec (.of K))) [IsProper X.hom] [ConnectedSpace X.left] [IsReduced X.left]
    (L : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle X.left) (n : ℕ) (hn : 0 < n)
    (e : (L.tensorPower n).sheaf ≅ AbelianModuli.HilbertConstruction.Line.Bundles.structureModule X.left)
    (s : AbelianModuli.HilbertConstruction.Line.Bundles.structureModule X.left ⟶ L.sheaf) (hs : s ≠ 0) : IsIso s := by
  apply isIso_of_nonempty_nonvanishing X L n hn e s
  by_contra h
  exact hs (ReducedSectionsEq.Construction.ReducedSections.section_eq_zero_of_nonvanishing_eq_bot L s
    ((TopologicalSpace.Opens.not_nonempty_iff_eq_bot _).mp h))

/-- A nontrivial torsion line bundle has no nonzero global section. -/
theorem section_eq_zero_of_nontrivial {K : Type u} [Field K]
    (X : Over (Spec (.of K))) [IsProper X.hom] [ConnectedSpace X.left] [IsReduced X.left]
    (L : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle X.left) (n : ℕ) (hn : 0 < n)
    (e : (L.tensorPower n).sheaf ≅ AbelianModuli.HilbertConstruction.Line.Bundles.structureModule X.left)
    (hL : ¬ Nonempty (L.sheaf ≅ AbelianModuli.HilbertConstruction.Line.Bundles.structureModule X.left))
    (s : AbelianModuli.HilbertConstruction.Line.Bundles.structureModule X.left ⟶ L.sheaf) : s = 0 := by
  by_contra hs
  have : IsIso s := isIso_of_ne_zero X L n hn e s hs
  exact hL ⟨(asIso s).symm⟩

end OAI.AlgebraicGeometry.Quotients.FiniteDescent.TorsionLine.Construction.TorsionLineBundle
