import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Uniform.AffineChartExtension
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.NonvanishingRestrictionMap
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Affine.FrameCover

/-! # Degree Chart Extensions -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction

noncomputable section

/-!
Construct extensions of a function on `D(s)` on a finite affine frame cover,
all valued in restrictions of the same positive tensor power. Agreement on
the complete chart overlaps is a separate gluing step.
-/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u v

variable {X Y : Scheme.{u}} {L : Y.Modules}

/-- A local numerator has the prescribed ratio on the part of `D(s)` in its chart. -/
def Common.DegreeChartExtensions.ChartPowerExtends (f : X ⟶ Y) [IsOpenImmersion f]
    (s : Line.Bundles.structureModule Y ⟶ L) (r : Γ((Ample.LineBundles.sectionNonvanishing s).toScheme, ⊤))
    (n : ℕ) (t : Line.Bundles.structureModule X ⟶ (Scheme.Modules.pullback f).obj (TensorPower.PowerSheaf.tensorPowerModule L n)) :
    Prop :=
  letI := Power.SectionTransport.iteratedPullback_power_isIso f n (Ample.LineBundles.sectionNonvanishing (Ample.LineBundles.pullbackSection f s)).ι s
  Frame.Coordinates.frameCoordinate
    (Ample.LineBundles.pullbackSection (Ample.LineBundles.sectionNonvanishing (Ample.LineBundles.pullbackSection f s)).ι
      (Ample.LineBundles.pullbackSection f (TensorPower.Maps.tensorPowerSection s n)))
    (Ample.LineBundles.pullbackSection (Ample.LineBundles.sectionNonvanishing (Ample.LineBundles.pullbackSection f s)).ι t) =
      (NonvanishingRestrictionMap.sectionNonvanishingMap f s).appTop r

/-- A finite affine frame cover admits local extensions in a common positive degree. -/
theorem Common.DegreeChartExtensions.affine_frame_cover_common_extension (C : Scheme.AffineOpenCover.{v} Y) [Finite C.I₀]
    (frames : ∀ i, Nonempty ((Scheme.Modules.pullback (C.f i)).obj L ≅
      Line.Bundles.structureModule (Spec (C.X i))))
    (s : Line.Bundles.structureModule Y ⟶ L) (r : Γ((Ample.LineBundles.sectionNonvanishing s).toScheme, ⊤)) :
    ∃ (n : ℕ) (_ : 0 < n)
      (t : ∀ i, Line.Bundles.structureModule (Spec (C.X i)) ⟶
        (Scheme.Modules.pullback (C.f i)).obj (TensorPower.PowerSheaf.tensorPowerModule L n)),
      ∀ i, Common.DegreeChartExtensions.ChartPowerExtends (C.f i) s r n (t i) := by
  classical
  let : Fintype C.I₀ := Fintype.ofFinite C.I₀
  have hlocal (i : C.I₀) := Uniform.AffineChartExtension.affine_chart_section_extension_eventually
    (C.f i) (frames i).some.inv s ((NonvanishingRestrictionMap.sectionNonvanishingMap (C.f i) s).appTop r)
  choose n _hn h using hlocal
  let m := Finset.univ.sup n + 1
  have hm (i : C.I₀) : n i ≤ m :=
    (Finset.le_sup (f := n) (Finset.mem_univ i)).trans (Nat.le_succ _)
  choose t ht using fun i => h i m (hm i)
  exact ⟨m, Nat.zero_lt_succ _, t, ht⟩

/-- A line bundle on a quasi-compact scheme has a finite affine cover carrying
local extensions of any function on `D(s)` in one common positive tensor power. -/
theorem Line.Bundles.LineBundle.exists_common_degree_chart_extensions (L : Line.Bundles.LineBundle Y) [CompactSpace Y]
    (s : Line.Bundles.structureModule Y ⟶ L.sheaf) (r : Γ((Ample.LineBundles.sectionNonvanishing s).toScheme, ⊤)) :
    ∃ C : Scheme.AffineOpenCover.{0} Y, Finite C.I₀ ∧
      ∃ (n : ℕ) (_ : 0 < n)
        (t : ∀ i, Line.Bundles.structureModule (Spec (C.X i)) ⟶
          (Scheme.Modules.pullback (C.f i)).obj (TensorPower.PowerSheaf.tensorPowerModule L.sheaf n)),
        ∀ i, Common.DegreeChartExtensions.ChartPowerExtends (C.f i) s r n (t i) := by
  obtain ⟨C, hC, frames⟩ := L.exists_finite_affine_frame_cover
  have : Finite C.I₀ := hC
  exact ⟨C, hC, Common.DegreeChartExtensions.affine_frame_cover_common_extension C frames s r⟩

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction
