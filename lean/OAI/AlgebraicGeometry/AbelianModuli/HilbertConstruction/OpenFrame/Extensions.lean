import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Common.DegreeChartExtensions

/-! # Extensions -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction

noncomputable section

/-! Common-degree extensions on finite families of actual affine open subsets. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u v

variable {Y : Scheme.{u}} {L : Y.Modules}

/-- A finite family of affine framed opens admits local numerators in one positive degree. -/
theorem OpenFrame.Extensions.affine_open_common_extension {ι : Type v} [Finite ι]
    (U : ι → Y.Opens) (hU : ∀ i, IsAffineOpen (U i))
    (frames : ∀ i, Nonempty ((Scheme.Modules.pullback (U i).ι).obj L ≅
      Line.Bundles.structureModule (U i).toScheme))
    (s : Line.Bundles.structureModule Y ⟶ L) (r : Γ((Ample.LineBundles.sectionNonvanishing s).toScheme, ⊤)) :
    ∃ (n : ℕ) (_ : 0 < n)
      (t : ∀ i, Line.Bundles.structureModule (U i).toScheme ⟶
        (Scheme.Modules.pullback (U i).ι).obj (TensorPower.PowerSheaf.tensorPowerModule L n)),
      ∀ i, Common.DegreeChartExtensions.ChartPowerExtends (U i).ι s r n (t i) := by
  classical
  let : Fintype ι := Fintype.ofFinite ι
  have hlocal (i : ι) := @Uniform.AffineChartExtension.affine_chart_section_extension_eventually (U i).toScheme Y
    (U i).ι inferInstance L (hU i) (frames i).some.inv inferInstance s
      ((NonvanishingRestrictionMap.sectionNonvanishingMap (U i).ι s).appTop r)
  choose n _hn h using hlocal
  let m := Finset.univ.sup n + 1
  have hm (i : ι) : n i ≤ m :=
    (Finset.le_sup (f := n) (Finset.mem_univ i)).trans (Nat.le_succ _)
  choose t ht using fun i => h i m (hm i)
  exact ⟨m, Nat.zero_lt_succ _, t, ht⟩

/-- A quasi-compact line bundle admits a finite affine frame cover and
common-degree chart extensions on that cover. -/
theorem Line.Bundles.LineBundle.exists_common_degree_open_extensions (L : Line.Bundles.LineBundle Y) [CompactSpace Y]
    (s : Line.Bundles.structureModule Y ⟶ L.sheaf) (r : Γ((Ample.LineBundles.sectionNonvanishing s).toScheme, ⊤)) :
    ∃ (k : ℕ) (U : Fin k → Y.Opens),
      (∀ i, IsAffineOpen (U i)) ∧
      (∀ i, Nonempty ((Scheme.Modules.pullback (U i).ι).obj L.sheaf ≅
        Line.Bundles.structureModule (U i).toScheme)) ∧
      (∀ y : Y, ∃ i, y ∈ U i) ∧
      ∃ (n : ℕ) (_ : 0 < n)
        (t : ∀ i, Line.Bundles.structureModule (U i).toScheme ⟶
          (Scheme.Modules.pullback (U i).ι).obj (TensorPower.PowerSheaf.tensorPowerModule L.sheaf n)),
        ∀ i, Common.DegreeChartExtensions.ChartPowerExtends (U i).ι s r n (t i) := by
  obtain ⟨k, U, hU, frames, cover⟩ := L.exists_finite_affine_frames
  exact ⟨k, U, hU, frames, cover, OpenFrame.Extensions.affine_open_common_extension U hU frames s r⟩

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction
