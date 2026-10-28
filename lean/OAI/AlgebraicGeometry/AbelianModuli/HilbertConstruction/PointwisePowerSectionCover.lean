import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Ample.Powers

/-! # Pointwise Power Section Cover -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction

noncomputable section

/-! On a quasi-compact scheme, pointwise nonvanishing global sections of positive line-bundle powers have a finite subcover. Affineness of their nonvanishing opens is not assumed. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

theorem Line.Bundles.LineBundle.finite_powerSection_cover_of_pointwise
    {X : Scheme.{u}} [CompactSpace X] (L : Line.Bundles.LineBundle X)
    (h : ∀ x : X, ∃ (n : ℕ) (_ : 0 < n) (s : Line.Bundles.structureModule X ⟶ (L.tensorPower n).sheaf),
      x ∈ Ample.LineBundles.sectionNonvanishing s) :
    ∃ (k : ℕ) (n : Fin k → ℕ) (_ : ∀ i, 0 < n i)
      (s : ∀ i, Line.Bundles.structureModule X ⟶ (L.tensorPower (n i)).sheaf),
      ∀ x : X, ∃ i, x ∈ Ample.LineBundles.sectionNonvanishing (s i) := by
  classical
  choose n hn s hx using h
  obtain ⟨t, ht⟩ := isCompact_univ.elim_finite_subcover
    (fun x => (Ample.LineBundles.sectionNonvanishing (s x) : Set X))
    (fun x => (Ample.LineBundles.sectionNonvanishing (s x)).isOpen)
    (fun x _ => Set.mem_iUnion.mpr ⟨x, hx x⟩)
  let e := Fintype.equivFin t
  refine ⟨Fintype.card t, fun i => n (e.symm i).val, fun i => hn _,
    fun i => s (e.symm i).val, fun x => ?_⟩
  obtain ⟨y, hy, hxy⟩ := Set.mem_iUnion₂.mp (ht (Set.mem_univ x))
  refine ⟨e ⟨y, hy⟩, ?_⟩
  have he : (e.symm (e ⟨y, hy⟩)).val = y := congrArg Subtype.val (e.symm_apply_apply ⟨y, hy⟩)
  exact (congrArg (fun z => x ∈ Ample.LineBundles.sectionNonvanishing (s z)) he).mpr hxy

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction
