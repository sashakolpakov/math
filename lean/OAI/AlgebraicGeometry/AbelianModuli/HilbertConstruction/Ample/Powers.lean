import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.LineBundle.Powers
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Section.Nonvanishing

/-! # Powers -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction

noncomputable section

/-! Ampleness expressed using constructed tensor powers, and finite affine section covers. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

variable {X Y : Scheme.{u}}

/-- Changing the target of a section by an isomorphism preserves its nonvanishing open. -/
theorem Ample.Powers.sectionNonvanishing_comp_iso {P Q : X.Modules}
    (s : Line.Bundles.structureModule X ⟶ P) (e : P ≅ Q) :
    Ample.LineBundles.sectionNonvanishing (s ≫ e.hom) = Ample.LineBundles.sectionNonvanishing s := by
  apply congrArg sSup
  ext U
  change IsIso (Ample.LineBundles.pullbackSection U.ι (s ≫ e.hom)) ↔ IsIso (Ample.LineBundles.pullbackSection U.ι s)
  simp only [Ample.LineBundles.pullbackSection, Functor.map_comp, ← Category.assoc, isIso_comp_right_iff]

/-- The constructed tensor power restricts to the constructed power of the restriction. -/
def Line.Bundles.LineBundle.tensorPowerPullbackIso (L : Line.Bundles.LineBundle Y) (n : ℕ) (f : X ⟶ Y) [IsOpenImmersion f] :
    ((L.tensorPower n).pullback f).sheaf ≅ ((L.pullback f).tensorPower n).sheaf :=
  Classical.choice (((L.tensorPower_isTensorPower n).pullback_of_isOpenImmersion f).unique
    ((L.pullback f).tensorPower_isTensorPower n))

/-- The arbitrary tensor-power witness in ampleness may be replaced by the constructed power. -/
theorem Line.Bundles.LineBundle.isAmple_iff_tensorPower (L : Line.Bundles.LineBundle X) :
    L.IsAmple ↔ IsCompact (Set.univ : Set X) ∧
      ∀ x : X, ∃ (n : ℕ) (_ : 0 < n) (s : Line.Bundles.structureModule X ⟶ (L.tensorPower n).sheaf),
        x ∈ Ample.LineBundles.sectionNonvanishing s ∧ IsAffineOpen (Ample.LineBundles.sectionNonvanishing s) := by
  constructor
  · rintro ⟨hX, hL⟩
    refine ⟨hX, fun x => ?_⟩
    obtain ⟨n, hn, P, hP, s, hx, hs⟩ := hL x
    obtain ⟨e⟩ := hP.unique (L.tensorPower_isTensorPower n)
    refine ⟨n, hn, s ≫ e.hom, ?_, ?_⟩
    · rw [Ample.Powers.sectionNonvanishing_comp_iso]
      exact hx
    · rw [Ample.Powers.sectionNonvanishing_comp_iso]
      exact hs
  · rintro ⟨hX, hL⟩
    refine ⟨hX, fun x => ?_⟩
    obtain ⟨n, hn, s, hx, hs⟩ := hL x
    exact ⟨n, hn, L.tensorPower n, L.tensorPower_isTensorPower n, s, hx, hs⟩

/-- Finitely many actual sections of positive powers have affine nonvanishing loci covering X. -/
theorem Line.Bundles.LineBundle.IsAmple.finite_tensorPower_cover {L : Line.Bundles.LineBundle X} (hL : L.IsAmple) :
    ∃ (k : ℕ) (n : Fin k → ℕ) (_ : ∀ i, 0 < n i)
      (s : ∀ i, Line.Bundles.structureModule X ⟶ (L.tensorPower (n i)).sheaf),
      (∀ i, IsAffineOpen (Ample.LineBundles.sectionNonvanishing (s i))) ∧
        ∀ x : X, ∃ i, x ∈ Ample.LineBundles.sectionNonvanishing (s i) := by
  classical
  obtain ⟨hX, h⟩ := (L.isAmple_iff_tensorPower).mp hL
  choose n hn s hx hs using h
  obtain ⟨t, ht⟩ := hX.elim_finite_subcover
    (fun x => (Ample.LineBundles.sectionNonvanishing (s x) : Set X))
    (fun x => (Ample.LineBundles.sectionNonvanishing (s x)).isOpen)
    (fun x _ => Set.mem_iUnion.mpr ⟨x, hx x⟩)
  let e := Fintype.equivFin t
  refine ⟨Fintype.card t, fun i => n (e.symm i).val, fun i => hn _,
    fun i => s (e.symm i).val, fun i => hs _, fun x => ?_⟩
  obtain ⟨y, hy, hxy⟩ := Set.mem_iUnion₂.mp (ht (Set.mem_univ x))
  refine ⟨e ⟨y, hy⟩, ?_⟩
  have he : (e.symm (e ⟨y, hy⟩)).val = y := congrArg Subtype.val (e.symm_apply_apply ⟨y, hy⟩)
  exact (congrArg (fun z => x ∈ Ample.LineBundles.sectionNonvanishing (s z)) he).mpr hxy

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction
