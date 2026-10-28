import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.DisjointCoverSectionExtension
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.LineBundle.PowerBaseChange
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Ample.PowerStability

/-! # Disjoint Cover Ampleness -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction

noncomputable section

/-! Ampleness of an actual line bundle can be checked on a finite disjoint open cover. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u v

theorem Line.Bundles.LineBundle.isAmple_of_finite_disjoint_open_cover
    {X : Scheme.{u}} {ι : Type v} [Finite ι]
    (T : ι → Scheme.{u}) (g : ∀ i, T i ⟶ X) [∀ i, IsOpenImmersion (g i)]
    (hg : ∀ x : X, ∃ i, x ∈ g i ''ᵁ (⊤ : (T i).Opens))
    (hdis : Pairwise (fun i j => Disjoint (g i ''ᵁ (⊤ : (T i).Opens)) (g j ''ᵁ (⊤ : (T j).Opens))))
    (L : Line.Bundles.LineBundle X) (hL : ∀ i, (L.pullback (g i)).IsAmple) : L.IsAmple := by
  have hc : IsCompact (Set.univ : Set X) := by
    have hcover : (⋃ i, g i '' (Set.univ : Set (T i))) = Set.univ := by
      apply Set.eq_univ_of_forall
      intro x
      obtain ⟨i, hi⟩ := hg x
      exact Set.mem_iUnion.mpr ⟨i, hi⟩
    exact hcover ▸ isCompact_iUnion (fun i => (hL i).1.image (g i).continuous)
  apply L.isAmple_iff_tensorPower.mpr
  refine ⟨hc, fun x => ?_⟩
  obtain ⟨i, y, _, hy⟩ := hg x
  obtain ⟨n, hn, s, hys, has⟩ := ((L.pullback (g i)).isAmple_iff_tensorPower.mp (hL i)).2 y
  let q := s ≫ (L.powerBaseChangeIso (g i) n).inv
  have hq : Ample.LineBundles.sectionNonvanishing q = Ample.LineBundles.sectionNonvanishing s :=
    Ample.Powers.sectionNonvanishing_comp_iso s (L.powerBaseChangeIso (g i) n).symm
  obtain ⟨t, ht, hzero⟩ := DisjointCoverSectionExtension.moduleSection_extend_by_zero_on_disjoint_cover T g hg
    (L.tensorPower n).sheaf hdis i q
  have he := (L.tensorPower n).sectionNonvanishing_extension_by_zero T g hg i q t ht hzero
  refine ⟨n, hn, t, ?_, ?_⟩
  · apply (congrArg (fun U : X.Opens => x ∈ U) he).mpr
    exact ⟨y, (congrArg (fun U : (T i).Opens => y ∈ U) hq).mpr hys, hy⟩
  · apply (congrArg IsAffineOpen he).mpr
    exact (g i).isAffineOpen_iff_of_isOpenImmersion.mpr ((congrArg IsAffineOpen hq).mpr has)

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction
