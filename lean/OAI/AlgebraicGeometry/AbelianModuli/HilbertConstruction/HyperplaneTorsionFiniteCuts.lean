import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Iterated.PointedSectionCuts

/-! # Hyperplane Torsion Finite Cuts -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.HyperplaneTorsionFiniteCuts

noncomputable section

/-! On an irreducible scheme of dimension at most g+1, a nonzero
hyperplane section followed by g pullbacks of hyperplanes through a
rational point has finite common support. The intervening endomorphism
is only required to be locally quasi-finite, as multiplication is on
the tame abelian families in the torsion application. -/
open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace
universe u
variable {K : Type u} [Field K] [Infinite K] {X : Scheme.{u}}

theorem exists_hyperplane_cuts_with_finite_support
    [NoetherianSpace X] [IrreducibleSpace X]
    (p : X ⟶ Spec (.of K)) (L : Line.Bundles.LineBundle X) {n : ℕ}
    (s : Fin (n + 1) → (Line.Bundles.structureModule X ⟶ L.sheaf))
    (hcover : ∀ x : X, ∃ i, x ∈ Ample.LineBundles.sectionNonvanishing (s i))
    (ha : ∀ i, IsAffineOpen (Ample.LineBundles.sectionNonvanishing (s i)))
    (hgen : Section.ProjectivePresentation.SectionRatiosGenerate p s)
    (z : Spec (.of K) ⟶ X) (hz : z ≫ p = 𝟙 _)
    (m : X ⟶ X) [LocallyQuasiFinite m]
    (g : ℕ) (hdim : topologicalKrullDim X ≤ (g + 1 : ℕ))
    (a : Line.Bundles.structureModule X ⟶ L.sheaf) (ha_nonzero : ∃ x, x ∈ Ample.LineBundles.sectionNonvanishing a) :
    ∃ ts : List (Line.Bundles.structureModule X ⟶ L.sheaf),
      ts.length = g ∧
      (∀ t ∈ ts, z (IsLocalRing.closedPoint K) ∉ Ample.LineBundles.sectionNonvanishing t) ∧
      {x : X | x ∉ Ample.LineBundles.sectionNonvanishing a ∧
        ∀ t ∈ ts, m x ∉ Ample.LineBundles.sectionNonvanishing t}.Finite := by
  let C : Closeds X := ⟨(Ample.LineBundles.sectionNonvanishing a : Set X)ᶜ, (Ample.LineBundles.sectionNonvanishing a).isOpen.isClosed_compl⟩
  have hproper : (C : Set X) ≠ Set.univ := by
    intro h
    obtain ⟨x, hx⟩ := ha_nonzero
    have hc : x ∈ (C : Set X) := h.symm ▸ Set.mem_univ x
    exact hc hx
  have hlt := Closed.SubsetDimensionDrop.properClosed_topologicalKrullDim_lt (C : Set X) C.isClosed hproper (g + 1) hdim
  have hdimC : topologicalKrullDim (C : Set X) ≤ g := by
    simpa only [Nat.cast_add, Nat.cast_one, ENat.WithBot.lt_add_one_iff] using hlt
  let Y := ReducedClosedSubschemes.reducedClosedSubscheme X C
  let j := ReducedClosedSubschemes.reducedClosedInclusion X C
  let : NoetherianSpace Y :=
    (IsClosedImmersion.isClosedEmbedding j).isEmbedding.isInducing.noetherianSpace
  let : LocallyQuasiFinite (j ≫ m) := inferInstance
  have hdimY : topologicalKrullDim Y ≤ g :=
    (Iterated.PointedSectionCuts.reducedClosedSubschemeHomeomorph X C).isInducing.topologicalKrullDim_le.trans hdimC
  obtain ⟨ts, hlen, hzts, hfinite⟩ := Iterated.PointedSectionCuts.exists_pointed_sections_with_finite_common_zeros
    p L s hcover ha hgen z hz g Y (j ≫ m) hdimY
  refine ⟨ts, hlen, hzts, (hfinite.image j).subset ?_⟩
  intro x hx
  have hxr : x ∈ Set.range j := by
    rw [show Set.range j = (C : Set X) from ReducedClosedSubschemes.reducedClosedInclusion_range X C]
    exact hx.1
  obtain ⟨y, hy⟩ := hxr
  refine ⟨y, ?_, hy⟩
  intro t ht
  change m (j y) ∉ Ample.LineBundles.sectionNonvanishing t
  rw [hy]
  exact hx.2 t ht

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.HyperplaneTorsionFiniteCuts
