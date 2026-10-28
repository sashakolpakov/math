import OAI.NumberTheory.PadicHodge.IntegralComparison.ProperAffineCover
import OAI.NumberTheory.PadicHodge.IntegralComparison.Open.FiniteFrame
import OAI.NumberTheory.PadicHodge.IntegralComparison.Principal.OpenCover
import OAI.NumberTheory.PadicHodge.IntegralComparison.Small.CrystallineLocalization

/-! # Proper Crystalline Frames -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.ProperCrystallineFrames

noncomputable section

/-!
# IntegralComparison: a fixed finite family of charts supplies global crystalline frames

For a proper scheme, choose finite polynomial generators once on its
finite affine cover. Every original crystalline object has a finite
principal covering whose members map into frames on these fixed charts.
The construction uses the original crystalline objects and morphisms.
-/

open _root_.CategoryTheory _root_.AlgebraicGeometry

open OAI.NumberTheory.PadicHodge.IntegralComparison.ProperAffineCover OAI.NumberTheory.PadicHodge.IntegralComparison.Witt.Crystalline OAI.NumberTheory.PadicHodge.IntegralComparison.Crystalline.Presentation
open OAI.NumberTheory.PadicHodge.IntegralComparison.Small.CrystallineLocalization OAI.NumberTheory.PadicHodge.IntegralComparison.BigCrystallineSite

universe u

variable (p : ℕ) [Fact p.Prime] (k : Type u) [Field k] [Fintype k] [CharP k p]
  (X : Over (Spec (CommRingCat.of k))) [IsProper X.hom]

def affineChartMap (i : (ProperAffineCover.cover X.hom).I₀) :
    (Crystalline.Presentation.affineScheme k (ProperAffineCover.coordinateRing X.hom i)).left ⟶ X.left := ProperAffineCover.chartMap X.hom i

instance affineChartMap_open (i : (ProperAffineCover.cover X.hom).I₀) : IsOpenImmersion (affineChartMap k X i) :=
  ProperAffineCover.chartMap_open X.hom i

omit [Fintype k] in
theorem affineChartMap_over (i : (ProperAffineCover.cover X.hom).I₀) :
    affineChartMap k X i ≫ X.hom = (Crystalline.Presentation.affineScheme k (ProperAffineCover.coordinateRing X.hom i)).hom :=
  ProperAffineCover.chartMap_over X.hom i

/-- A fixed finite affine cover with finite polynomial coordinates controls every
original crystalline object after a finite principal refinement. -/
theorem exists_frames :
    ∃ (σ : (ProperAffineCover.cover X.hom).I₀ → Type u) (_ : ∀ i, Fintype (σ i))
      (x : ∀ i, σ i → ProperAffineCover.coordinateRing X.hom i)
      (hx : ∀ i, Function.Surjective
        (MvPolynomial.aeval (x i) : MvPolynomial (σ i) k →ₐ[k] ProperAffineCover.coordinateRing X.hom i)),
      ∀ U : Witt.Crystalline.CrystallineObject p k X,
        ∃ s : Finset U.ring, Ideal.span (s : Set U.ring) = ⊤ ∧
          Small.CrystallineLocalization.smallPresieve U (fun r : s => r.val) ∈ Crystalline.Site.AffineThickening.precoverage U ∧
          ∀ r ∈ s, ∃ (i : (ProperAffineCover.cover X.hom).I₀) (n : ℕ),
            Nonempty (Small.CrystallineLocalization.smallObject U r ⟶ Open.FiniteFrame.frame p k
              (ProperAffineCover.coordinateRing X.hom i) (σ i) (x i) (hx i) X
              (affineChartMap k X i) (affineChartMap_over k X i) n) := by
  choose σ hσ x hx using ProperAffineCover.chart_generators X.hom
  refine ⟨σ, hσ, x, hx, ?_⟩
  intro U
  have hcover : ∀ z : X.left, ∃ i, z ∈ Set.range (ProperAffineCover.chartMap X.hom i) := by
    intro z
    have hz : z ∈ (⨆ i, (ProperAffineCover.chartMap X.hom i).opensRange : X.left.Opens) := by
      rw [ProperAffineCover.chartMaps_cover]
      trivial
    exact (TopologicalSpace.Opens.mem_iSup.mp hz)
  obtain ⟨s, hspan, hs⟩ := Principal.OpenCover.finite_principal_refinement (BigCrystallineSite.fromSmall.obj U)
    (fun i => Spec (ProperAffineCover.coordinateRing X.hom i)) (ProperAffineCover.chartMap X.hom) hcover
  change Finset U.ring at s
  change Ideal.span (s : Set U.ring) = ⊤ at hspan
  refine ⟨s, hspan, ?_, ?_⟩
  · apply Small.CrystallineLocalization.small_covering
    have he : Set.range (fun r : s => r.val) = (s : Set U.ring) := by
      ext a
      constructor
      · rintro ⟨b, rfl⟩
        exact b.property
      · intro ha
        exact ⟨⟨a, ha⟩, rfl⟩
    rw [he]
    exact hspan
  intro r hr
  obtain ⟨i, hi⟩ := hs r hr
  let V := Small.CrystallineLocalization.smallObject U r
  let j : (Crystalline.Presentation.affineScheme k (ProperAffineCover.coordinateRing X.hom i)).left ⟶ X.left := ProperAffineCover.chartMap X.hom i
  have : IsOpenImmersion j := ProperAffineCover.chartMap_open X.hom i
  have hj : j ≫ X.hom = (Crystalline.Presentation.affineScheme k (ProperAffineCover.coordinateRing X.hom i)).hom := ProperAffineCover.chartMap_over X.hom i
  have hv : Set.range V.openMap ⊆ Set.range j := hi
  let t := IsOpenImmersion.lift j V.openMap hv
  have ht : t ≫ j = V.openMap := IsOpenImmersion.lift_fac j V.openMap hv
  obtain ⟨n, hn⟩ := Open.FiniteFrame.exists_presentation p k (ProperAffineCover.coordinateRing X.hom i)
    (σ i) (x i) (hx i) X j hj V t ht
  exact ⟨i, n, hn⟩

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.ProperCrystallineFrames
