import OAI.AlgebraicGeometry.Crystalline.Cohomology.Base.ProperOrdinaryFormCharts
import Mathlib.RingTheory.Artinian.Ring

/-! # Section Form Chart -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Intrinsic.SectionFormChart

noncomputable section

/-! One original native form chart contains the whole Artinian
section. Intersecting it with a prescribed section neighborhood keeps
that section and supplies the chart bound for residue comparison. -/
open _root_.CategoryTheory _root_.AlgebraicGeometry
universe u
variable (R : Type u) [CommRing R] [IsArtinianRing R] [IsLocalRing R]
  (X : Over (Spec (CommRingCat.of R))) [IsProper X.hom] [Smooth X.hom]
  (s : Spec (CommRingCat.of R) ⟶ X.left)

theorem exists_chart : ∃ j : AlgebraicGeometry.Crystalline.Cohomology.Base.SmoothProperEtaleCover.BaseSmoothProperEtaleCover.Index R X,
    ⊤ ≤ s ⁻¹ᵁ AlgebraicGeometry.Crystalline.Cohomology.Base.ProperOrdinaryFormCharts.BaseSmoothProperOrdinaryFormCharts.opens R X j := by
  let : Subsingleton (Spec (CommRingCat.of R)) := Ring.KrullDimLE.subsingleton_primeSpectrum R
  let p : Spec (CommRingCat.of R) := Classical.ofNonempty
  obtain ⟨j,hj⟩ := AlgebraicGeometry.Crystalline.Cohomology.Base.SmoothProperEtaleCover.BaseSmoothProperEtaleCover.covers R X (s p)
  refine ⟨j,?_⟩
  intro x _
  have hx : x=p := Subsingleton.elim _ _
  subst x
  exact hj

theorem exists_inside (W : X.left.Opens) (hW : ⊤ ≤ s ⁻¹ᵁ W) :
    ∃ j : AlgebraicGeometry.Crystalline.Cohomology.Base.SmoothProperEtaleCover.BaseSmoothProperEtaleCover.Index R X,
      ⊤ ≤ s ⁻¹ᵁ (W ⊓ AlgebraicGeometry.Crystalline.Cohomology.Base.ProperOrdinaryFormCharts.BaseSmoothProperOrdinaryFormCharts.opens R X j) := by
  obtain ⟨j,hj⟩ := exists_chart R X s
  exact ⟨j,fun x hx => ⟨hW hx,hj hx⟩⟩

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Intrinsic.SectionFormChart
