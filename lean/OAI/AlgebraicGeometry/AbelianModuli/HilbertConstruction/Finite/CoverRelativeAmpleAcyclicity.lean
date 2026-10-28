import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Relative.AmpleRestrictionAcyclicity
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Affine.PushforwardZariskiComparison

/-! # Cover Relative Ample Acyclicity -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Finite.CoverRelativeAmpleAcyclicity

noncomputable section

/- Adapted from ProperFiniteCoverAmpleVanishing, using HilbertConstruction's independently checked Ext cohomology and default computation limits. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry _root_.TopologicalSpace
universe u

theorem finiteCover_relativelyAmple_eventually_acyclic
    {X Y : Scheme.{u}} [Y.IsSeparated] [IsLocallyNoetherian Y]
    (f : X ⟶ Y) [IsProper f] (L : Line.Bundles.LineBundle X) (hL : L.IsRelativelyAmple f)
    {ι : Type u} [Fintype ι] (U : ι → Y.Opens) (hUa : ∀ i, IsAffineOpen (U i)) :
    ∃ b : ℕ, ∀ n : ℕ, b ≤ n →
      Cech.AcyclicIntersectionColumns.IntrinsicCech.CechIntersectionsAcyclic (fun i => f ⁻¹ᵁ U i)
        ((SheafOfModules.toSheaf X.ringCatSheaf).obj (L.tensorPower n).sheaf) := by
  classical
  let J := {s : Finset ι // s.Nonempty}
  let V (j : J) : Y.Opens := ⨅ i ∈ j.val, U i
  have hVa (j : J) : IsAffineOpen (V j) :=
    IsAffineOpen.biInf (j.val : Set ι) j.val.finite_toSet j.property (fun i _ => hUa i)
  have hv (j : J) := Relative.AmpleRestrictionAcyclicity.relativelyAmple_restrictedPowers_eventually_acyclic f L hL (V j) (hVa j)
  choose b hb using hv
  let B := Finset.univ.sup b
  refine ⟨B, fun n hn p i q => ?_⟩
  let j : J := ⟨Finset.univ.image i, by
    exact Finset.Nonempty.image ⟨0, Finset.mem_univ _⟩ i⟩
  have hj : (∏ᶜ fun k : Fin (p + 1) => U (i k)) = V j := by
    rw [show (∏ᶜ fun k : Fin (p + 1) => U (i k)) = ⨅ k, U (i k) from
      (IsLimit.conePointUniqueUpToIso (limit.isLimit _) (Preorder.isLimitIInf _)).to_eq]
    simp only [V, j, Finset.iInf_finset_image, Finset.mem_univ, iInf_true]
  have hpre : (∏ᶜ fun k : Fin (p + 1) => f ⁻¹ᵁ U (i k)) = f ⁻¹ᵁ V j :=
    (CoefficientCech.PushforwardFactors.preimageCechIntersection f U p i).symm.trans (congrArg (fun W => f ⁻¹ᵁ W) hj)
  change Subsingleton (Zariski.Cohomology.ZariskiCohomology.H
    ((L.tensorPower n).sheaf.restrict (∏ᶜ fun k : Fin (p + 1) => f ⁻¹ᵁ U (i k)).ι) (q + 1))
  rw [hpre]
  exact hb j n ((Finset.le_sup (f := b) (Finset.mem_univ j)).trans hn) q

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Finite.CoverRelativeAmpleAcyclicity
