import OAI.AlgebraicGeometry.HilbertScheme.Presentations.Proper.RelativeAmpleRestrictionVanishing
import OAI.AlgebraicGeometry.SheafCohomology.Cech.VerticalComparison
import Mathlib.AlgebraicGeometry.Morphisms.Affine

/-! # Finite Cover Ample Vanishing -/

namespace OAI.AlgebraicGeometry.HilbertScheme.Presentations.Proper.FiniteCoverAmpleVanishing

noncomputable section

/-! One power bound makes all inverse-image intersections of a finite
affine cover acyclic. Repeated tuple indices give only finitely many opens. -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry _root_.TopologicalSpace

namespace Cohomology

universe u

theorem finiteCover_relativelyAmple_eventually_acyclic
    {X Y : Scheme.{u}} [Y.IsSeparated] [IsLocallyNoetherian Y]
    (f : X ⟶ Y) [IsProper f] (L : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle X) (hL : L.IsRelativelyAmple f)
    {ι : Type u} [Fintype ι] (U : ι → Y.Opens) (hUa : ∀ i, IsAffineOpen (U i)) :
    ∃ b : ℕ, ∀ n : ℕ, b ≤ n →
      SheafCohomology.Cech.VerticalComparison.TopCat.Sheaf.CechIntersectionsAcyclic (fun i => f ⁻¹ᵁ U i)
        ((SheafOfModules.toSheaf X.ringCatSheaf).obj (L.tensorPower n).sheaf) := by
  classical
  let J := {s : Finset ι // s.Nonempty}
  let V (j : J) : Y.Opens := ⨅ i ∈ j.val, U i
  have hVa (j : J) : IsAffineOpen (V j) :=
    IsAffineOpen.biInf (j.val : Set ι) j.val.finite_toSet j.property (fun i _ => hUa i)
  have hv (j : J) := RelativeAmpleRestrictionVanishing.Cohomology.relativelyAmple_restrictedPowers_eventually_vanishing f L hL (V j) (hVa j)
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
    ((SheafCohomology.Cech.SchemeModuleBaseBasic.Scheme.Hom.preimage_cechIntersection f) U p i).symm.trans (congrArg (fun W => f ⁻¹ᵁ W) hj)
  change Subsingleton (SheafCohomology.AffineH.Projective.H
    ((L.tensorPower n).sheaf.restrict (∏ᶜ fun k : Fin (p + 1) => f ⁻¹ᵁ U (i k)).ι) (q + 1))
  rw [hpre]
  exact hb j n ((Finset.le_sup (f := b) (Finset.mem_univ j)).trans hn) (q + 1) (Nat.zero_lt_succ q)

end Cohomology

end

end OAI.AlgebraicGeometry.HilbertScheme.Presentations.Proper.FiniteCoverAmpleVanishing
