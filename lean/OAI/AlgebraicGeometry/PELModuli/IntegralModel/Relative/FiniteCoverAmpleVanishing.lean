import OAI.AlgebraicGeometry.PELModuli.IntegralModel.AmpleAllVanishing
import OAI.AlgebraicGeometry.Quotients.FiniteDescent.TensorPullback
import OAI.AlgebraicGeometry.SheafCohomology.Cech.VerticalComparison
import Mathlib.AlgebraicGeometry.Morphisms.Affine

/-! # Finite Cover Ample Vanishing -/

namespace OAI.AlgebraicGeometry.PELModuli.IntegralModel.Relative.FiniteCoverAmpleVanishing

noncomputable section

section

/-! Relative Serre vanishing on every actual inverse image of an
affine base open, stated for restrictions of the original tensor powers. -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open _root_.CategoryTheory _root_.AlgebraicGeometry

theorem relativelyAmple_restrictedPowers_eventually_vanishing
    {X Y : Scheme.{0}} [IsLocallyNoetherian Y]
    (f : X ⟶ Y) [IsProper f] (L : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle X) (hL : L.IsRelativelyAmple f)
    (U : Y.Opens) (hU : IsAffineOpen U) :
    ∃ b : ℕ, ∀ n : ℕ, b ≤ n → ∀ q : ℕ, 0 < q →
      Subsingleton (SheafCohomology.AffineH.Projective.H ((L.tensorPower n).sheaf.restrict (f ⁻¹ᵁ U).ι) q) := by
  have : IsAffine U.toScheme := hU
  have : IsLocallyNoetherian U.toScheme := inferInstance
  have : IsNoetherianRing Γ(U.toScheme, ⊤) :=
    IsLocallyNoetherian.component_noetherian ⟨⊤, isAffineOpen_top _⟩
  let V := f ⁻¹ᵁ U
  obtain ⟨b, hb⟩ := AmpleAllVanishing.ample_lineBundle_eventually_vanishing
    (f ∣_ U) (L.pullback V.ι) (hL U hU)
  refine ⟨b, fun n hn q hq => ?_⟩
  have : Subsingleton (SheafCohomology.AffineH.Projective.H ((L.pullback V.ι).tensorPower n).sheaf q) := hb n hn q hq
  let e : (L.tensorPower n).sheaf.restrict V.ι ≅ ((L.pullback V.ι).tensorPower n).sheaf :=
    (Scheme.Modules.restrictFunctorIsoPullback V.ι).app (L.tensorPower n).sheaf ≪≫
      Quotients.FiniteDescent.TensorPullback.Construction.TensorPullbackMap.iso V.ι L n
  exact (ConcreteCategory.bijective_of_isIso ((SheafCohomology.AffineH.Projective.zariskiFunctor V.toScheme q).map e.hom)).injective.subsingleton

end

/-! One power bound makes all inverse-image intersections of a finite
affine cover acyclic. Repeated tuple indices give only finitely many opens. -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry _root_.TopologicalSpace

theorem finiteCover_relativelyAmple_eventually_acyclic
    {X Y : Scheme.{0}} [Y.IsSeparated] [IsLocallyNoetherian Y]
    (f : X ⟶ Y) [IsProper f] (L : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle X) (hL : L.IsRelativelyAmple f)
    {ι : Type} [Fintype ι] (U : ι → Y.Opens) (hUa : ∀ i, IsAffineOpen (U i)) :
    ∃ b : ℕ, ∀ n : ℕ, b ≤ n →
      SheafCohomology.Cech.VerticalComparison.TopCat.Sheaf.CechIntersectionsAcyclic (fun i => f ⁻¹ᵁ U i)
        ((SheafOfModules.toSheaf X.ringCatSheaf).obj (L.tensorPower n).sheaf) := by
  classical
  let J := {s : Finset ι // s.Nonempty}
  let V (j : J) : Y.Opens := ⨅ i ∈ j.val, U i
  have hVa (j : J) : IsAffineOpen (V j) :=
    IsAffineOpen.biInf (j.val : Set ι) j.val.finite_toSet j.property (fun i _ => hUa i)
  have hv (j : J) := relativelyAmple_restrictedPowers_eventually_vanishing f L hL (V j) (hVa j)
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

end

end OAI.AlgebraicGeometry.PELModuli.IntegralModel.Relative.FiniteCoverAmpleVanishing
