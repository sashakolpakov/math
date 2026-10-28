import OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Evaluated.ParameterPoints
import Mathlib.CategoryTheory.Monoidal.Cartesian.Over

/-! # Split Point Surjectivity -/

namespace OAI.AlgebraicGeometry.Isogenies.NeighborCounting.SplitPointSurjectivity.Lifts

noncomputable section

/-! A surjective morphism between evaluated finite schemes is surjective
on rational labels. This derives the point-level component surjectivity
used to construct the generic linear section. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.CategoryTheory.Limits
open _root_.CategoryTheory.MonoidalCategory

universe u

variable {k : Type u} [Field k] {I J : Type u}

def splitLabelPoint {X : Over (Spec (.of k))}
    (e : AbelianModuli.HilbertConstruction.ConstantScheme.Iff.constantScheme (Spec (.of k)) I ≅ X) (i : I) : (𝟙_ (Over (Spec (.of k)))) ⟶ X :=
  (show Over.mk (𝟙 (Spec (.of k))) ⟶ AbelianModuli.HilbertConstruction.ConstantScheme.Iff.constantScheme (Spec (.of k)) I from
    Over.homMk (Sigma.ι (fun _ : I ↦ Spec (.of k)) i) (AbelianModuli.HilbertConstruction.ConstantScheme.Iff.constantScheme_ι_hom i)) ≫ e.hom

theorem splitLabelPoint_covers {X : Over (Spec (.of k))}
    (e : AbelianModuli.HilbertConstruction.ConstantScheme.Iff.constantScheme (Spec (.of k)) I ≅ X) (x : X.left) :
    ∃ i, (splitLabelPoint e i).left (IsLocalRing.closedPoint k) = x := by
  obtain ⟨⟨i, t⟩, ht⟩ := (sigmaMk (fun _ : I ↦ Spec (.of k))).surjective (e.inv.left x)
  refine ⟨i, ?_⟩
  have hpoint : IsLocalRing.closedPoint k = t := Subsingleton.elim _ _
  change e.hom.left (Sigma.ι (fun _ : I ↦ Spec (.of k)) i (IsLocalRing.closedPoint k)) = x
  rw [hpoint, ← sigmaMk_mk, ht]
  have he : e.inv.left ≫ e.hom.left = 𝟙 X.left := congrArg Over.Hom.left e.inv_hom_id
  exact congrArg (fun f : X.left ⟶ X.left ↦ f x) he

theorem splitSource_constantTarget_points_surjective {X : Over (Spec (.of k))}
    (e : AbelianModuli.HilbertConstruction.ConstantScheme.Iff.constantScheme (Spec (.of k)) I ≅ X)
    (f : X ⟶ AbelianModuli.HilbertConstruction.ConstantScheme.Iff.constantScheme (Spec (.of k)) J) [Surjective f.left] :
    Function.Surjective (fun a : (𝟙_ (Over (Spec (.of k)))) ⟶ X ↦ a ≫ f) := by
  intro b
  obtain ⟨x, hx⟩ := f.left.surjective (b.left (IsLocalRing.closedPoint k))
  obtain ⟨i, hi⟩ := splitLabelPoint_covers e x
  refine ⟨splitLabelPoint e i, ?_⟩
  apply (AbelianModuli.HilbertConstruction.ConstantScheme.Iff.constantSchemePointsEquiv (Spec (.of k)) J (𝟙_ (Over (Spec (.of k))))).injective
  apply LocallyConstant.ext
  intro t
  have ht : t = IsLocalRing.closedPoint k :=
    @Subsingleton.elim (Spec (.of k)) inferInstance t _
  subst t
  exact congrArg (AbelianModuli.HilbertConstruction.ConstantScheme.Iff.constantSchemeIndex (Spec (.of k)) J) ((congrArg f.left hi).trans hx)

theorem split_points_surjective {X Y : Over (Spec (.of k))}
    (eX : AbelianModuli.HilbertConstruction.ConstantScheme.Iff.constantScheme (Spec (.of k)) I ≅ X)
    (eY : AbelianModuli.HilbertConstruction.ConstantScheme.Iff.constantScheme (Spec (.of k)) J ≅ Y)
    (f : X ⟶ Y) [Surjective f.left] :
    Function.Surjective (fun a : (𝟙_ (Over (Spec (.of k)))) ⟶ X ↦ a ≫ f) := by
  have : IsIso eY.inv.left := (Over.forget _).map_isIso eY.inv
  have : Surjective (f ≫ eY.inv).left := inferInstanceAs (Surjective (f.left ≫ eY.inv.left))
  intro b
  obtain ⟨a, ha⟩ := splitSource_constantTarget_points_surjective eX (f ≫ eY.inv) (b ≫ eY.inv)
  refine ⟨a, (cancel_mono eY.inv).mp ?_⟩
  exact (Category.assoc _ _ _).trans ha

end

end OAI.AlgebraicGeometry.Isogenies.NeighborCounting.SplitPointSurjectivity.Lifts
