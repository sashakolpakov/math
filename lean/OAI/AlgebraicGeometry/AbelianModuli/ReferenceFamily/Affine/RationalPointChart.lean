import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Affine.OverMorphismAlgebra
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Open.ImmersionLiftFibers
import Mathlib.AlgebraicGeometry.Morphisms.Smooth

/-! # Rational Point Chart -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Affine.RationalPointChart

noncomputable section

/-! A rational point over a field has an actual affine neighborhood
over the original base, and the point factors through that neighborhood.
Smoothness is inherited from the original family. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

attribute [local implicit_reducible] EtaleSplittingAt.EtaleSplitting.affineOver

variable (k : Type) [Field k] (A : Over (Spec (.of k))) (p : EtaleSplittingAt.EtaleSplitting.affineOver k k ⟶ A)

structure AffineOverPointChart where
  source : Over (Spec (.of k))
  affine : IsAffine source.left
  inclusion : source ⟶ A
  openImmersion : IsOpenImmersion inclusion.left
  point : EtaleSplittingAt.EtaleSplitting.affineOver k k ⟶ source
  commutes : point ≫ inclusion = p

attribute [instance] AffineOverPointChart.affine AffineOverPointChart.openImmersion

theorem exists_affineOverPointChart : Nonempty (AffineOverPointChart k A p) := by
  let x : (EtaleSplittingAt.EtaleSplitting.affineOver k k).left := IsLocalRing.closedPoint k
  let : Subsingleton (EtaleSplittingAt.EtaleSplitting.affineOver k k).left := inferInstanceAs (Subsingleton (PrimeSpectrum k))
  obtain ⟨V, hV, hx, _⟩ := exists_isAffineOpen_mem_and_subset (X := A.left)
    (x := p.left x) (U := ⊤) (show p.left x ∈ (⊤ : A.left.Opens) from trivial)
  let U : Over (Spec (.of k)) := Over.mk (V.ι ≫ A.hom)
  let i : U ⟶ A := Over.homMk V.ι
  have hopen : IsOpenImmersion i.left := inferInstanceAs (IsOpenImmersion V.ι)
  have hr : Set.range p.left ⊆ Set.range i.left := by
    rintro _ ⟨t, rfl⟩
    have ht : t = x := Subsingleton.elim _ _
    exact ⟨⟨p.left t, ht.symm ▸ hx⟩, rfl⟩
  exact ⟨⟨U, hV, i, hopen, DualOpen.Lifts.overOpenLift i p hr, DualOpen.Lifts.overOpenLift_fac i p hr⟩⟩

instance affineOverPointChart_smooth [Smooth A.hom] (D : AffineOverPointChart k A p) :
    Smooth D.source.hom := by
  have h : Smooth (D.inclusion.left ≫ A.hom) := inferInstance
  exact D.inclusion.w ▸ h

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Affine.RationalPointChart
