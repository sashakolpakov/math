import OAI.NumberTheory.PadicHodge.GeometricComparison.DeRham.Functor
import OAI.NumberTheory.PadicHodge.GeometricComparison.DeRham.FiltrationPullback

/-! # Iso Filtration General -/

namespace OAI.NumberTheory.PadicHodge.GeometricComparison.DeRham.IsoFiltrationGeneral

noncomputable section

/-! Actual inverse pullbacks identify Hodge filtrations under a scheme isomorphism without a finiteness assumption. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

variable {R : Type} [CommRing R] {X Y : Over (Spec (CommRingCat.of R))}
  (f : X ⟶ Y) [IsIso f]

theorem pullback_inv_apply (n : ℕ) (x : AlgebraicGeometry.Crystalline.Cohomology.DeRhamGlobalId.DeRhamGlobal.cohomology R X n) :
    Int.pullback f n (Int.pullback (inv f) n x) = x := by
  have h := congrArg (fun T => T x) (Composition.pullback_comp f (inv f) n)
  rw [IsIso.hom_inv_id, Functor.pullback_id] at h
  exact h

theorem isoPullback_filtration_without_finiteness (n : ℕ) (r : ℤ) :
    (AlgebraicGeometry.Crystalline.Cohomology.HodgeFiltrationD.HodgeFiltration.filtration R Y n r).map (IsoCohomology.isoPullback f n).toLinearMap =
      AlgebraicGeometry.Crystalline.Cohomology.HodgeFiltrationD.HodgeFiltration.filtration R X n r := by
  rw [IsoCohomology.isoPullback_toLinearMap]
  apply le_antisymm (FiltrationPullback.filtration_pullback f n r)
  intro x hx
  refine ⟨Int.pullback (inv f) n x, ?_, pullback_inv_apply f n x⟩
  exact FiltrationPullback.filtration_pullback (inv f) n r ⟨x, hx, rfl⟩

end

end OAI.NumberTheory.PadicHodge.GeometricComparison.DeRham.IsoFiltrationGeneral
