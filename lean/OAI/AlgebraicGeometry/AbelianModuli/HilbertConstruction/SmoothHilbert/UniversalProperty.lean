import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.SmoothHilbert.PointEquivalence

/-! # Universal Property -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.SmoothHilbert.UniversalProperty

noncomputable section

/-! The actual smooth Hilbert universal family has the unique classification property on all test schemes. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

theorem smoothHilbertUniversalFamily_point
    (S : Scheme.{u}) (T : Over S) (n : ℕ) (P : Polynomial ℚ) (g : T ⟶ Parameter.smoothHilbertParameter S n P) :
    (Parameter.smoothHilbertUniversalFamily S n P).pullback g.left = (PointEquivalence.smoothHilbertParameterPointEquiv S T n P g).val :=
  (Hilbert.ParameterScheme.hilbertUniversalFamily S n P).pullback_comp (Parameter.smoothHilbertParameterInclusion S n P).left g.left

theorem smoothHilbertUniversalFamily_existsUnique
    {S : Scheme.{u}} {T : Over S} {n : ℕ} {P : Polynomial ℚ}
    (F : PointEquivalence.SmoothRelativeProjectiveHilbertFamily T.left n P) :
    ∃! g : T ⟶ Parameter.smoothHilbertParameter S n P, (Parameter.smoothHilbertUniversalFamily S n P).pullback g.left = F.val := by
  let e := PointEquivalence.smoothHilbertParameterPointEquiv S T n P
  refine ⟨e.symm F, (smoothHilbertUniversalFamily_point S T n P (e.symm F)).trans
    (congrArg Subtype.val (e.apply_symm_apply F)), ?_⟩
  intro g hg
  apply e.injective
  exact (Subtype.ext ((smoothHilbertUniversalFamily_point S T n P g).symm.trans hg)).trans
    (e.apply_symm_apply F).symm

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.SmoothHilbert.UniversalProperty
