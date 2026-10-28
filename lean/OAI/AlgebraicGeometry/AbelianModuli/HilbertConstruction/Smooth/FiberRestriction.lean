import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Smooth.FiberOpenSource
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Smooth.FiberCartesianComparison

/-! # Fiber Restriction -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Smooth.FiberRestriction

noncomputable section

/-! A smooth fiber remains smooth on simultaneous open restrictions of source and target. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

theorem smooth_fiber_resLE
    {X S : Scheme.{u}} (f : X ⟶ S) (U : S.Opens) (V : X.Opens) (e : V ≤ f ⁻¹ᵁ U)
    (x : V.toScheme) [Smooth (f.fiberToSpecResidueField (f (V.ι x)))] :
    Smooth ((f.resLE U V e).fiberToSpecResidueField ((f.resLE U V e) x)) := by
  let g := V.ι ≫ f
  let p := f.resLE U V e
  have hp : p ≫ U.ι = g := Scheme.Hom.resLE_comp_ι f e
  have h : IsPullback (𝟙 V.toScheme) p g U.ι :=
    IsPullback.of_horiz_isIso_mono ⟨(Category.id_comp g).trans hp.symm⟩
  have : Smooth (f.fiberToSpecResidueField (g x)) :=
    inferInstanceAs (Smooth (f.fiberToSpecResidueField (f (V.ι x))))
  have hg : Smooth (g.fiberToSpecResidueField (g x)) := FiberOpenSource.smooth_fiber_precomp_open f V.ι (g x)
  have he : U.ι (p x) = g x := congrArg (fun k : V.toScheme ⟶ S => k x) hp
  apply (FiberCartesianComparison.smooth_fiber_iff_of_isPullback _ p g U.ι h (p x)).mpr
  rw [he]
  exact hg

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Smooth.FiberRestriction
