import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Affine.SchemeSmoothFiberCriterion
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Smooth.FiberRestriction

/-! # Fiber Point Criterion -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Smooth.FiberPointCriterion

noncomputable section

/-! Every point of a smooth fiber of a flat finitely presented morphism lies in its smooth locus. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace

universe u

theorem stalk_formallySmooth_of_smooth_fiber
    {X S : Scheme.{u}} (f : X ⟶ S) [Flat f] [LocallyOfFinitePresentation f]
    (x : X) [Smooth (f.fiberToSpecResidueField (f x))] : (f.stalkMap x).hom.FormallySmooth := by
  obtain ⟨U, hU, hfx, _⟩ := Opens.isBasis_iff_nbhd.mp S.isBasis_affineOpens (Opens.mem_top (f x))
  change S.Opens at U
  obtain ⟨V, hV, hx, e⟩ := Opens.isBasis_iff_nbhd.mp X.isBasis_affineOpens
    (show x ∈ f ⁻¹ᵁ U from hfx)
  change X.Opens at V
  have : IsAffine U.toScheme := hU
  have : IsAffine V.toScheme := hV
  let y : V.toScheme := ⟨x, hx⟩
  have : Smooth (f.fiberToSpecResidueField (f (V.ι y))) :=
    inferInstanceAs (Smooth (f.fiberToSpecResidueField (f x)))
  have : Smooth ((f.resLE U V e).fiberToSpecResidueField ((f.resLE U V e) y)) :=
    FiberRestriction.smooth_fiber_resLE f U V e y
  have h := Affine.SchemeSmoothFiberCriterion.affineScheme_stalk_formallySmooth_of_smooth_fiber (f.resLE U V e) y
  exact (RingHom.FormallySmooth.respectsIso.arrow_mk_iso_iff (Scheme.Hom.resLEStalkMap f e y)).mp h

theorem fiber_smoothLocus_of_smooth_fiber
    {X S : Scheme.{u}} (f : X ⟶ S) [Flat f] [LocallyOfFinitePresentation f]
    (s : S) [Smooth (f.fiberToSpecResidueField s)] (x : X) (hx : f x = s) : x ∈ f.smoothLocus := by
  have : Smooth (f.fiberToSpecResidueField (f x)) := hx.symm ▸ (inferInstanceAs (Smooth (f.fiberToSpecResidueField s)))
  exact stalk_formallySmooth_of_smooth_fiber f x

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Smooth.FiberPointCriterion
