import OAI.AlgebraicGeometry.Resolution.Blowups.Global.AtlasFromAffineCover
import OAI.AlgebraicGeometry.Resolution.Blowups.Open.AffineBoundaryRestriction

/-! # Mixed Atlas Open Gluing -/

namespace OAI.AlgebraicGeometry.Resolution.Blowups.Global

noncomputable section

/-! Admissible-center atlases glue from actual open covers with the fixed native center and boundary ideals. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

def CanonicalBoundaryAtlas.Construction.GlobalMixedCenterAtlas.ofOpenCover
    {X : Scheme} (f : X ⟶ Foundations.Scheme.ProjectiveSpace.complexBase) (I : X.IdealSheafData)
    {β : Type} (D : β → X.IdealSheafData) (C : X.OpenCover)
    (A : ∀ i, CanonicalBoundaryAtlas.Construction.GlobalMixedCenterAtlas (C.f i ≫ f) (I.comap (C.f i))
      (fun l => (D l).comap (C.f i))) : CanonicalBoundaryAtlas.Construction.GlobalMixedCenterAtlas f I D := by
  let B (i : C.I₀) := MonomialBoundaryAtlas.Construction.chosenAffineSpecCover (A i).opens (A i).cover
  let E := C.bind (fun i => (B i).openCover)
  let F : X.AffineOpenCover := {
    I₀ := Σ i, (A i).indices
    X := fun r => .of Γ(C.X r.1, (A r.1).opens r.2)
    f := fun r => ((A r.1).opens r.2).2.fromSpec ≫ C.f r.1
    map_prop := fun r => by
      let : IsOpenImmersion ((A r.1).opens r.2).2.fromSpec :=
        ((A r.1).opens r.2).2.isOpenImmersion_fromSpec
      infer_instance
    idx := Scheme.Cover.idx E
    covers := Scheme.Cover.covers E }
  let : ∀ r : F.I₀, Algebra ℂ (F.X r) :=
    fun r => Smooth.DifferentialIdealSheaf.Construction.affineComplexAlgebra (C.f r.1 ≫ f) ((A r.1).opens r.2)
  apply CanonicalBoundaryAtlas.Construction.GlobalMixedCenterAtlas.ofAffineCover f I D F
    (fun r => ?_) (fun r => (I.comap (C.f r.1)).ideal ((A r.1).opens r.2))
    (fun r => (A r.1).equations r.2) (fun r => (A r.1).divided r.2)
  · intro r
    change I.comap (((A r.1).opens r.2).2.fromSpec ≫ C.f r.1) = _
    rw [Scheme.IdealSheafData.comap_comp]
    exact Affine.IdealSheafIdentification.Construction.idealSheaf_comap_fromSpec_eq_quotient_kernel _ _
  · intro r l
    change (D l).comap (((A r.1).opens r.2).2.fromSpec ≫ C.f r.1) = _
    rw [Scheme.IdealSheafData.comap_comp, Affine.IdealSheafIdentification.Construction.idealSheaf_comap_fromSpec_eq_quotient_kernel,
      (A r.1).component r.2 l]
  · intro r
    exact (A r.1).boundary r.2
  · intro r
    exact (A r.1).center r.2
  · change (((A r.1).opens r.2).2.fromSpec ≫ C.f r.1) ≫ f = _
    rw [Category.assoc]
    exact (Affine.ComplexNaturality.Construction.affineComplexScalars_spec (C.f r.1 ≫ f) ((A r.1).opens r.2)).symm

end

end OAI.AlgebraicGeometry.Resolution.Blowups.Global
