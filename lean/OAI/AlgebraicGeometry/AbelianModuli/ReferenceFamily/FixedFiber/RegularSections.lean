import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Affine.PresentationRegularSections
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.FixedFiber.CoordinateProjection
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.FixedFiber.DerivationPresheaf
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Regular.SectionTransport

/-! # Regular Sections -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.FixedFiber.RegularSections

noncomputable section

/-! Fixed-fiber tensor coefficients are the original regular
sections on the corresponding inverse-image opens, compatibly with
restriction and the actual base constants. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped TensorProduct

attribute [local implicit_reducible] AffineDiagram.fixedFiberTensorDiagram AffineDiagram.fixedFiberTensorAlgebras
attribute [local implicit_reducible] Affine.OpenDiagram.familyAffineCoordinateFunctor HilbertConstruction.Affine.CoordinateFunctor.affineCoordinateFunctor HilbertConstruction.AlgebraTensorFunctor.algebraTensorFunctor

variable (R k : Type) [CommRing R] [CommRing k] [Algebra R k]
    (X : Over (Spec (.of R)))

def fixedFiberRegularSectionEquiv (V : X.left.affineOpens) :
    (k ⊗[R] Family.AffineTangentLifts.familyAffineRing R X V) ≃+*
      Γ(((Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap R k)))).obj X).left,
        CoordinateProjection.fixedFiberAffineOpen R k X V) := by
  let G := (Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap R k)))).obj X
  let B := CommAlgCat.of k (k ⊗[R] Family.AffineTangentLifts.familyAffineRing R X V)
  let i : EtaleSplittingAt.EtaleSplitting.affineOver k B ⟶ G := AffineDiagram.fixedFiberTensorInclusion R k X V
  have : IsOpenImmersion i.left := AffineDiagram.fixedFiberTensorInclusion_open R k X V
  exact (Affine.PresentationRegularSections.affinePresentationRegularSectionEquiv k B G i).trans
    (Regular.SectionTransport.regularSectionTransport (CoordinateProjection.fixedFiberTensorInclusion_range R k X V))

theorem fixedFiberRegularSectionEquiv_restrict {V W : X.left.affineOpens} (h : V.1 ≤ W.1)
    (a : k ⊗[R] Family.AffineTangentLifts.familyAffineRing R X W) :
    fixedFiberRegularSectionEquiv R k X V (DerivationPresheaf.fixedFiberTensorRestriction R k X h a) =
      ((Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap R k)))).obj X).left.presheaf.map
        (homOfLE ((CoordinateProjection.fixedFamilyProjection R k X).preimage_mono h)).op (fixedFiberRegularSectionEquiv R k X W a) := by
  let G := (Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap R k)))).obj X
  let BV := CommAlgCat.of k (k ⊗[R] Family.AffineTangentLifts.familyAffineRing R X V)
  let BW := CommAlgCat.of k (k ⊗[R] Family.AffineTangentLifts.familyAffineRing R X W)
  let iV : EtaleSplittingAt.EtaleSplitting.affineOver k BV ⟶ G := AffineDiagram.fixedFiberTensorInclusion R k X V
  let iW : EtaleSplittingAt.EtaleSplitting.affineOver k BW ⟶ G := AffineDiagram.fixedFiberTensorInclusion R k X W
  have : IsOpenImmersion iV.left := AffineDiagram.fixedFiberTensorInclusion_open R k X V
  have : IsOpenImmersion iW.left := AffineDiagram.fixedFiberTensorInclusion_open R k X W
  have hR : iV.left.opensRange ≤ iW.left.opensRange := by
    change (AffineDiagram.fixedFiberTensorInclusion R k X V).left.opensRange ≤ (AffineDiagram.fixedFiberTensorInclusion R k X W).left.opensRange
    rw [CoordinateProjection.fixedFiberTensorInclusion_range, CoordinateProjection.fixedFiberTensorInclusion_range]
    exact (CoordinateProjection.fixedFamilyProjection R k X).preimage_mono h
  have hn := Affine.PresentationRegularSections.affinePresentationRegularSectionEquiv_natural k BW G iW BV iV
    (DerivationPresheaf.fixedFiberTensorRestriction R k X h) (AffineDiagram.fixedFiberTensorInclusion_natural R k X (homOfLE h)) hR a
  exact (congrArg (Regular.SectionTransport.regularSectionTransport (CoordinateProjection.fixedFiberTensorInclusion_range R k X V)) hn).trans
    (Regular.SectionTransport.regularSectionTransport_restrict (CoordinateProjection.fixedFiberTensorInclusion_range R k X W)
      (CoordinateProjection.fixedFiberTensorInclusion_range R k X V) hR ((CoordinateProjection.fixedFamilyProjection R k X).preimage_mono h)
      (Affine.PresentationRegularSections.affinePresentationRegularSectionEquiv k BW G iW a))

theorem fixedFiberRegularSectionEquiv_constant (V : X.left.affineOpens) (c : k) :
    fixedFiberRegularSectionEquiv R k X V
      (algebraMap k (k ⊗[R] Family.AffineTangentLifts.familyAffineRing R X V) c) =
      ((Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap R k)))).obj X).left.presheaf.map
        (homOfLE (show CoordinateProjection.fixedFiberAffineOpen R k X V ≤ ⊤ from le_top)).op
        (((Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap R k)))).obj X).hom.appTop
          ((Scheme.ΓSpecIso (.of k)).inv c)) := by
  let G := (Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap R k)))).obj X
  let B := CommAlgCat.of k (k ⊗[R] Family.AffineTangentLifts.familyAffineRing R X V)
  let i : EtaleSplittingAt.EtaleSplitting.affineOver k B ⟶ G := AffineDiagram.fixedFiberTensorInclusion R k X V
  have : IsOpenImmersion i.left := AffineDiagram.fixedFiberTensorInclusion_open R k X V
  have hc := Affine.PresentationRegularSections.affinePresentationRegularSectionEquiv_constant k B G i c
  exact (congrArg (Regular.SectionTransport.regularSectionTransport (CoordinateProjection.fixedFiberTensorInclusion_range R k X V)) hc).trans
    (Regular.SectionTransport.regularSectionTransport_restrict rfl (CoordinateProjection.fixedFiberTensorInclusion_range R k X V) le_top le_top
      (G.hom.appTop ((Scheme.ΓSpecIso (.of k)).inv c)))

theorem fixedFiberRegularSectionEquiv_smul (V : X.left.affineOpens) (c : k)
    (a : k ⊗[R] Family.AffineTangentLifts.familyAffineRing R X V) :
    fixedFiberRegularSectionEquiv R k X V (c • a) =
      ((Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap R k)))).obj X).left.presheaf.map
        (homOfLE (show CoordinateProjection.fixedFiberAffineOpen R k X V ≤ ⊤ from le_top)).op
        (((Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap R k)))).obj X).hom.appTop
          ((Scheme.ΓSpecIso (.of k)).inv c)) * fixedFiberRegularSectionEquiv R k X V a := by
  rw [Algebra.smul_def, map_mul, fixedFiberRegularSectionEquiv_constant]

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.FixedFiber.RegularSections
