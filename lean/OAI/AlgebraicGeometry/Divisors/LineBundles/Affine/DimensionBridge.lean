import OAI.AlgebraicGeometry.Divisors.LineBundles.Deformation.Transcendence
import OAI.AlgebraicGeometry.Foundations.Scheme.TranscendenceDimension
import OAI.AlgebraicGeometry.Foundations.Scheme.OpenFunctionField
import OAI.AlgebraicGeometry.Foundations.Scheme.AffineSectionFiniteType

/-! # Dimension Bridge -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles.Affine.DimensionBridge.BundleCycles

noncomputable section

/-!
# LineBundleCycles: actual affine scalar maps and transcendence dimension

The canonical spectrum/global-sections isomorphism respects the scalar
action induced by the actual structure morphism. It therefore identifies
the scheme's function-field dimension with the coordinate ring's
transcendence degree, without an assumed scalar compatibility.
-/

open _root_.AlgebraicGeometry _root_.CategoryTheory _root_.TopologicalSpace

universe u
variable (k A : Type u) [Field k] [CommRing A] [Algebra k A]

/-- The spectrum/global-sections isomorphism over the actual coefficient field. -/
def specGlobalScalarAlgEquiv :
    letI := Foundations.Scheme.SpecScalarTransport.specSectionScalarAlgebra (Spec.map (CommRingCat.ofHom (algebraMap k A))) ⊤
    Γ(Spec (CommRingCat.of A), ⊤) ≃ₐ[k] A := by
  let a : CommRingCat.of k ⟶ CommRingCat.of A := CommRingCat.ofHom (algebraMap k A)
  let := Foundations.Scheme.SpecScalarTransport.specSectionScalarAlgebra (Spec.map a) ⊤
  refine { (Scheme.ΓSpecIso (CommRingCat.of A)).commRingCatIsoToRingEquiv with commutes' := ?_ }
  intro r
  have h := ConcreteCategory.congr_hom (Scheme.ΓSpecIso_naturality a)
    ((Scheme.ΓSpecIso (CommRingCat.of k)).inv r)
  change (Scheme.ΓSpecIso (CommRingCat.of A)).hom
      ((Spec.map a).appTop ((Scheme.ΓSpecIso (CommRingCat.of k)).inv r)) =
    a ((Scheme.ΓSpecIso (CommRingCat.of k)).hom ((Scheme.ΓSpecIso (CommRingCat.of k)).inv r)) at h
  have he : (Spec.map a).appLE ⊤ ⊤ le_top = (Spec.map a).appTop :=
    (Spec.map a).app_eq_appLE.symm
  change (Scheme.ΓSpecIso (CommRingCat.of A)).hom
      ((Spec.map a).appLE ⊤ ⊤ le_top ((Scheme.ΓSpecIso (CommRingCat.of k)).inv r)) = algebraMap k A r
  exact (congrArg (fun g => (Scheme.ΓSpecIso (CommRingCat.of A)).hom
      (g ((Scheme.ΓSpecIso (CommRingCat.of k)).inv r))) he).trans
    (h.trans (congrArg a (Iso.inv_hom_id_apply (Scheme.ΓSpecIso (CommRingCat.of k)) r)))

/-- The canonical dimension of an integral affine scheme equals its actual ring transcendence degree. -/
theorem schemeTranscendenceDimension_spec_algebra [IsDomain A] :
    Foundations.Scheme.TranscendenceDimension.schemeTranscendenceDimension (Spec.map (CommRingCat.ofHom (algebraMap k A))) =
      (Algebra.trdeg k A).toNat := by
  let f := Spec.map (CommRingCat.ofHom (algebraMap k A))
  have : Nonempty (⊤ : (Spec (CommRingCat.of A)).Opens) :=
    ⟨⟨Classical.choice (inferInstance : Nonempty (Spec (CommRingCat.of A))), trivial⟩⟩
  let := Foundations.Scheme.SpecScalarTransport.specSectionScalarAlgebra f ⊤
  exact (Foundations.Scheme.TranscendenceDimension.schemeTranscendenceDimension_eq_affineSections f ⊤ (isAffineOpen_top _)).trans
    (congrArg Cardinal.toNat (specGlobalScalarAlgEquiv k A).trdeg_eq)

end

end OAI.AlgebraicGeometry.Divisors.LineBundles.Affine.DimensionBridge.BundleCycles
