import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Rational.ProjectivePolarizationIntrinsic
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.GraphPower.PolarizationSubfunctor
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.CompositeParameterPoints
import OAI.AlgebraicGeometry.HilbertScheme.Presentations.SubfunctorRepresentations

/-! # Projective Polarization Representation -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Rational.ProjectivePolarizationRepresentation.RationalProjectivePolarizationLocus

noncomputable section

/-! The actual rational polarization locus represents the original
normalized graph-power subfunctor on an affine parameter chart. All
factorizations and the natural isomorphism use arbitrary test schemes. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

variable {R : Type} [CommRing R] [IsNoetherianRing R] {g : ℕ}
    (A : Abelian.Schemes.AbelianScheme g (Spec (.of R))) (P : Projective.ProjectivePresentations.ProjectivePresentation A.scheme)
    (L : Line.Bundles.LineBundle A.scheme.left) (qS : Spec (.of R) ⟶ Spec (.of ℚ)) (hL : L.IsAmple)
    (d : ℕ) (hd : 0 < d) (δ : Fin g → ℕ) (hδ : ∀ i, 0 < δ i)
    {B : Scheme} (b : Spec (.of R) ⟶ B)

def relativeParameter : Over B :=
  (Over.map b).obj (ProjectivePolarizationParameter.RationalProjectivePolarizationLocus.parameter A P L qS hL d hd δ hδ)

def relativeInclusion : relativeParameter A P L qS hL d hd δ hδ b ⟶ Over.mk b :=
  CompositeParameterPoints.compositeParameterProjection (Over.mk b) (ProjectivePolarizationParameter.RationalProjectivePolarizationLocus.parameter A P L qS hL d hd δ hδ)

instance relativeInclusion_mono : Mono (relativeInclusion A P L qS hL d hd δ hδ b) := by
  let : Mono (relativeInclusion A P L qS hL d hd δ hδ b).left :=
    inferInstanceAs (Mono (ProjectivePolarizationParameter.RationalProjectivePolarizationLocus.parameter A P L qS hL d hd δ hδ).hom)
  exact Over.mono_of_mono_left _

instance relativeInclusion_locallyOfFiniteType :
    LocallyOfFiniteType (relativeInclusion A P L qS hL d hd δ hδ b).left :=
  inferInstanceAs (LocallyOfFiniteType (ProjectivePolarizationParameter.RationalProjectivePolarizationLocus.parameter A P L qS hL d hd δ hδ).hom)

instance relativeInclusion_quasiCompact :
    QuasiCompact (relativeInclusion A P L qS hL d hd δ hδ b).left :=
  inferInstanceAs (QuasiCompact (ProjectivePolarizationParameter.RationalProjectivePolarizationLocus.parameter A P L qS hL d hd δ hδ).hom)

variable {N : ℕ} (level : A.FullLevel N)

theorem relativeParameter_lifts_iff (T : Over B) (x : T ⟶ Over.mk b) :
    (∃ y : T ⟶ relativeParameter A P L qS hL d hd δ hδ b,
      y ≫ relativeInclusion A P L qS hL d hd δ hδ b = x) ↔
    GraphPower.PolarizationSubfunctor.GraphPowerPolarizationPoint (Over.mk b) δ (⟨A, level⟩ : Level.Data.AbelianSchemeWithFullLevel g N _)
      (A.zeroNormalizedBundle L) d x := by
  have h := ProjectivePolarizationIntrinsic.RationalProjectivePolarizationLocus.parameter_hasPoint_iff_graphPowerEnhancement A P L qS hL d hd δ hδ
    level (Over.mk x.left)
  let e := CompositeParameterPoints.compositeParameterFiberEquiv (Over.mk b) (ProjectivePolarizationParameter.RationalProjectivePolarizationLocus.parameter A P L qS hL d hd δ hδ) T x
  constructor
  · rintro ⟨y, hy⟩
    exact h.mp ⟨e ⟨y, hy⟩⟩
  · intro hx
    obtain ⟨a⟩ := h.mpr hx
    exact ⟨(e.symm a).val, (e.symm a).property⟩

theorem relativeParameter_represents :
    ∃ e : yoneda.obj (relativeParameter A P L qS hL d hd δ hδ b) ≅
        (GraphPower.PolarizationSubfunctor.graphPowerPolarizationSubfunctor (Over.mk b) δ
          (⟨A, level⟩ : Level.Data.AbelianSchemeWithFullLevel g N _) (A.zeroNormalizedBundle L) d).toFunctor,
      e.hom ≫ (GraphPower.PolarizationSubfunctor.graphPowerPolarizationSubfunctor (Over.mk b) δ
          (⟨A, level⟩ : Level.Data.AbelianSchemeWithFullLevel g N _) (A.zeroNormalizedBundle L) d).ι =
        yoneda.map (relativeInclusion A P L qS hL d hd δ hδ b) := by
  apply HilbertScheme.Presentations.SubfunctorRepresentations.subfunctor_representation_of_lifts
  intro T x
  exact (relativeParameter_lifts_iff A P L qS hL d hd δ hδ b level T x).symm

def universalEnhancement :
    GraphPower.PolarizationEnhancementData.GraphPowerPolarizationEnhancement δ
      ((⟨A, level⟩ : Level.Data.AbelianSchemeWithFullLevel g N _).pullback
        (ProjectivePolarizationParameter.RationalProjectivePolarizationLocus.parameter A P L qS hL d hd δ hδ).hom)
      ((A.zeroNormalizedBundle L).pullback
        (pullback.fst A.scheme.hom (ProjectivePolarizationParameter.RationalProjectivePolarizationLocus.parameter A P L qS hL d hd δ hδ).hom)) d where
  dual := (ProjectivePolarizationParameter.RationalProjectivePolarizationLocus.dualData A P L qS hL).pullback (ProjectivePolarizationParameter.RationalProjectivePolarizationLocus.parameter A P L qS hL d hd δ hδ).hom
  polarization := ProjectivePolarizationParameter.RationalProjectivePolarizationLocus.polarization A P L qS hL d hd δ hδ
  powerIso := ⟨ProjectivePolarizationParameter.RationalProjectivePolarizationLocus.universalGraphPowerIso A P L qS hL d hd δ hδ⟩

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Rational.ProjectivePolarizationRepresentation.RationalProjectivePolarizationLocus
