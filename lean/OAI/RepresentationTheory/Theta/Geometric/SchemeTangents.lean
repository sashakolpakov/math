import OAI.RepresentationTheory.Theta.Geometric.RegularTangent
import OAI.RepresentationTheory.Theta.Geometric.TangentNeighborhoods
import OAI.RepresentationTheory.Theta.Geometric.TangentSourcesBased

/-! # Scheme Tangents -/

namespace OAI.RepresentationTheory.Theta.Geometric.SchemeTangents

noncomputable section

section

/-! Actual scheme dual-number points at a complex base point are recovered
from any smooth affine neighborhood and its regular analytic chart. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

def schemeTangentPoints (X : Over AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.complexBase) (p : AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X) :=
  {f : AlgebraicGeometry.AbelianModuli.ReferenceFamily.LieRanks.dualNumberTest ℂ ⟶ X // AlgebraicGeometry.AbelianModuli.ReferenceFamily.LieRanks.dualNumberOrigin ℂ ≫ f = p}

def complexDualNumberIso : AlgebraicGeometry.Foundations.Scheme.AffineComplexPoints.affineSchemeOver ℂ (DualNumber ℂ) ≅ AlgebraicGeometry.AbelianModuli.ReferenceFamily.LieRanks.dualNumberTest ℂ :=
  Over.isoMk (Iso.refl _) (by
    change 𝟙 (Spec (.of (DualNumber ℂ))) ≫
      Spec.map (CommRingCat.ofHom (algebraMap ℂ (DualNumber ℂ))) = _
    rw [Category.id_comp]
    rfl)

theorem affineTangentOrigin_native :
    AlgebraicGeometry.Foundations.Scheme.AffineComplexPoints.affineComplexBaseIso.hom ≫ AlgebraicGeometry.AbelianModuli.ReferenceFamily.LieRanks.dualNumberOrigin ℂ =
      Affine.Tangents.affineTangentOrigin ℂ ≫ complexDualNumberIso.hom := by
  apply Over.OverMorphism.ext
  change 𝟙 (Spec (.of ℂ)) ≫
      Spec.map (CommRingCat.ofHom (AlgebraicGeometry.AbelianModuli.ReferenceFamily.LieRanks.dualNumberReduction ℂ)) =
    Spec.map (CommRingCat.ofHom (AlgebraicGeometry.AbelianModuli.ReferenceFamily.LieRanks.dualNumberReduction ℂ)) ≫ 𝟙 (Spec (.of (DualNumber ℂ)))
  simp only [Category.id_comp, Category.comp_id]

variable (R : Type) [CommRing R] [Algebra ℂ R]
  [Algebra R ℂ] [IsScalarTower ℂ R ℂ]

def affineTangentNativeEquiv : Affine.Tangents.affineTangentPoints ℂ R ≃
    schemeTangentPoints (AlgebraicGeometry.Foundations.Scheme.AffineComplexPoints.affineSchemeOver ℂ R)
      (AlgebraicGeometry.Foundations.Scheme.AffineComplexPoints.affineComplexBaseIso.inv ≫ Affine.Tangents.affineTangentBasePoint ℂ R) :=
  TangentSourcesBased.basedHomEquiv (Affine.Tangents.affineTangentOrigin ℂ) (AlgebraicGeometry.AbelianModuli.ReferenceFamily.LieRanks.dualNumberOrigin ℂ)
    AlgebraicGeometry.Foundations.Scheme.AffineComplexPoints.affineComplexBaseIso complexDualNumberIso affineTangentOrigin_native (Affine.Tangents.affineTangentBasePoint ℂ R)

theorem affineTangentNativeEquiv_apply (f : Affine.Tangents.affineTangentPoints ℂ R) :
    (affineTangentNativeEquiv R f).val = complexDualNumberIso.inv ≫ f.val :=
  TangentSourcesBased.basedHomEquiv_apply _ _ _ _ _ _ f

variable {R}

def regularChartNativeTangentEquiv {n : ℕ} [Algebra.Smooth ℂ R]
    (e : OpenPartialHomeomorph (AlgebraicGeometry.Foundations.Scheme.AffineComplexPoints.affineComplexPoints R) (Fin n → ℂ))
    (he : e ∈ AlgebraicGeometry.ComplexPoints.Analytic.SmoothSchemeManifold.affineRegularAtlas R n) (x : AlgebraicGeometry.Foundations.Scheme.AffineComplexPoints.affineComplexPoints R) (hx : x ∈ e.source)
    (hscalar : ∀ a : R, algebraMap R ℂ a = x a) :
    (Fin n → ℂ) ≃ schemeTangentPoints (AlgebraicGeometry.Foundations.Scheme.AffineComplexPoints.affineSchemeOver ℂ R)
      (AlgebraicGeometry.Foundations.Scheme.AffineComplexPoints.affineComplexBaseIso.inv ≫ Affine.Tangents.affineTangentBasePoint ℂ R) :=
  (RegularTangent.regularChartAffineTangentEquiv e he x hx hscalar).trans (affineTangentNativeEquiv R)

def schemeTangentNeighborhoodEquiv (X U : Over AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.complexBase)
    (i : U ⟶ X) [IsOpenImmersion i.left] (p : AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints U) :
    schemeTangentPoints U p ≃ schemeTangentPoints X (p ≫ i) :=
  TangentNeighborhoods.tangentNeighborhoodEquiv (AlgebraicGeometry.AbelianModuli.ReferenceFamily.LieRanks.dualNumberOrigin ℂ) (TangentNeighborhoods.dualNumberOrigin_surjective ℂ) i p

def regularNeighborhoodTangentEquiv {n : ℕ} [Algebra.Smooth ℂ R]
    (X : Over AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.complexBase) (i : AlgebraicGeometry.Foundations.Scheme.AffineComplexPoints.affineSchemeOver ℂ R ⟶ X) [IsOpenImmersion i.left]
    (e : OpenPartialHomeomorph (AlgebraicGeometry.Foundations.Scheme.AffineComplexPoints.affineComplexPoints R) (Fin n → ℂ))
    (he : e ∈ AlgebraicGeometry.ComplexPoints.Analytic.SmoothSchemeManifold.affineRegularAtlas R n) (x : AlgebraicGeometry.Foundations.Scheme.AffineComplexPoints.affineComplexPoints R) (hx : x ∈ e.source)
    (hscalar : ∀ a : R, algebraMap R ℂ a = x a) :
    (Fin n → ℂ) ≃ schemeTangentPoints X
      ((AlgebraicGeometry.Foundations.Scheme.AffineComplexPoints.affineComplexBaseIso.inv ≫ Affine.Tangents.affineTangentBasePoint ℂ R) ≫ i) :=
  (regularChartNativeTangentEquiv e he x hx hscalar).trans
    (schemeTangentNeighborhoodEquiv X _ i _)

theorem regularNeighborhoodTangentEquiv_apply {n : ℕ} [Algebra.Smooth ℂ R]
    (X : Over AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.complexBase) (i : AlgebraicGeometry.Foundations.Scheme.AffineComplexPoints.affineSchemeOver ℂ R ⟶ X) [IsOpenImmersion i.left]
    (e : OpenPartialHomeomorph (AlgebraicGeometry.Foundations.Scheme.AffineComplexPoints.affineComplexPoints R) (Fin n → ℂ))
    (he : e ∈ AlgebraicGeometry.ComplexPoints.Analytic.SmoothSchemeManifold.affineRegularAtlas R n) (x : AlgebraicGeometry.Foundations.Scheme.AffineComplexPoints.affineComplexPoints R) (hx : x ∈ e.source)
    (hscalar : ∀ a : R, algebraMap R ℂ a = x a) (v : Fin n → ℂ) :
    (regularNeighborhoodTangentEquiv (R := R) X i e he x hx hscalar v).val =
      (complexDualNumberIso.inv ≫
        (Affine.Tangents.derivationAffineTangentEquiv ℂ R (RegularTangent.regularChartDerivation e he x hx hscalar v)).val) ≫ i := rfl

end

/-! Scalar multiplication in tangent coordinates is the actual scaling
map of the dual-number test scheme. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

variable {k R : Type} [Field k] [CommRing R] [Algebra k R]
  [Algebra R k] [IsScalarTower k R k]

theorem derivationDualNumber_smul (c : k) (δ : Derivation k R k) :
    Dual.Numbers.derivationDualNumber (c • δ) = (AlgebraicGeometry.AbelianModuli.ReferenceFamily.LieRanks.dualNumberScale k c).comp (Dual.Numbers.derivationDualNumber δ) := by
  apply AlgHom.ext
  intro a
  apply TrivSqZeroExt.ext
  · exact (TrivSqZeroExt.fst_map _ _).symm
  · change c • δ a = (AlgebraicGeometry.AbelianModuli.ReferenceFamily.LieRanks.dualNumberScale k c (Dual.Numbers.derivationDualNumber δ a)).snd
    rw [AlgebraicGeometry.AbelianModuli.ReferenceFamily.LieRanks.dualNumberScale, TrivSqZeroExt.snd_map]
    rfl

theorem derivationAffineTangent_smul (c : k) (δ : Derivation k R k) :
    (Affine.Tangents.derivationAffineTangentEquiv k R (c • δ)).val =
      AlgebraicGeometry.Foundations.Scheme.AffineComplexPoints.affineAlgHomOverSpecEquiv k (DualNumber k) (DualNumber k) (AlgebraicGeometry.AbelianModuli.ReferenceFamily.LieRanks.dualNumberScale k c) ≫
        (Affine.Tangents.derivationAffineTangentEquiv k R δ).val := by
  change AlgebraicGeometry.Foundations.Scheme.AffineComplexPoints.affineAlgHomOverSpecEquiv k R (DualNumber k) (Dual.Numbers.derivationDualNumber (c • δ)) = _
  rw [derivationDualNumber_smul]
  exact (Affine.Tangents.affineSpec_comp _ _).symm

theorem nativeDualNumberScalar (c : ℂ) :
    complexDualNumberIso.inv ≫
        AlgebraicGeometry.Foundations.Scheme.AffineComplexPoints.affineAlgHomOverSpecEquiv ℂ (DualNumber ℂ) (DualNumber ℂ) (AlgebraicGeometry.AbelianModuli.ReferenceFamily.LieRanks.dualNumberScale ℂ c) =
      AlgebraicGeometry.AbelianModuli.ReferenceFamily.LieRanks.dualNumberScalar ℂ c ≫ complexDualNumberIso.inv := by
  apply Over.OverMorphism.ext
  change 𝟙 (Spec (.of (DualNumber ℂ))) ≫
      Spec.map (CommRingCat.ofHom (AlgebraicGeometry.AbelianModuli.ReferenceFamily.LieRanks.dualNumberScale ℂ c).toRingHom) =
    Spec.map (CommRingCat.ofHom (AlgebraicGeometry.AbelianModuli.ReferenceFamily.LieRanks.dualNumberScale ℂ c).toRingHom) ≫ 𝟙 (Spec (.of (DualNumber ℂ)))
  simp only [Category.id_comp, Category.comp_id]

theorem regularNeighborhoodTangent_smul {R : Type} [CommRing R] [Algebra ℂ R]
    [Algebra R ℂ] [IsScalarTower ℂ R ℂ] {n : ℕ} [Algebra.Smooth ℂ R]
    (X : Over AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.complexBase) (i : AlgebraicGeometry.Foundations.Scheme.AffineComplexPoints.affineSchemeOver ℂ R ⟶ X) [IsOpenImmersion i.left]
    (e : OpenPartialHomeomorph (AlgebraicGeometry.Foundations.Scheme.AffineComplexPoints.affineComplexPoints R) (Fin n → ℂ))
    (he : e ∈ AlgebraicGeometry.ComplexPoints.Analytic.SmoothSchemeManifold.affineRegularAtlas R n) (x : AlgebraicGeometry.Foundations.Scheme.AffineComplexPoints.affineComplexPoints R) (hx : x ∈ e.source)
    (hscalar : ∀ a : R, algebraMap R ℂ a = x a) (c : ℂ) (v : Fin n → ℂ) :
    (regularNeighborhoodTangentEquiv (R := R) X i e he x hx hscalar (c • v)).val =
      AlgebraicGeometry.AbelianModuli.ReferenceFamily.LieRanks.dualNumberScalar ℂ c ≫
        (regularNeighborhoodTangentEquiv (R := R) X i e he x hx hscalar v).val := by
  rw [regularNeighborhoodTangentEquiv_apply, regularNeighborhoodTangentEquiv_apply]
  have hδ := (RegularTangent.regularChartDerivation e he x hx hscalar).map_smul c v
  have hs := derivationAffineTangent_smul c (RegularTangent.regularChartDerivation e he x hx hscalar v)
  have hraw := (congrArg (fun δ : Derivation ℂ R ℂ => (Affine.Tangents.derivationAffineTangentEquiv ℂ R δ).val) hδ).trans hs
  refine (congrArg (fun f : AlgebraicGeometry.Foundations.Scheme.AffineComplexPoints.affineSchemeOver ℂ (DualNumber ℂ) ⟶ AlgebraicGeometry.Foundations.Scheme.AffineComplexPoints.affineSchemeOver ℂ R =>
    (complexDualNumberIso.inv ≫ f) ≫ i) hraw).trans ?_
  rw [← Category.assoc complexDualNumberIso.inv, nativeDualNumberScalar]
  simp only [Category.assoc]

end

end OAI.RepresentationTheory.Theta.Geometric.SchemeTangents
