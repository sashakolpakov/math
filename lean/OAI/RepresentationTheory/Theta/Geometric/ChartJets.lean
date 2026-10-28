import OAI.RepresentationTheory.Theta.Geometric.RegularTangentNaturality
import OAI.RepresentationTheory.Theta.Geometric.SchemeTangents

/-! # Chart Jets -/

namespace OAI.RepresentationTheory.Theta.Geometric.ChartJets

noncomputable section

/-! First-order regular-chart points, independent of any externally installed
point algebra, and their exact functoriality under affine scheme maps. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

variable {A : Type} [CommRing A] [Algebra ℂ A] {n : ℕ}
  (e : OpenPartialHomeomorph (AlgebraicGeometry.Foundations.Scheme.AffineComplexPoints.affineComplexPoints A) (Fin n → ℂ))
  (he : e ∈ AlgebraicGeometry.ComplexPoints.Analytic.SmoothSchemeManifold.affineRegularAtlas A n) (x : AlgebraicGeometry.Foundations.Scheme.AffineComplexPoints.affineComplexPoints A) (hx : x ∈ e.source)

def regularChartJet (v : Fin n → ℂ) : A →ₐ[ℂ] DualNumber ℂ :=
  let : Algebra A ℂ := x.toRingHom.toAlgebra
  let : IsScalarTower ℂ A ℂ := IsScalarTower.of_algHom x
  Dual.Numbers.derivationDualNumber (RegularTangent.regularChartDerivation e he x hx (fun _ => rfl) v)

theorem regularChartJet_fst (v : Fin n → ℂ) (a : A) :
    (regularChartJet e he x hx v a).fst = x a := rfl

theorem regularChartJet_snd (v : Fin n → ℂ) (a : A) :
    (regularChartJet e he x hx v a).snd =
      fderiv ℂ (fun z => e.symm z a) (e x) v := rfl

def regularChartSpecJet (v : Fin n → ℂ) : AlgebraicGeometry.AbelianModuli.ReferenceFamily.LieRanks.dualNumberTest ℂ ⟶ AlgebraicGeometry.Foundations.Scheme.AffineComplexPoints.affineSchemeOver ℂ A :=
  SchemeTangents.complexDualNumberIso.inv ≫ AlgebraicGeometry.Foundations.Scheme.AffineComplexPoints.affineAlgHomOverSpecEquiv ℂ A (DualNumber ℂ)
    (regularChartJet e he x hx v)

theorem regularChartSpecJet_origin (v : Fin n → ℂ) :
    AlgebraicGeometry.AbelianModuli.ReferenceFamily.LieRanks.dualNumberOrigin ℂ ≫ regularChartSpecJet e he x hx v =
      AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.affineSchemePointEquiv A x := by
  let : Algebra A ℂ := x.toRingHom.toAlgebra
  let : IsScalarTower ℂ A ℂ := IsScalarTower.of_algHom x
  have h := (SchemeTangents.affineTangentNativeEquiv A (Affine.Tangents.derivationAffineTangentEquiv ℂ A
    (RegularTangent.regularChartDerivation e he x hx (fun _ => rfl) v))).property
  have hp : IsScalarTower.toAlgHom ℂ A ℂ = x := AlgHom.ext (fun _ => rfl)
  change _ = AlgebraicGeometry.Foundations.Scheme.AffineComplexPoints.affineComplexBaseIso.inv ≫
    AlgebraicGeometry.Foundations.Scheme.AffineComplexPoints.affineAlgHomOverSpecEquiv ℂ A ℂ (IsScalarTower.toAlgHom ℂ A ℂ) at h
  rw [hp] at h
  exact h

theorem regularChartSpecJet_injective :
    Function.Injective (regularChartSpecJet e he x hx) := by
  intro v w h
  have hjet := (AlgebraicGeometry.Foundations.Scheme.AffineComplexPoints.affineAlgHomOverSpecEquiv ℂ A (DualNumber ℂ)).injective
    ((cancel_epi SchemeTangents.complexDualNumberIso.inv).mp h)
  apply RegularTangent.regularChart_tangent_ext e he x hx
  intro a
  exact congrArg (fun f : A →ₐ[ℂ] DualNumber ℂ => (f a).snd) hjet

def regularChartSpecJetEquiv [Algebra.Smooth ℂ A] :
    (Fin n → ℂ) ≃ SchemeTangents.schemeTangentPoints (AlgebraicGeometry.Foundations.Scheme.AffineComplexPoints.affineSchemeOver ℂ A) (AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.affineSchemePointEquiv A x) := by
  let : Algebra A ℂ := x.toRingHom.toAlgebra
  let : IsScalarTower ℂ A ℂ := IsScalarTower.of_algHom x
  have hp : AlgebraicGeometry.Foundations.Scheme.AffineComplexPoints.affineComplexBaseIso.inv ≫ Affine.Tangents.affineTangentBasePoint ℂ A =
      AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.affineSchemePointEquiv A x := by
    have hp : IsScalarTower.toAlgHom ℂ A ℂ = x := AlgHom.ext (fun _ => rfl)
    change AlgebraicGeometry.Foundations.Scheme.AffineComplexPoints.affineComplexBaseIso.inv ≫ AlgebraicGeometry.Foundations.Scheme.AffineComplexPoints.affineAlgHomOverSpecEquiv ℂ A ℂ
      (IsScalarTower.toAlgHom ℂ A ℂ) = _
    rw [hp]
    rfl
  exact (SchemeTangents.regularChartNativeTangentEquiv e he x hx (fun _ => rfl)).trans
    (Equiv.subtypeEquivRight (fun _ => by rw [hp]))

theorem regularChartSpecJetEquiv_apply [Algebra.Smooth ℂ A] (v : Fin n → ℂ) :
    (regularChartSpecJetEquiv e he x hx v).val = regularChartSpecJet e he x hx v := rfl

variable {B : Type} [CommRing B] [Algebra ℂ B] {m : ℕ}
  (h : B →ₐ[ℂ] A)
  (f : OpenPartialHomeomorph (AlgebraicGeometry.Foundations.Scheme.AffineComplexPoints.affineComplexPoints B) (Fin m → ℂ))
  (hf : f ∈ AlgebraicGeometry.ComplexPoints.Analytic.SmoothSchemeManifold.affineRegularAtlas B m) (hfx : x.comp h ∈ f.source)

theorem regularChartJet_naturality (v : Fin n → ℂ) :
    regularChartJet f hf (x.comp h) hfx
      (fderiv ℂ (fun z => f ((e.symm z).comp h)) (e x) v) =
        (regularChartJet e he x hx v).comp h := by
  apply AlgHom.ext
  intro a
  apply TrivSqZeroExt.ext
  · rfl
  · exact (RegularTangentNaturality.regularChart_derivative_naturality h e f he hf x hx hfx a v).symm

theorem regularChartSpecJet_naturality (v : Fin n → ℂ) :
    regularChartSpecJet f hf (x.comp h) hfx
      (fderiv ℂ (fun z => f ((e.symm z).comp h)) (e x) v) =
        regularChartSpecJet e he x hx v ≫ AlgebraicGeometry.Foundations.Scheme.AffineComplexPoints.affineAlgHomOverSpecEquiv ℂ B A h := by
  unfold regularChartSpecJet
  rw [regularChartJet_naturality, ← Affine.Tangents.affineSpec_comp, Category.assoc]

end

end OAI.RepresentationTheory.Theta.Geometric.ChartJets
