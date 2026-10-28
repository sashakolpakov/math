import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Affine.DualOpen
import OAI.AlgebraicGeometry.ComplexPoints.Analytic.IntrinsicOpenDifferential

/-! # Scheme Dual Tangent -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Intrinsic.SchemeDualTangent

noncomputable section

/-! Actual dual-number points of a smooth integral complex scheme are
parametrized by its established native manifold tangent space. The
construction uses an affine neighborhood and its actual differential. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry OAI.AlgebraicGeometry.ComplexPoints.Analytic.IntrinsicOpenDifferential
open scoped _root_.Manifold ContDiff

variable (X : Over Foundations.Scheme.ProjectiveSpace.complexBase) [IsIntegral X.left] [Smooth X.hom]
local notation "ModelX" => (Fin (OAI.AlgebraicGeometry.Betti.AffineDimension.Realization.functionFieldDifferentialDimension X.hom) → ℂ)

theorem nativeSchemeTangentDual_nonempty (p : ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X) :
    Nonempty (TangentSpace 𝓘(ℂ, ModelX) p ≃ DualOpen.Lifts.DualSchemePoints X p) := by
  obtain ⟨U, hU, x, hx⟩ := ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.exists_affineOpenPoint_lift X p
  have hpU : ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.underlying p ∈ U := by
    have hr : p ∈ Set.range (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.affineOpenPointMap X U hU) := ⟨x, hx⟩
    rwa [ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.range_affineOpenPointMap] at hr
  let : Nonempty U := ⟨⟨ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.underlying p, hpU⟩⟩
  let A := ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.affineOpenAlgebra X U
  let : IsDomain A := ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.affineOpenAlgebra_isDomain X U
  let : Algebra.Smooth ℂ A := ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.affineOpenAlgebra_smooth X U hU
  let i := ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.affineOpenSchemeMap X U hU
  have hi : ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.affinePointMap A i x = p := hx
  exact hi ▸ ⟨Affine.DualOpen.affineOpenTangentDualEquiv A i x⟩

theorem exists_nativeSchemeTangentDual (p : ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X) :
    ∃ e : TangentSpace 𝓘(ℂ, ModelX) p ≃ DualOpen.Lifts.DualSchemePoints X p,
      ∀ (A : CommAlgCat ℂ) [IsDomain A] [Algebra.Smooth ℂ A]
        (i : Foundations.Scheme.AffineComplexPoints.affineSchemeOver ℂ A ⟶ X) [IsOpenImmersion i.left]
        (x : Foundations.Scheme.AffineComplexPoints.affineComplexPoints A), ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.affinePointMap A i x = p →
        ∀ v : ModelX, (e v).val = (Affine.DualOpen.affineOpenTangentDualEquiv A i x v).val := by
  obtain ⟨U, hU, y, hy⟩ := ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.exists_affineOpenPoint_lift X p
  have hpU : ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.underlying p ∈ U := by
    have hr : p ∈ Set.range (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.affineOpenPointMap X U hU) := ⟨y, hy⟩
    rwa [ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.range_affineOpenPointMap] at hr
  let : Nonempty U := ⟨⟨ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.underlying p, hpU⟩⟩
  let B := ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.affineOpenAlgebra X U
  let : IsDomain B := ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.affineOpenAlgebra_isDomain X U
  let : Algebra.Smooth ℂ B := ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.affineOpenAlgebra_smooth X U hU
  let j := ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.affineOpenSchemeMap X U hU
  have hj : ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.affinePointMap B j y = p := hy
  let q : DualOpen.Lifts.DualSchemePoints X (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.affinePointMap B j y) ≃ DualOpen.Lifts.DualSchemePoints X p :=
    Set.equivOfEq (congrArg (fun z => {f : LieRanks.dualNumberTest ℂ ⟶ X | LieRanks.dualNumberOrigin ℂ ≫ f = z}) hj)
  refine ⟨(Affine.DualOpen.affineOpenTangentDualEquiv B j y).trans q, ?_⟩
  intro A _ _ i _ x hx v
  change (Affine.DualOpen.affineOpenTangentDualEquiv B j y v).val = _
  exact Affine.DualOpen.affineOpenTangentDual_independent B A j i y x (hj.trans hx.symm) v

def nativeSchemeTangentDualEquiv (p : ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X) :
    TangentSpace 𝓘(ℂ, ModelX) p ≃ DualOpen.Lifts.DualSchemePoints X p :=
  (exists_nativeSchemeTangentDual X p).choose

theorem nativeSchemeTangentDual_affine (p : ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X)
    (A : CommAlgCat ℂ) [IsDomain A] [Algebra.Smooth ℂ A]
    (i : Foundations.Scheme.AffineComplexPoints.affineSchemeOver ℂ A ⟶ X) [IsOpenImmersion i.left]
    (x : Foundations.Scheme.AffineComplexPoints.affineComplexPoints A) (hx : ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.affinePointMap A i x = p)
    (v : ModelX) :
    (nativeSchemeTangentDualEquiv X p v).val = (Affine.DualOpen.affineOpenTangentDualEquiv A i x v).val :=
  (exists_nativeSchemeTangentDual X p).choose_spec A i x hx v

theorem nativeSchemeTangentDual_mfderiv
    (A : CommAlgCat ℂ) [IsDomain A] [Algebra.Smooth ℂ A]
    (i : Foundations.Scheme.AffineComplexPoints.affineSchemeOver ℂ A ⟶ X) [IsOpenImmersion i.left]
    (x : Foundations.Scheme.AffineComplexPoints.affineComplexPoints A)
    (v : TangentSpace 𝓘(ℂ, Fin (Foundations.Scheme.SmoothDomainDimension.Algebraic.genericDifferentialRank ℂ A) → ℂ) x) :
    (nativeSchemeTangentDualEquiv X (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.affinePointMap A i x)
      (mfderiv 𝓘(ℂ, Fin (Foundations.Scheme.SmoothDomainDimension.Algebraic.genericDifferentialRank ℂ A) → ℂ) 𝓘(ℂ, ModelX)
        (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.affinePointMap A i) x v)).val =
      Affine.DualOpen.affineDualSchemeMap (AffineDualPoints.nativeAffineDualPointEquiv x v).val ≫ i :=
  (nativeSchemeTangentDual_affine X _ A i x rfl _).trans
    (Affine.DualOpen.affineOpenTangentDualEquiv_mfderiv A i x v)

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Intrinsic.SchemeDualTangent
