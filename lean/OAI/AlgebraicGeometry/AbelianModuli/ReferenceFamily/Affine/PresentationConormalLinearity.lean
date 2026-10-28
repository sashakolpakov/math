import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Regular.CoefficientConormalLinearity
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Affine.ChartConormalRestriction
import Mathlib.AlgebraicGeometry.Properties

/-! # Presentation Conormal Linearity -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Affine.PresentationConormalLinearity

noncomputable section

/-! Any actual affine presentation of an open in a smooth integral
complex group has coefficient-linear conormal coordinates, including
the empty chart. The chart ring need not be its chosen global-section
presentation. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj

attribute [local implicit_reducible] EtaleSplittingAt.EtaleSplitting.affineOver

variable (G : Over Foundations.Scheme.ProjectiveSpace.complexBase) [IsIntegral G.left] [Smooth G.hom] [GrpObj G]
    (B : CommAlgCat ℂ) (i : EtaleSplittingAt.EtaleSplitting.affineOver ℂ B ⟶ G) [IsOpenImmersion i.left]

include i in
omit [IsIntegral G.left] [GrpObj G] in
theorem affinePresentationAlgebra_smooth : Algebra.Smooth ℂ B := by
  have hs : Smooth (i.left ≫ G.hom) := inferInstance
  have h : Smooth (EtaleSplittingAt.EtaleSplitting.affineOver ℂ B).hom := (congrArg Smooth i.w).mp hs
  exact RingHom.smooth_algebraMap.mp (HasRingHomProperty.Spec_iff.mp h)

include i in
omit [Smooth G.hom] [GrpObj G] in
theorem affinePresentationAlgebra_isDomain [Nontrivial B] : IsDomain B := by
  have : Nonempty (EtaleSplittingAt.EtaleSplitting.affineOver ℂ B).left := inferInstanceAs (Nonempty (PrimeSpectrum B))
  have : IsIntegral (EtaleSplittingAt.EtaleSplitting.affineOver ℂ B).left := isIntegral_of_isOpenImmersion i.left
  exact (affine_isIntegral_iff (.of B)).mp this

def affinePresentationConormalLinearEquiv :
    Derivation ℂ B B ≃ₗ[B] (Constructed.IdentityConormal.constructedIdentityConormal ℂ G →ₗ[ℂ] B) := by
  let F := ChartCoefficientConormal.affineChartCoefficientConormalEquiv ℂ B B G i
  refine { toEquiv := F, map_add' := ?_, map_smul' := ?_ }
  · intro d e
    cases subsingleton_or_nontrivial B with
    | inl h =>
      let := h
      exact Subsingleton.elim _ _
    | inr h =>
      let := h
      have : Algebra.Smooth ℂ B := affinePresentationAlgebra_smooth G B i
      have : IsDomain B := affinePresentationAlgebra_isDomain G B i
      exact Regular.CoefficientConormalLinearity.regularCoefficientConormal_add G B i B d e
  · intro c d
    cases subsingleton_or_nontrivial B with
    | inl h =>
      let := h
      exact Subsingleton.elim _ _
    | inr h =>
      let := h
      have : Algebra.Smooth ℂ B := affinePresentationAlgebra_smooth G B i
      have : IsDomain B := affinePresentationAlgebra_isDomain G B i
      exact Regular.CoefficientConormalLinearity.regularCoefficientConormal_smul G B i B c d

variable (D : CommAlgCat ℂ) (j : EtaleSplittingAt.EtaleSplitting.affineOver ℂ D ⟶ G) [IsOpenImmersion j.left]

theorem affinePresentationConormalLinearEquiv_natural (q : B →ₐ[ℂ] D) (hq : q.toRingHom.Etale)
    (hi : AlgebraAutomorphismNaturality.affineOverAlgHom ℂ B D q ≫ i = j) (d : Derivation ℂ B B)
    (z : Constructed.IdentityConormal.constructedIdentityConormal ℂ G) :
    affinePresentationConormalLinearEquiv G D j (EtaleHomDerivation.etaleAlgHomDerivationLinear q hq d) z =
      q (affinePresentationConormalLinearEquiv G B i d z) :=
  ChartConormalRestriction.affineChartCoefficientConormalEquiv_restriction ℂ B D q hq G i j hi d z

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Affine.PresentationConormalLinearity
