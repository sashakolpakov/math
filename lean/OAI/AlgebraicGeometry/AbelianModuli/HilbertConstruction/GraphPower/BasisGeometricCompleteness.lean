import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Cartesian.SectionBasis
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.CanonicalGraph.FieldSectionIsomorphism
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.ProperFlat.SectionFiberCriterion
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Affine.CoefficientSectionBasis

/-! # Basis Geometric Completeness -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction

noncomputable section

/-! Geometric completeness is automatic for a complete basis of a
positive graph power over a tame noetherian affine base, by the actual
field-valued section comparison. -/
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable {S : Scheme.{u}} [IsAffine S] [IsNoetherianRing Γ(S, ⊤)]
variable {g N r : ℕ} {δ : Fin g → ℕ} (A : PolarizationData.PolarizedAbelianWithFullLevel g δ N S)

theorem PolarizationData.PolarizedAbelianWithFullLevel.graphPower_coefficientBasis_geometricComplete
    (hN : 3 ≤ N) (hunit : IsUnit (N : Γ(S, ⊤))) (m : ℕ) (hm : 0 < m)
    (b : Module.Basis (Fin r) Γ(S, ⊤) ((Coefficient.GlobalSectionsFunctor.coefficientGlobalSectionsFunctor A.abelian.scheme.hom.appTop.hom).obj
      (A.graphBundle.tensorPower m).sheaf)) :
    ProperFlat.SectionFiberCriterion.GeometricallyCompleteSectionFamily A.abelian.scheme.hom (A.graphBundle.tensorPower m).sheaf
      (Coefficient.RingSectionBasis.coefficientRingBasisFamily A.abelian.scheme.hom.appTop.hom (A.graphBundle.tensorPower m).sheaf b)
      (𝟙 S) := by
  intro K _ q
  let L := A.graphBundle.tensorPower m
  let H := IsPullback.of_hasPullback A.abelian.scheme.hom q
  let hb := A.graphBundle_positivePower_fieldSectionTensorComparison_bijective hN hunit m hm q
  let B := Cartesian.SectionBasis.cartesianSectionBasis H L.sheaf hb b
  have hB : Coefficient.RingSectionBasis.coefficientRingBasisFamily (pullback.snd A.abelian.scheme.hom q).appTop.hom
      (L.pullback (pullback.fst A.abelian.scheme.hom q)).sheaf B =
      (fun i => Ample.LineBundles.pullbackSection (pullback.fst A.abelian.scheme.hom q)
        (Coefficient.RingSectionBasis.coefficientRingBasisFamily A.abelian.scheme.hom.appTop.hom L.sheaf b i)) := by
    funext i
    exact Cartesian.SectionBasis.cartesianSectionBasis_family H L.sheaf hb b i
  have hc := (Coefficient.SectionFrameCriterion.coefficientSectionLinearCombination_bijective_iff
    (pullback.snd A.abelian.scheme.hom q).appTop.hom
    (L.pullback (pullback.fst A.abelian.scheme.hom q)).sheaf _).mpr ⟨B, hB⟩
  exact hc

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction
