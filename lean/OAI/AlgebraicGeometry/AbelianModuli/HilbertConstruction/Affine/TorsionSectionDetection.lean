import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.EvenGraphEvaluationSplitting
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Affine.FramedSectionEvaluation

/-! # Torsion Section Detection -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction

noncomputable section

/-! A geometrically complete basis and sufficiently high auxiliary
level detect actual global graph-power sections over any affine ring.
The conclusion is an equality of sections over the original ring. -/
open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped Classical
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable {R : Type u} [CommRing R] {g N n r : ℕ} {δ : Fin g → ℕ} [NeZero n]
variable (A : PolarizationData.PolarizedAbelianWithFullLevel g δ N (Spec (.of R)))

def PolarizationData.PolarizedAbelianWithFullLevel.fullLevelAffineEvenGraphEvaluation (level : A.abelian.FullLevel n) (t : ℕ)
    (e : ∀ c : Multiplicative (Fin (2 * g) → ZMod n),
      ((A.graphBundle.tensorPower (2 * t)).pullback (A.abelian.fullLevelGlobalSection level c)).sheaf ≅
        Line.Bundles.structureModule (Spec (.of R))) :
    (Coefficient.GlobalSectionsFunctor.schemeGlobalSectionsFunctor A.abelian.scheme.hom).obj (A.graphBundle.tensorPower (2 * t)).sheaf →ₗ[R]
      (Multiplicative (Fin (2 * g) → ZMod n) → R) :=
  LinearMap.pi (fun c => Affine.FramedSectionEvaluation.affineFramedSectionEvaluation A.abelian.scheme.hom
    (A.graphBundle.tensorPower (2 * t)) (A.abelian.fullLevelGlobalSection level c)
    (A.abelian.fullLevelGlobalSection_comp level c) (e c))

theorem PolarizationData.PolarizedAbelianWithFullLevel.fullLevelAffineEvenGraphEvaluation_injective
    (hg : 0 < g) (hδ : ∀ i, 0 < δ i) (hN : 3 ≤ N)
    (hunit : IsUnit (N : Γ(Spec (.of R), ⊤)))
    (level : A.abelian.FullLevel n) (t : ℕ) (ht : 0 < t)
    (htlarge : Graph.EmbeddingNumerics.graphSquareSectionRank g δ ≤ t)
    (hlarge : EvenGraphTorsionBound.evenGraphTorsionDegree g δ t < n ^ 2)
    (b : Module.Basis (Fin r) R ((Coefficient.GlobalSectionsFunctor.schemeGlobalSectionsFunctor A.abelian.scheme.hom).obj
      (A.graphBundle.tensorPower (2 * t)).sheaf))
    (hs : ProperFlat.SectionFiberCriterion.GeometricallyCompleteSectionFamily A.abelian.scheme.hom
      (A.graphBundle.tensorPower (2 * t)).sheaf
      (Coefficient.RingSectionBasis.coefficientRingBasisFamily (Coefficient.ModulePresheaf.schemeCoefficientMap A.abelian.scheme.hom)
        (A.graphBundle.tensorPower (2 * t)).sheaf b) (𝟙 (Spec (.of R))))
    (e : ∀ c : Multiplicative (Fin (2 * g) → ZMod n),
      ((A.graphBundle.tensorPower (2 * t)).pullback (A.abelian.fullLevelGlobalSection level c)).sheaf ≅
        Line.Bundles.structureModule (Spec (.of R))) :
    Function.Injective (A.fullLevelAffineEvenGraphEvaluation level t e) := by
  let s := Coefficient.RingSectionBasis.coefficientRingBasisFamily (Coefficient.ModulePresheaf.schemeCoefficientMap A.abelian.scheme.hom)
    (A.graphBundle.tensorPower (2 * t)).sheaf b
  let ev := A.fullLevelAffineEvenGraphEvaluation level t e
  have heq : Affine.GeometricMatrixSplitting.affineCoordinateMatrix (A.evenGraphFamilyEvaluationMatrix level t s e) =
      BasisEvaluationMatrices.basisEvaluationMatrix b ev := rfl
  have hM := A.evenGraphFamilyEvaluationMatrix_injective_all_baseChanges hg hδ hN hunit
    level t ht htlarge hlarge s hs e (RingHom.id R)
  change Function.Injective (Matrix.toLin'
    (Affine.GeometricMatrixSplitting.affineCoordinateMatrix (A.evenGraphFamilyEvaluationMatrix level t s e))) at hM
  rw [heq, BasisEvaluationMatrices.basisEvaluationMatrix_linearMap] at hM
  intro v w hvw
  apply b.equivFun.injective
  apply hM
  simpa only [LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.symm_apply_apply] using hvw

theorem PolarizationData.PolarizedAbelianWithFullLevel.affineEvenGraphPower_section_eq_zero_of_framed_values
    (hg : 0 < g) (hδ : ∀ i, 0 < δ i) (hN : 3 ≤ N)
    (hunit : IsUnit (N : Γ(Spec (.of R), ⊤)))
    (level : A.abelian.FullLevel n) (t : ℕ) (ht : 0 < t)
    (htlarge : Graph.EmbeddingNumerics.graphSquareSectionRank g δ ≤ t)
    (hlarge : EvenGraphTorsionBound.evenGraphTorsionDegree g δ t < n ^ 2)
    (b : Module.Basis (Fin r) R ((Coefficient.GlobalSectionsFunctor.schemeGlobalSectionsFunctor A.abelian.scheme.hom).obj
      (A.graphBundle.tensorPower (2 * t)).sheaf))
    (hs : ProperFlat.SectionFiberCriterion.GeometricallyCompleteSectionFamily A.abelian.scheme.hom
      (A.graphBundle.tensorPower (2 * t)).sheaf
      (Coefficient.RingSectionBasis.coefficientRingBasisFamily (Coefficient.ModulePresheaf.schemeCoefficientMap A.abelian.scheme.hom)
        (A.graphBundle.tensorPower (2 * t)).sheaf b) (𝟙 (Spec (.of R))))
    (e : ∀ c : Multiplicative (Fin (2 * g) → ZMod n),
      ((A.graphBundle.tensorPower (2 * t)).pullback (A.abelian.fullLevelGlobalSection level c)).sheaf ≅
        Line.Bundles.structureModule (Spec (.of R)))
    (a : Line.Bundles.structureModule A.abelian.scheme.left ⟶ (A.graphBundle.tensorPower (2 * t)).sheaf)
    (ha : ∀ c, Affine.FramedSectionEvaluation.affineFramedSectionValue (A.graphBundle.tensorPower (2 * t))
      (A.abelian.fullLevelGlobalSection level c) (e c) a = 0) : a = 0 := by
  let E := Coefficient.RingSectionBasis.coefficientRingSectionAddEquiv (Coefficient.ModulePresheaf.schemeCoefficientMap A.abelian.scheme.hom)
    (A.graphBundle.tensorPower (2 * t)).sheaf
  apply E.injective
  apply A.fullLevelAffineEvenGraphEvaluation_injective hg hδ hN hunit
    level t ht htlarge hlarge b hs e
  rw [map_zero, map_zero]
  funext c
  exact (Affine.FramedSectionEvaluation.affineFramedSectionEvaluation_section A.abelian.scheme.hom
    (A.graphBundle.tensorPower (2 * t)) (A.abelian.fullLevelGlobalSection level c)
    (A.abelian.fullLevelGlobalSection_comp level c) (e c) a).trans (ha c)

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction
