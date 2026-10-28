import OAI.AlgebraicGeometry.Divisors.LineBundles.Relative.NormalizationFields
import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Integral.Height

/-! # Normalization Charts -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles.Relative.NormalizationCharts.BundleCycles.RelativeNormalizationCharts

noncomputable section

/-! Actual integral-closure charts of relative normalization and preservation
of point codimensions for a finite-type base over a field. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.Order

open OAI.AlgebraicGeometry.Divisors.LineBundles.Relative.Normalization.BundleCycles.RelativeNormalization OAI.AlgebraicGeometry.Divisors.LineBundles.Relative.NormalizationLocal.BundleCycles.RelativeNormalizationLocal

universe u

variable (Y : Scheme.{u}) [IsIntegral Y] (L : Type u) [Field L] [Algebra Y.functionField L]

local instance (U : Y.Opens) [Nonempty U] : Algebra Γ(Y, U) L :=
  ((algebraMap Y.functionField L).comp (algebraMap Γ(Y, U) Y.functionField)).toAlgebra

local instance (U : Y.Opens) [Nonempty U] : IsScalarTower Γ(Y, U) Y.functionField L :=
  IsScalarTower.of_algebraMap_eq' rfl

def chartMap (U : Y.Opens) (hU : IsAffineOpen U) [Nonempty U] :
    Spec (.of (integralClosure Γ(Y, U) L)) ⟶ Normalization.BundleCycles.RelativeNormalization.relativeNormalization Y L :=
  Spec.map (NormalizationLocal.BundleCycles.RelativeNormalizationLocal.affineRingIso Y L U hU).hom ≫ (hU.preimage (Normalization.BundleCycles.RelativeNormalization.relativeNormalizationMap Y L)).fromSpec

instance (U : Y.Opens) (hU : IsAffineOpen U) [Nonempty U] :
    IsOpenImmersion (chartMap Y L U hU) := by
  unfold chartMap
  infer_instance

theorem chartMap_comp (U : Y.Opens) (hU : IsAffineOpen U) [Nonempty U] :
    chartMap Y L U hU ≫ Normalization.BundleCycles.RelativeNormalization.relativeNormalizationMap Y L =
      Spec.map (CommRingCat.ofHom (algebraMap Γ(Y, U) (integralClosure Γ(Y, U) L))) ≫
        hU.fromSpec := by
  rw [chartMap, Category.assoc,
    ← hU.SpecMap_appLE_fromSpec (Normalization.BundleCycles.RelativeNormalization.relativeNormalizationMap Y L)
      (hU.preimage (Normalization.BundleCycles.RelativeNormalization.relativeNormalizationMap Y L)) le_rfl,
    ← Category.assoc, ← Spec.map_comp]
  congr 2
  rw [← Scheme.Hom.app_eq_appLE, NormalizationLocal.BundleCycles.RelativeNormalizationLocal.affineRingIso_base]

theorem chartMap_range (U : Y.Opens) (hU : IsAffineOpen U) [Nonempty U] :
    Set.range (chartMap Y L U hU) =
      (Normalization.BundleCycles.RelativeNormalization.relativeNormalizationMap Y L ⁻¹ᵁ U : Set (Normalization.BundleCycles.RelativeNormalization.relativeNormalization Y L)) := by
  rw [chartMap, Scheme.Hom.comp_base, TopCat.coe_comp, Set.range_comp,
    (Spec.map (NormalizationLocal.BundleCycles.RelativeNormalizationLocal.affineRingIso Y L U hU).hom).surjective.range_eq, Set.image_univ]
  exact (hU.preimage (Normalization.BundleCycles.RelativeNormalization.relativeNormalizationMap Y L)).range_fromSpec

theorem relativeNormalizationMap_coheight {k : Type u} [Field k]
    (f : Y ⟶ Spec (.of k)) [LocallyOfFiniteType f]
    (z : Normalization.BundleCycles.RelativeNormalization.relativeNormalization Y L) :
    coheight (Normalization.BundleCycles.RelativeNormalization.relativeNormalizationMap Y L z) = coheight z := by
  obtain ⟨U, hU, hzU, _⟩ :=
    exists_isAffineOpen_mem_and_subset (TopologicalSpace.Opens.mem_top (Normalization.BundleCycles.RelativeNormalization.relativeNormalizationMap Y L z))
  let : Nonempty U := ⟨⟨Normalization.BundleCycles.RelativeNormalization.relativeNormalizationMap Y L z, hzU⟩⟩
  let A := Γ(Y, U)
  let B := integralClosure A L
  let := Foundations.Scheme.SpecScalarTransport.specSectionScalarAlgebra f U
  let := Foundations.Scheme.AffineSectionFiniteType.specSectionScalarAlgebra_finiteType f U hU
  let := functionField_isFractionRing_of_isAffineOpen Y U hU
  have hinjL : Function.Injective (algebraMap A L) :=
    (algebraMap Y.functionField L).injective.comp (IsFractionRing.injective A Y.functionField)
  have hinj : Function.Injective (algebraMap A B) := by
    intro a b hab
    apply hinjL
    exact congrArg (fun t : B => (t : L)) hab
  have hzrange : z ∈ Set.range (chartMap Y L U hU) := by
    rw [chartMap_range]
    exact hzU
  obtain ⟨q, hq⟩ := hzrange
  have hpoint := congrArg (fun i : Spec (.of B) ⟶ Y => i q) (chartMap_comp Y L U hU)
  change Normalization.BundleCycles.RelativeNormalization.relativeNormalizationMap Y L (chartMap Y L U hU q) =
    hU.fromSpec ((Spec.map (CommRingCat.ofHom (algebraMap A B))) q) at hpoint
  rw [← hq, hpoint]
  simp only [coheight_eq_of_isOpenImmersion]
  rw [← idealHeight_eq_coheight, ← idealHeight_eq_coheight]
  exact IntersectionTheory.ProjectionFormula.Integral.Height.integral_height_under k A B hinj q

end

end OAI.AlgebraicGeometry.Divisors.LineBundles.Relative.NormalizationCharts.BundleCycles.RelativeNormalizationCharts
