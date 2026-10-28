import OAI.AlgebraicGeometry.CycleClass.Thom.PointProductNormal
import OAI.AlgebraicGeometry.CycleClass.Thom.SingleChartPoint

/-! # Point Canonical -/

namespace OAI.AlgebraicGeometry.CycleClass.Thom.Product.PointCanonical.Constructions.Class

noncomputable section

/-! Products of normal point classes have the canonical complex orientation in a specified flattened chart. -/

open _root_.CategoryTheory

open OAI.AlgebraicGeometry.CycleClass.Thom.PointProductNormal.Constructions.Class OAI.AlgebraicGeometry.CycleClass.Thom.SingleChartPoint.Constructions.Class OAI.AlgebraicGeometry.CycleClass.Thom.SingleChartComplexManifold.Constructions
open OAI.AlgebraicGeometry.CycleClass.Thom.Supported.PointProjection.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.CanonicalLocalDual.Constructions

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

theorem relativeMap_congr {X Y : TopCat.{0}} {f g : X ⟶ Y} (h : f = g)
    {A : Set X} {B : Set Y} (hf : Set.MapsTo f A B) (hg : Set.MapsTo g A B) (n : ℕ) :
    AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomologyMap (ModuleCat.of ℚ ℚ) f hf n =
      AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomologyMap (ModuleCat.of ℚ ℚ) g hg n := by
  subst g
  rfl

theorem normalPointMap_eq_centered (p d : ℕ) (x : Fin d → ℂ)
    (e : ((Fin p → ℂ) × (Fin d → ℂ)) ≃L[ℂ] (Fin (p + d) → ℂ)) :
    PointProductNormal.Constructions.Class.normalPointMap p d x e = SingleChartPoint.Constructions.Class.centeredChartMap (p + d) e.toHomeomorph (0, x) := by
  apply TopCat.hom_ext
  apply ContinuousMap.ext
  rintro ⟨u, v⟩
  change e (u, v - x) = e (u, v) - e (0, x)
  simpa only [Prod.mk_sub_mk, sub_zero] using e.map_sub (u, v) (0, x)

theorem productPointComplement (p d : ℕ) (x : Fin d → ℂ) :
    Set.MapsTo (𝟙 (TopCat.of ((Fin p → ℂ) × (Fin d → ℂ))))
      (({0} : Set (Fin p → ℂ)) ×ˢ {x})ᶜ ({(0, x)}ᶜ) := by
  intro z hz he
  change z = (0, x) at he
  subst z
  exact hz ⟨rfl, rfl⟩

theorem productPointClass_canonical (p d : ℕ) (x : Fin d → ℂ)
    (e : ((Fin p → ℂ) × (Fin d → ℂ)) ≃L[ℂ] (Fin (p + d) → ℂ)) :
    letI := SingleChartComplexManifold.Constructions.coordinateChartedSpace (p + d) e.toHomeomorph
    eqToHom (congrArg (fun n => AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomology (ModuleCat.of ℚ ℚ)
      (TopCat.of ((Fin p → ℂ) × (Fin d → ℂ))) (({0} : Set (Fin p → ℂ)) ×ˢ {x})ᶜ n)
      (Nat.mul_add 2 p d).symm)
      (Supported.PointProjection.Constructions.productPointClass d (TopCat.of (Fin p → ℂ)) {0} isClosed_singleton x (2 * p)
        (Geometric.RationalLocalPurity.Cycles.complexNormalRationalDualClass p)) =
      AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomologyMap (ModuleCat.of ℚ ℚ)
        (𝟙 (TopCat.of ((Fin p → ℂ) × (Fin d → ℂ)))) (productPointComplement p d x)
        (2 * (p + d)) (CanonicalLocalDual.Constructions.canonicalLocalDual (p + d) (0, x)) := by
  let := SingleChartComplexManifold.Constructions.coordinateChartedSpace (p + d) e.toHomeomorph
  refine (PointProductNormal.Constructions.Class.productPointClass_normal p d x e).trans ?_
  have hc := SingleChartPoint.Constructions.Class.canonicalLocalDual_centeredChart (p + d) e.toHomeomorph (0, x)
  have hcomp := ConcreteCategory.congr_hom
    (AlgebraicTopology.Cohomology.Singular.RelativeOpenSupport.relativeSingularCohomologyMap_comp (ModuleCat.of ℚ ℚ)
      (𝟙 (TopCat.of ((Fin p → ℂ) × (Fin d → ℂ))))
      (SingleChartPoint.Constructions.Class.centeredChartMap (p + d) e.toHomeomorph (0, x))
      (productPointComplement p d x) (SingleChartPoint.Constructions.Class.centeredChartMapsTo (p + d) e.toHomeomorph (0, x))
      (2 * (p + d))) (Geometric.RationalLocalPurity.Cycles.complexNormalRationalDualClass (p + d))
  have hm := relativeMap_congr (normalPointMap_eq_centered p d x e)
    (PointProductNormal.Constructions.Class.normalPointMapsTo p d x e)
    ((SingleChartPoint.Constructions.Class.centeredChartMapsTo (p + d) e.toHomeomorph (0, x)).comp (productPointComplement p d x))
    (2 * (p + d))
  refine (ConcreteCategory.congr_hom hm (Geometric.RationalLocalPurity.Cycles.complexNormalRationalDualClass (p + d))).trans
    (hcomp.symm.trans ?_)
  exact congrArg (AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomologyMap (ModuleCat.of ℚ ℚ)
    (𝟙 (TopCat.of ((Fin p → ℂ) × (Fin d → ℂ)))) (productPointComplement p d x)
    (2 * (p + d))) hc

end

end OAI.AlgebraicGeometry.CycleClass.Thom.Product.PointCanonical.Constructions.Class
