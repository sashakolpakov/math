import OAI.AlgebraicGeometry.Divisors.LineBundles.Support.LaurentChart
import OAI.AlgebraicGeometry.Divisors.LineBundles.Laurent.FiberGenericPoint

/-! # Punctured Generic Point -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles.Support.PuncturedGenericPoint.BundleCycles

noncomputable section

/-! # LineBundleCycles: generic points of the actual punctured closed-support fibers -/

open _root_.AlgebraicGeometry _root_.CategoryTheory _root_.TopologicalSpace
open _root_.AlgebraicGeometry.Scheme.AffineZariskiSite

variable {X : Scheme.{0}} (I P : X.IdealSheafData)

theorem supportPuncturedChart_prime_projection (U : X.AffineZariskiSite)
    (p : Spec ((CoefficientDiagram.BundleCycles.supportCoefficientDiagram P).obj (.op U))) :
    LaurentChart.BundleCycles.supportPuncturedProjection I P
        (LaurentChart.BundleCycles.supportPuncturedLaurentChart I P U (Laurent.FiberGenericPoint.BundleCycles.laurentPrimePoint ((CoefficientDiagram.BundleCycles.supportCoefficientDiagram P).obj (.op U)) p)) =
      Projection.BundleCycles.supportCoefficientChart P U p :=
  (congrArg (fun k => k (Laurent.FiberGenericPoint.BundleCycles.laurentPrimePoint ((CoefficientDiagram.BundleCycles.supportCoefficientDiagram P).obj (.op U)) p))
    (LaurentChart.BundleCycles.supportPuncturedLaurentChart_toSupport I P U)).trans
      (congrArg (Projection.BundleCycles.supportCoefficientChart P U)
        (Laurent.FiberGenericPoint.BundleCycles.laurentPrimePoint_projection ((CoefficientDiagram.BundleCycles.supportCoefficientDiagram P).obj (.op U)) p))

theorem supportPuncturedProjection_surjective : Function.Surjective (LaurentChart.BundleCycles.supportPuncturedProjection I P) := by
  intro x
  obtain ⟨U, p, hp⟩ := P.subschemeCover.openCover.exists_eq x
  exact ⟨LaurentChart.BundleCycles.supportPuncturedLaurentChart I P U (Laurent.FiberGenericPoint.BundleCycles.laurentPrimePoint ((CoefficientDiagram.BundleCycles.supportCoefficientDiagram P).obj (.op U)) p),
    (supportPuncturedChart_prime_projection I P U p).trans hp⟩

theorem supportPuncturedChart_prime_specializes (U : X.AffineZariskiSite)
    (p : Spec ((CoefficientDiagram.BundleCycles.supportCoefficientDiagram P).obj (.op U))) (y : LaurentChart.BundleCycles.supportPuncturedDeformation I P)
    (hy : LaurentChart.BundleCycles.supportPuncturedProjection I P y = Projection.BundleCycles.supportCoefficientChart P U p) :
    LaurentChart.BundleCycles.supportPuncturedLaurentChart I P U (Laurent.FiberGenericPoint.BundleCycles.laurentPrimePoint ((CoefficientDiagram.BundleCycles.supportCoefficientDiagram P).obj (.op U)) p) ⤳ y := by
  have hyr : y ∈ Set.range (LaurentChart.BundleCycles.supportPuncturedLaurentChart I P U) :=
    (congrArg (fun s : Set (LaurentChart.BundleCycles.supportPuncturedDeformation I P) => y ∈ s)
      (LaurentChart.BundleCycles.supportPuncturedLaurentChart_range I P U)).mpr ⟨p, hy.symm⟩
  obtain ⟨Q, rfl⟩ := hyr
  have hp : Laurent.FiberGenericPoint.BundleCycles.laurentProjection ((CoefficientDiagram.BundleCycles.supportCoefficientDiagram P).obj (.op U)) Q = p := by
    apply (Projection.BundleCycles.supportCoefficientChart P U).isOpenEmbedding.injective
    exact (congrArg (fun k => k Q) (LaurentChart.BundleCycles.supportPuncturedLaurentChart_toSupport I P U)).symm.trans hy
  exact (Laurent.FiberGenericPoint.BundleCycles.laurentPrimePoint_specializes_fiber ((CoefficientDiagram.BundleCycles.supportCoefficientDiagram P).obj (.op U)) p Q hp).map
    (LaurentChart.BundleCycles.supportPuncturedLaurentChart I P U).continuous

theorem supportPuncturedGenericPoint_exists (x : P.subscheme) :
    ∃ z : LaurentChart.BundleCycles.supportPuncturedDeformation I P, LaurentChart.BundleCycles.supportPuncturedProjection I P z = x ∧
      ∀ y, LaurentChart.BundleCycles.supportPuncturedProjection I P y = x → z ⤳ y := by
  obtain ⟨U, p, hp⟩ := P.subschemeCover.openCover.exists_eq x
  refine ⟨LaurentChart.BundleCycles.supportPuncturedLaurentChart I P U (Laurent.FiberGenericPoint.BundleCycles.laurentPrimePoint ((CoefficientDiagram.BundleCycles.supportCoefficientDiagram P).obj (.op U)) p),
    (supportPuncturedChart_prime_projection I P U p).trans hp, ?_⟩
  intro y hy
  exact supportPuncturedChart_prime_specializes I P U p y (hy.trans hp.symm)

def supportPuncturedGenericPoint (x : P.subscheme) : LaurentChart.BundleCycles.supportPuncturedDeformation I P :=
  (supportPuncturedGenericPoint_exists I P x).choose

theorem supportPuncturedGenericPoint_projection (x : P.subscheme) :
    LaurentChart.BundleCycles.supportPuncturedProjection I P (supportPuncturedGenericPoint I P x) = x :=
  (supportPuncturedGenericPoint_exists I P x).choose_spec.1

theorem supportPuncturedGenericPoint_specializes (x : P.subscheme) (y : LaurentChart.BundleCycles.supportPuncturedDeformation I P)
    (hy : LaurentChart.BundleCycles.supportPuncturedProjection I P y = x) : supportPuncturedGenericPoint I P x ⤳ y :=
  (supportPuncturedGenericPoint_exists I P x).choose_spec.2 y hy

theorem supportPuncturedGenericPoint_on_chart (U : X.AffineZariskiSite)
    (p : Spec ((CoefficientDiagram.BundleCycles.supportCoefficientDiagram P).obj (.op U))) :
    supportPuncturedGenericPoint I P (Projection.BundleCycles.supportCoefficientChart P U p) =
      LaurentChart.BundleCycles.supportPuncturedLaurentChart I P U (Laurent.FiberGenericPoint.BundleCycles.laurentPrimePoint ((CoefficientDiagram.BundleCycles.supportCoefficientDiagram P).obj (.op U)) p) := by
  exact ((supportPuncturedGenericPoint_specializes I P _ _
    (supportPuncturedChart_prime_projection I P U p)).antisymm
      (supportPuncturedChart_prime_specializes I P U p _
        (supportPuncturedGenericPoint_projection I P _))).eq

theorem supportPuncturedGenericPoint_injective : Function.Injective (supportPuncturedGenericPoint I P) :=
  Function.LeftInverse.injective (supportPuncturedGenericPoint_projection I P)

end

end OAI.AlgebraicGeometry.Divisors.LineBundles.Support.PuncturedGenericPoint.BundleCycles
