import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Ordinary.Locus
import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.FiberGeneration
import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.ProductDetection
import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.AlbaneseProduct
import OAI.ArithmeticGeometry.OrdinaryLocus.Openness.SmoothReduced
import OAI.AlgebraicGeometry.AbelianScheme.TateComparison.BaseChange

/-! # Detection -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Intrinsic.Detection.CM

noncomputable section

/-! Faithful ordinary-difference detection for CMPoints's actual geometric
family and IntegralModel's actual component Albanese groups. The detection clause
is proved from the native geometric and generation conclusions. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj
open OAI.AlgebraicGeometry.AbelianScheme.TateComparison.BaseChange
open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Geometric.PointExt.CM OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Ordinary.Locus.CM
open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.PointEvaluationCM.CM OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.ProductPoints.CM
open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.ProductDetection.CM OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.AlbaneseProduct.CM

variable {E K : Type} [Field E] [NumberField E] [Algebra ℚ E]
  [NumberField.IsCMField E] [Field K] [NumberField K]
  {M : PELModuli.CMPoints.Models.RankThreePELModel E K} {q : ℕ} [Fact q.Prime]
  {j : M.QadicChoice q} (R : M.GoodIntegralReduction q j) (a : M.Family)

abbrev residueClosure := AlgebraicClosure (ZMod q)

def geometricAlbaneseFactors (i : Fin (M.componentCount a)) :
    CommGrp (Over (Spec (.of (residueClosure (q := q))))) :=
  AbelianScheme.TateComparison.BaseChange.baseChangedGroup ((M.components a).A i).X R.geometricBase

def geometricAlbanese : CommGrp (Over (Spec (.of (residueClosure (q := q))))) :=
  AbelianScheme.TateComparison.Products.componentProduct (geometricAlbaneseFactors R a)

def geometricComponentMap (i : Fin (M.componentCount a)) :
    Ordinary.Locus.CM.componentFiber R a i ⟶ (geometricAlbaneseFactors R a i).X :=
  (Over.pullback R.geometricBase).map ((M.components a).a i)

def ordinaryPoints := Σ i : Fin (M.componentCount a),
  {p : Geometric.PointExt.CM.pointBase (residueClosure (q := q)) ⟶ Ordinary.Locus.CM.componentFiber R a i //
    p.left (IsLocalRing.closedPoint (residueClosure (q := q))) ∈ Ordinary.Locus.CM.componentOrdinaryLocus R a i}

def ordinaryAlbanesePoint (p : ordinaryPoints R a) :
    Additive (Geometric.PointExt.CM.pointBase (residueClosure (q := q)) ⟶ (geometricAlbanese R a).X) :=
  Additive.ofMul (p.2.val ≫ geometricComponentMap R a p.1 ≫
    ProductPoints.CM.factorMap (geometricAlbaneseFactors R a) p.1)

theorem geometric_factor_geometry
    (hA : ∀ i, AlbaneseProduct.CM.GoodGroupGeometry ((M.components a).A i).X)
    (i : Fin (M.componentCount a)) : AlbaneseProduct.CM.GoodGroupGeometry (geometricAlbaneseFactors R a i).X := by
  let : Smooth ((M.components a).A i).X.hom := (hA i).1
  let : IsProper ((M.components a).A i).X.hom := (hA i).2.1
  let : GeometricallyConnected ((M.components a).A i).X.hom := (hA i).2.2
  change Smooth (CategoryTheory.Limits.pullback.snd ((M.components a).A i).X.hom R.geometricBase) ∧
    IsProper (CategoryTheory.Limits.pullback.snd ((M.components a).A i).X.hom R.geometricBase) ∧
    GeometricallyConnected
      (CategoryTheory.Limits.pullback.snd ((M.components a).A i).X.hom R.geometricBase)
  exact ⟨inferInstance, inferInstance, inferInstance⟩

theorem detection_from_IntegralModel_CMPoints
    (hS : ∀ i, Smooth ((M.components a).S i).hom)
    (hA : ∀ i, AlbaneseProduct.CM.GoodGroupGeometry ((M.components a).A i).X)
    (hgenerate : ∀ i, ∃ n : ℕ, 0 < n ∧
      ∀ t : PELModuli.IntegralModel.Base.GeometricPoint M.arithmetic.base,
        Function.Surjective ((M.components a).sumOfDifferences i n t))
    (ho : IsOpen (R.ordinaryLocus a))
    (hd : ∀ x : R.geom a, Dense {y : connectedComponent x | R.IsOrdinary a y.val})
    (f : AbelianScheme.TateComparison.End.IntegralEnd (geometricAlbanese R a).X)
    (h : ∀ x y : ordinaryPoints R a, x.1 = y.1 →
      PointEvaluationCM.CM.pointAction (geometricAlbanese R a).X f
        (ordinaryAlbanesePoint R a x - ordinaryAlbanesePoint R a y) = 0) : f = 0 := by
  let : IsDomain M.arithmetic.R := Localization.Away.isDomain
    (Nat.cast_ne_zero.mpr M.arithmetic.denominator_ne_zero)
  let : ∀ i, Smooth (Ordinary.Locus.CM.componentFiber R a i).hom := fun i => by
    let : Smooth ((M.components a).S i).hom := hS i
    exact inferInstanceAs
      (Smooth (CategoryTheory.Limits.pullback.snd ((M.components a).S i).hom R.geometricBase))
  let : ∀ i, IsReduced (Ordinary.Locus.CM.componentFiber R a i).left :=
    fun i => ArithmeticGeometry.OrdinaryLocus.Openness.SmoothReduced.Construction.isReduced_smooth_over_field (Ordinary.Locus.CM.componentFiber R a i).hom
  have hG := AlbaneseProduct.CM.component_product_geometry (geometricAlbaneseFactors R a)
    (geometric_factor_geometry R a hA)
  let : Smooth (AbelianScheme.TateComparison.Products.componentProduct (geometricAlbaneseFactors R a)).X.hom := hG.1
  let : IsProper (AbelianScheme.TateComparison.Products.componentProduct (geometricAlbaneseFactors R a)).X.hom := hG.2.1
  let : IsReduced (AbelianScheme.TateComparison.Products.componentProduct (geometricAlbaneseFactors R a)).X.left :=
    ArithmeticGeometry.OrdinaryLocus.Openness.SmoothReduced.Construction.isReduced_smooth_over_field
      (AbelianScheme.TateComparison.Products.componentProduct (geometricAlbaneseFactors R a)).X.hom
  let U : ∀ i, (Ordinary.Locus.CM.componentFiber R a i).left.Opens := fun i =>
    ⟨Ordinary.Locus.CM.componentOrdinaryLocus R a i, (Ordinary.Locus.CM.componentOrdinaryLocus_open_dense R a ho hd i).1⟩
  let n : Fin (M.componentCount a) → ℕ := fun i => (hgenerate i).choose
  have hn : ∀ i, Function.Surjective (fun z : Fin (n i) →
      (Geometric.PointExt.CM.pointBase (residueClosure (q := q)) ⟶ Ordinary.Locus.CM.componentFiber R a i) ×
      (Geometric.PointExt.CM.pointBase (residueClosure (q := q)) ⟶ Ordinary.Locus.CM.componentFiber R a i) =>
      ∑ v, (Additive.ofMul ((z v).1 ≫ geometricComponentMap R a i) -
        Additive.ofMul ((z v).2 ≫ geometricComponentMap R a i))) := by
    intro i
    let : Smooth ((M.components a).A i).X.hom := (hA i).1
    let : IsProper ((M.components a).A i).X.hom := (hA i).2.1
    let : GeometricallyConnected ((M.components a).A i).X.hom := (hA i).2.2
    let t : PELModuli.IntegralModel.Base.GeometricPoint M.arithmetic.base :=
      ⟨residueClosure (q := q), R.geometricBase⟩
    exact FiberGeneration.CM.component_generation_on_fiber (M.components a) i t (n i)
      ((hgenerate i).choose_spec.2 t)
  apply ProductDetection.CM.product_end_eq_zero_of_ordinary_differences (geometricAlbaneseFactors R a)
    (Ordinary.Locus.CM.componentFiber R a) (geometricComponentMap R a) U
    (fun i => (Ordinary.Locus.CM.componentOrdinaryLocus_open_dense R a ho hd i).2) n hn f
  intro i p z hp hz
  exact h ⟨i, p, hp⟩ ⟨i, z, hz⟩ rfl

end

end OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Intrinsic.Detection.CM
