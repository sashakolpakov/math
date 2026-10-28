import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.FiberGeneration
import OAI.AlgebraicGeometry.PELModuli.CMPoints.Models
import OAI.ArithmeticGeometry.OrdinaryLocus.Openness.FiberDimensionCharts

/-! # Residue Point -/

namespace OAI

noncomputable section

namespace AlgebraicGeometry.HodgeConjecture.HeckeCycles.Geometric.ResiduePoint.CM

/-! At an actual rational point over an algebraically closed field,
the canonical algebraic-closure residue point is isomorphic to that
point. This identifies the torsion counts in CMPoints with actual point
functors, without changing their field or adding an ordinarity premise. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj
open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Geometric.PointExt.CM OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.FiberGeneration.CM

variable {k : Type} [Field k] [IsAlgClosed k]
  (X : Over (Spec (.of k))) [LocallyOfFiniteType X.hom]
  (p : PointExt.CM.pointBase k ⟶ X)

def closedPoint : _root_.closedPoints X.left :=
  pointEquivClosedPoint X.hom ⟨p.left, p.w⟩

theorem pointOfClosedPoint_eq :
    AlgebraicGeometry.pointOfClosedPoint X.hom (CM.closedPoint X p).val
      (CM.closedPoint X p).property = p.left :=
  congrArg Subtype.val ((pointEquivClosedPoint X.hom).symm_apply_apply ⟨p.left, p.w⟩)

def residueClosureIso :
    PELModuli.CMPoints.Models.geometricPoint X.left (CM.closedPoint X p).val ≅ Over.mk p.left := by
  let x := (CM.closedPoint X p).val
  let e := residueFieldIsoBase X.hom x (CM.closedPoint X p).property
  let : IsAlgClosed (X.left.residueField x) :=
    IsAlgClosed.of_ringEquiv k _ e.symm.commRingCatIsoToRingEquiv
  let f := CommRingCat.ofHom (algebraMap (X.left.residueField x)
    (AlgebraicClosure (X.left.residueField x)))
  let : IsIso f := (ConcreteCategory.isIso_iff_bijective f).mpr
    IsAlgClosed.algebraMap_bijective_of_isIntegral
  let c : CommRingCat.of k ≅ CommRingCat.of (AlgebraicClosure (X.left.residueField x)) :=
    e.symm ≪≫ asIso f
  refine Over.isoMk (Scheme.Spec.mapIso c.op) ?_
  change Spec.map (e.inv ≫ f) ≫ p.left =
    Spec.map f ≫ X.left.fromSpecResidueField x
  rw [← pointOfClosedPoint_eq X p]
  change Spec.map (e.inv ≫ f) ≫
    (Spec.map e.hom ≫ X.left.fromSpecResidueField x) = _
  rw [← Category.assoc, ← Spec.map_comp]
  simp only [← Category.assoc, e.hom_inv_id, Category.id_comp]

variable (A : Over X.left) [GrpObj A] (n : ℕ)

theorem torsionPointCard_eq :
    Nat.card {z : PELModuli.CMPoints.Models.geometricPoint X.left (CM.closedPoint X p).val ⟶ A // z ^ n = 1} =
      Nat.card {z : Over.mk p.left ⟶ A // z ^ n = 1} := by
  let e := FiberGeneration.CM.testPointMulEquiv (G := A) (residueClosureIso X p)
  apply Nat.card_congr
  exact e.toEquiv.subtypeEquiv (fun z => by
    change z ^ n = 1 ↔ (e z) ^ n = 1
    rw [← map_pow, e.map_eq_one_iff])

end AlgebraicGeometry.HodgeConjecture.HeckeCycles.Geometric.ResiduePoint.CM

namespace AlgebraicGeometry.HodgeConjecture.HeckeCycles.Geometric.ResiduePoint.CM.RationalOrdinary

/-! The ordinary-locus condition at an actual geometric moduli point
is exactly maximal rank of its actual q-torsion point group. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj
open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Geometric.PointExt.CM
open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Geometric.ResiduePoint.CM

variable {k : Type} [Field k] [IsAlgClosed k]
  (X : Over (Spec (.of k))) [LocallyOfFiniteType X.hom]
  {g : ℕ} (A : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme g X.left)

omit [IsAlgClosed k] [LocallyOfFiniteType X.hom] in
theorem fiber_dimension (x : X.left) :
    topologicalKrullDim (A.scheme.hom.fiber x) = (g : WithBot ℕ∞) := by
  let e : A.scheme ⟶ A.scheme := 𝟙 A.scheme
  let : IsOpenImmersion e.left :=
    inferInstanceAs (IsOpenImmersion (𝟙 A.scheme.left))
  apply ArithmeticGeometry.OrdinaryLocus.Openness.FiberDimensionCharts.Construction.dimension_fiber_of_smooth_chart A.scheme A.scheme e g x
  refine ⟨η[A.scheme].left x, ?_⟩
  have h : η[A.scheme].left ≫ A.scheme.hom = 𝟙 X.left := (η[A.scheme]).w
  exact (Scheme.Hom.comp_apply _ _ x).symm.trans
    (congrArg (fun f : X.left ⟶ X.left => f x) h)

theorem isOrdinaryAt_iff_point_count (p : PointExt.CM.pointBase k ⟶ X) (q : ℕ) :
    PELModuli.CMPoints.Models.IsOrdinaryAt q A.scheme (p.left (IsLocalRing.closedPoint k)) ↔
      Nat.card (A.torsionPoints q (Over.mk p.left)) = q ^ g := by
  have hc := torsionPointCard_eq X p A.scheme q
  change Nat.card {z : PELModuli.CMPoints.Models.geometricPoint X.left (p.left (IsLocalRing.closedPoint k)) ⟶ A.scheme //
      z ^ q = 1} = Nat.card (A.torsionPoints q (Over.mk p.left)) at hc
  constructor
  · rintro ⟨d, hd, hn⟩
    have hdg : d = g := by
      exact_mod_cast hd.symm.trans (fiber_dimension X A _)
    subst d
    exact hc.symm.trans hn
  · intro h
    exact ⟨g, fiber_dimension X A _, hc.trans h⟩

end AlgebraicGeometry.HodgeConjecture.HeckeCycles.Geometric.ResiduePoint.CM.RationalOrdinary

end

end OAI
