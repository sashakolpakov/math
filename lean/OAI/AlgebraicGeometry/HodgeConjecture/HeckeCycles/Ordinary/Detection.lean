import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.PointEvaluationCM

/-! # Detection -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Ordinary.Detection.CM

noncomputable section

/-! Dense ordinary points detect the vanishing of Albanese differences.
All points below are morphisms from the actual algebraically closed
residue field, and all endomorphisms are algebraic group endomorphisms. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj
open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Geometric.PointExt.CM
open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.PointEvaluationCM.CM

variable {k : Type} [Field k] [IsAlgClosed k]

def structurePointMap (X : Over (Spec (.of k))) : X ⟶ Geometric.PointExt.CM.pointBase k :=
  Over.homMk X.hom (Category.comp_id _)

omit [IsAlgClosed k] in
@[simp] theorem point_structurePointMap {X : Over (Spec (.of k))}
    (p : Geometric.PointExt.CM.pointBase k ⟶ X) : p ≫ structurePointMap X = 𝟙 _ := by
  apply Over.OverMorphism.ext
  exact p.w

theorem exists_point_in_dense_open
    {X : Over (Spec (.of k))} [LocallyOfFiniteType X.hom]
    (U : X.left.Opens) (hU : Dense (U : Set X.left))
    (p : Geometric.PointExt.CM.pointBase k ⟶ X) :
    ∃ r : Geometric.PointExt.CM.pointBase k ⟶ X, r.left (IsLocalRing.closedPoint k) ∈ U := by
  let : Nonempty X.left := ⟨p.left (IsLocalRing.closedPoint k)⟩
  let : JacobsonSpace X.left := LocallyOfFiniteType.jacobsonSpace X.hom
  obtain ⟨x, hx, hc⟩ := nonempty_inter_closedPoints hU.nonempty U.isOpen.isLocallyClosed
  change IsClosed {x} at hc
  refine ⟨Over.homMk (pointOfClosedPoint X.hom x hc)
    (pointOfClosedPoint_comp X.hom x hc), ?_⟩
  have he := pointOfClosedPoint_apply X.hom x hc
    (show Spec (.of k) from IsLocalRing.closedPoint k)
  exact he.symm ▸ hx

theorem equal_on_dense_open_implies_equal_on_points
    {X Y : Over (Spec (.of k))} [IsReduced X.left]
    [LocallyOfFiniteType X.hom] [LocallyOfFiniteType Y.hom] [IsSeparated Y.hom]
    (f : X ⟶ Y) (U : X.left.Opens) (hU : Dense (U : Set X.left))
    (h : ∀ p q : Geometric.PointExt.CM.pointBase k ⟶ X,
      p.left (IsLocalRing.closedPoint k) ∈ U →
      q.left (IsLocalRing.closedPoint k) ∈ U → p ≫ f = q ≫ f)
    (p q : Geometric.PointExt.CM.pointBase k ⟶ X) : p ≫ f = q ≫ f := by
  obtain ⟨r, hr⟩ := exists_point_in_dense_open U hU p
  have hf : f = structurePointMap X ≫ r ≫ f := by
    apply Geometric.PointExt.CM.over_hom_ext_on_dense_open _ _ U hU
    intro x hx
    simpa only [← Category.assoc, point_structurePointMap, Category.id_comp]
      using h x r hx hr
  calc
    p ≫ f = p ≫ (structurePointMap X ≫ r ≫ f) := congrArg (p ≫ ·) hf
    _ = r ≫ f := by simp only [← Category.assoc, point_structurePointMap, Category.id_comp]
    _ = q ≫ (structurePointMap X ≫ r ≫ f) := by
      simp only [← Category.assoc, point_structurePointMap, Category.id_comp]
    _ = q ≫ f := congrArg (q ≫ ·) hf.symm

theorem kills_all_differences_of_ordinary
    {X G : Over (Spec (.of k))} [IsReduced X.left]
    [LocallyOfFiniteType X.hom] [LocallyOfFiniteType G.hom] [IsSeparated G.hom]
    [GrpObj G] [IsCommMonObj G]
    (a : X ⟶ G) (U : X.left.Opens) (hU : Dense (U : Set X.left))
    (f : AbelianScheme.TateComparison.End.IntegralEnd G)
    (h : ∀ p q : Geometric.PointExt.CM.pointBase k ⟶ X,
      p.left (IsLocalRing.closedPoint k) ∈ U →
      q.left (IsLocalRing.closedPoint k) ∈ U →
      PointEvaluationCM.CM.pointAction G f (Additive.ofMul (p ≫ a) - Additive.ofMul (q ≫ a)) = 0)
    (p q : Geometric.PointExt.CM.pointBase k ⟶ X) :
    PointEvaluationCM.CM.pointAction G f (Additive.ofMul (p ≫ a) - Additive.ofMul (q ≫ a)) = 0 := by
  have hh : ∀ x y : Geometric.PointExt.CM.pointBase k ⟶ X,
      x.left (IsLocalRing.closedPoint k) ∈ U →
      y.left (IsLocalRing.closedPoint k) ∈ U →
      x ≫ (a ≫ AbelianScheme.TateComparison.End.endSchemeMap G f) = y ≫ (a ≫ AbelianScheme.TateComparison.End.endSchemeMap G f) := by
    intro x y hx hy
    have he := h x y hx hy
    rw [map_sub, sub_eq_zero] at he
    have hp := congrArg Additive.toMul he
    exact ((AbelianScheme.TateComparison.End.endSchemeMap_points G f _ (x ≫ a)).symm.trans
      (hp.trans (AbelianScheme.TateComparison.End.endSchemeMap_points G f _ (y ≫ a))))
  have he := equal_on_dense_open_implies_equal_on_points
    (a ≫ AbelianScheme.TateComparison.End.endSchemeMap G f) U hU hh p q
  rw [map_sub, sub_eq_zero]
  apply Additive.toMul.injective
  exact (AbelianScheme.TateComparison.End.endSchemeMap_points G f _ (p ≫ a)).trans
    (he.trans (AbelianScheme.TateComparison.End.endSchemeMap_points G f _ (q ≫ a)).symm)

theorem end_eq_zero_of_ordinary_differences
    {X G : Over (Spec (.of k))} [IsReduced X.left] [IsReduced G.left]
    [LocallyOfFiniteType X.hom] [LocallyOfFiniteType G.hom] [IsSeparated G.hom]
    [GrpObj G] [IsCommMonObj G]
    (a : X ⟶ G) (U : X.left.Opens) (hU : Dense (U : Set X.left))
    (n : ℕ)
    (hgenerate : Function.Surjective (fun z : Fin n →
      (Geometric.PointExt.CM.pointBase k ⟶ X) × (Geometric.PointExt.CM.pointBase k ⟶ X) =>
        ∑ i, (Additive.ofMul ((z i).1 ≫ a) - Additive.ofMul ((z i).2 ≫ a))))
    (f : AbelianScheme.TateComparison.End.IntegralEnd G)
    (h : ∀ p q : Geometric.PointExt.CM.pointBase k ⟶ X,
      p.left (IsLocalRing.closedPoint k) ∈ U →
      q.left (IsLocalRing.closedPoint k) ∈ U →
      PointEvaluationCM.CM.pointAction G f (Additive.ofMul (p ≫ a) - Additive.ofMul (q ≫ a)) = 0) :
    f = 0 := by
  apply PointEvaluationCM.CM.end_eq_zero_of_points G f
  intro x
  obtain ⟨z, rfl⟩ := hgenerate x
  rw [map_sum]
  apply Finset.sum_eq_zero
  intro i _
  exact kills_all_differences_of_ordinary a U hU f h (z i).1 (z i).2

end

end OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Ordinary.Detection.CM
