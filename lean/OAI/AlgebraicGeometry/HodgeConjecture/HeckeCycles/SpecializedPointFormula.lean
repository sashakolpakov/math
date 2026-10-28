import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.ValuativePoints

/-! # Specialized Point Formula -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.SpecializedPointFormula.CM

noncomputable section

/-! Transfer evaluated pointwise Hecke identities by the actual proper
specialization map. Naturality of integral endomorphisms and additivity
preserve every term of the generic neighbor multiset. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj
open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.PointSpecializationFormula.CM.Points
open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.ValuativePoints.CM

variable {R L : Type} [CommRing R] [IsDomain R] [ValuationRing R]
  [Field L] [Algebra R L] [IsFractionRing R L]
  {S : Scheme} (b : Spec (.of R) ⟶ S)
  (G : CommGrp (Over S)) [IsProper G.X.hom]

theorem extendGroup_evaluate (f : AbelianScheme.TateComparison.End.IntegralEnd G.X)
    (z : Additive (ValuativePoints.CM.genericTest (L := L) b ⟶ G.X)) :
    (ValuativePoints.CM.evaluatedGroupEquiv b G).symm (PointSpecializationFormula.CM.Points.evaluateAt G (ValuativePoints.CM.genericTest b) f z) =
      PointSpecializationFormula.CM.Points.evaluateAt G (Over.mk b) f ((ValuativePoints.CM.evaluatedGroupEquiv b G).symm z) := by
  apply (ValuativePoints.CM.evaluatedGroupEquiv (L := L) b G).injective
  rw [AddEquiv.apply_symm_apply]
  change PointSpecializationFormula.CM.Points.evaluateAt G (ValuativePoints.CM.genericTest b) f z =
    Additive.ofMul (ValuativePoints.CM.restrictTest b ≫
      (PointSpecializationFormula.CM.Points.evaluateAt G (Over.mk b) f ((ValuativePoints.CM.evaluatedGroupEquiv b G).symm z)).toMul)
  rw [← PointSpecializationFormula.CM.Points.evaluate_precomp]
  change PointSpecializationFormula.CM.Points.evaluateAt G (ValuativePoints.CM.genericTest b) f z =
    PointSpecializationFormula.CM.Points.evaluateAt G (ValuativePoints.CM.genericTest b) f
      (ValuativePoints.CM.evaluatedGroupEquiv b G ((ValuativePoints.CM.evaluatedGroupEquiv b G).symm z))
  rw [AddEquiv.apply_symm_apply]

variable {k : Type} [Field k] (res : R →+* k)

theorem specializeGroup_evaluate (f : AbelianScheme.TateComparison.End.IntegralEnd G.X)
    (z : Additive (ValuativePoints.CM.genericTest (L := L) b ⟶ G.X)) :
    ValuativePoints.CM.specializeGroup b G res (PointSpecializationFormula.CM.Points.evaluateAt G (ValuativePoints.CM.genericTest b) f z) =
      PointSpecializationFormula.CM.Points.evaluateAt G (ValuativePoints.CM.specialTest b res) f (ValuativePoints.CM.specializeGroup b G res z) := by
  change ValuativePoints.CM.reduceIntegralGroup b G res
    ((ValuativePoints.CM.evaluatedGroupEquiv b G).symm (PointSpecializationFormula.CM.Points.evaluateAt G (ValuativePoints.CM.genericTest b) f z)) = _
  rw [extendGroup_evaluate]
  exact (PointSpecializationFormula.CM.Points.evaluate_precomp G (ValuativePoints.CM.reductionTest b res) f
    ((ValuativePoints.CM.evaluatedGroupEquiv b G).symm z)).symm

variable {X : Over S} [IsProper X.hom] (a : X ⟶ G.X)

theorem specializeGroup_neighbor_sum
    (N : Multiset (ValuativePoints.CM.genericTest (L := L) b ⟶ X)) :
    ValuativePoints.CM.specializeGroup b G res ((N.map (fun z => Additive.ofMul (z ≫ a))).sum) =
      (N.map (fun z => Additive.ofMul (ValuativePoints.CM.specializePoint b res X z ≫ a))).sum := by
  rw [map_multiset_sum, Multiset.map_map]
  apply congrArg Multiset.sum
  apply Multiset.map_congr rfl
  intro z _
  exact ValuativePoints.CM.specializeGroup_map b G res a z

theorem specialized_neighbor_formula
    (f : AbelianScheme.TateComparison.End.IntegralEnd G.X) (x y : ValuativePoints.CM.genericTest (L := L) b ⟶ X)
    (Nx Ny : Multiset (ValuativePoints.CM.genericTest (L := L) b ⟶ X))
    (h : PointSpecializationFormula.CM.Points.evaluateAt G (ValuativePoints.CM.genericTest b) f
      (Additive.ofMul (x ≫ a) - Additive.ofMul (y ≫ a)) =
        (Nx.map (fun z => Additive.ofMul (z ≫ a))).sum -
          (Ny.map (fun z => Additive.ofMul (z ≫ a))).sum) :
    PointSpecializationFormula.CM.Points.evaluateAt G (ValuativePoints.CM.specialTest b res) f
      (Additive.ofMul (ValuativePoints.CM.specializePoint b res X x ≫ a) -
        Additive.ofMul (ValuativePoints.CM.specializePoint b res X y ≫ a)) =
      (Nx.map (fun z => Additive.ofMul (ValuativePoints.CM.specializePoint b res X z ≫ a))).sum -
        (Ny.map (fun z => Additive.ofMul (ValuativePoints.CM.specializePoint b res X z ≫ a))).sum := by
  simpa only [specializeGroup_evaluate, map_sub, ValuativePoints.CM.specializeGroup_map,
    specializeGroup_neighbor_sum] using congrArg (ValuativePoints.CM.specializeGroup b G res) h

end

end OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.SpecializedPointFormula.CM
