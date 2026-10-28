import OAI.AlgebraicGeometry.Isogenies.NeighborCounting.IntegralMarking
import OAI.AlgebraicGeometry.AbelianScheme.TateComparison.PELBaseChange

/-! # Marking Base Change -/

namespace OAI.AlgebraicGeometry.Isogenies.NeighborCounting.MarkingBaseChange

noncomputable section

/-! Generic PEL marking equations imply the equations on the actual
pullbacks of every ordered constant level section. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj

open OAI.AlgebraicGeometry.AbelianScheme.TateComparison.PELBaseChange OAI.AlgebraicGeometry.Isogenies.NeighborCounting.IntegralMarking OAI.AlgebraicGeometry.Isogenies.NeighborCounting.IntegralComparison

variable {S T : Scheme} {d N : ℕ} {A : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme d S}

theorem fullLevel_constant_pullback (α : A.FullLevel N) (s : T ⟶ S)
    (c : Multiplicative (Fin (2 * d) → ZMod N)) :
    (Over.pullback s).map
      (α.hom.app (.op (Over.mk (𝟙 S))) (LocallyConstant.const S c)).val =
    ((α.pullback s).hom.app (.op ((Over.pullback s).obj (Over.mk (𝟙 S))))
      (LocallyConstant.const _ c)).val := by
  let U := (Over.pullback s).obj (Over.mk (𝟙 S))
  let j : (Over.map s).obj U ⟶ Over.mk (𝟙 S) :=
    (Over.mapPullbackAdj s).counit.app (Over.mk (𝟙 S))
  apply (A.baseChangePointsEquiv s U).injective
  rw [AbelianScheme.TateComparison.PELBaseChange.fullLevel_pullback_basis]
  have hn := congrArg Subtype.val
    (ConcreteCategory.congr_hom (α.hom.naturality j.op) (LocallyConstant.const S c))
  change (α.hom.app (.op ((Over.map s).obj U)) (LocallyConstant.const _ c)).val =
    j ≫ (α.hom.app (.op (Over.mk (𝟙 S))) (LocallyConstant.const S c)).val at hn
  refine Eq.trans ?_ hn.symm
  apply Over.OverMorphism.ext
  exact CategoryTheory.Limits.pullback.lift_fst _ _ _

variable {R K O : Type} [CommRing R] [Field K] [Algebra R K] [CommRing O]
variable {n : ℕ} {A B : AbelianScheme.TateComparison.PEL.PELFamilyData O d N (Spec (.of R))}

/-- This is derived from the original generic isogeny's full marking,
without assuming integral or special-fiber marking identification. -/
theorem generic_marking_on_constant_sections
    (f : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme.Isogeny A.abelian B.abelian)
    (g : AbelianScheme.TateComparison.PELIsogenies.PELIsogeny (A.pullback (IntegralComparison.genericMap (R := R) (K := K)))
      (B.pullback (IntegralComparison.genericMap (R := R) (K := K))) n)
    (hf : (Over.pullback (IntegralComparison.genericMap (R := R) (K := K))).map f.hom = g.isogeny.hom)
    (c : Multiplicative (Fin (2 * d) → ZMod N)) :
    (Over.pullback (IntegralComparison.genericMap (R := R) (K := K))).map
      (IntegralMarking.constantLevelSection A.marking c ≫ f.hom) =
    (Over.pullback (IntegralComparison.genericMap (R := R) (K := K))).map (IntegralMarking.constantLevelSection B.marking c) := by
  rw [Functor.map_comp, hf]
  exact (congrArg (fun z => z ≫ g.isogeny.hom)
    (fullLevel_constant_pullback A.marking (IntegralComparison.genericMap (R := R) (K := K)) c)).trans
      ((g.marking _ _).trans
        (fullLevel_constant_pullback B.marking (IntegralComparison.genericMap (R := R) (K := K)) c).symm)

end

end OAI.AlgebraicGeometry.Isogenies.NeighborCounting.MarkingBaseChange
