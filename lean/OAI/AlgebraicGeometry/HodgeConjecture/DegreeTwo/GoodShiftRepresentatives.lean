import OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.GoodShiftCohomology

/-! # Good Shift Representatives -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.GoodShiftRepresentatives.Constructions

noncomputable section

/-! The canonical good shift sends an actual cocycle to the same cohomology class. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits

set_option backward.isDefEq.respectTransparency false

variable {R : Type} [Ring R] (K : CochainComplex (ModuleCat.{0} R) ℕ) (k n : ℕ)

def cochainRestrictedCocycle (c : AlgebraicTopology.Cohomology.Singular.Representatives.cochainCocycles K (k+n)) :
    AlgebraicTopology.Cohomology.Singular.Representatives.cochainCocycles (K.restriction (RelativeCupHomotopy.Constructions.cochainDegreeShiftEmbedding k)) n :=
  ⟨c.val, by
    rw [AlgebraicTopology.Cohomology.Singular.Representatives.mem_cochainCocycles_iff]
    exact (AlgebraicTopology.Cohomology.Singular.Representatives.mem_cochainCocycles_iff K (k+n) c.val).mp c.property⟩

def cochainGoodShiftCocycle (c : AlgebraicTopology.Cohomology.Singular.Representatives.cochainCocycles K (k+n)) :
    AlgebraicTopology.Cohomology.Singular.Representatives.cochainCocycles (K.truncGE' (RelativeCupHomotopy.Constructions.cochainDegreeShiftEmbedding k)) n :=
  AlgebraicTopology.Cohomology.Singular.RepresentativesNaturality.cochainCocycleMap (K.restrictionToTruncGE' (RelativeCupHomotopy.Constructions.cochainDegreeShiftEmbedding k)) n
    (cochainRestrictedCocycle K k n c)

theorem cochainGoodShiftCocycle_cycles (c : AlgebraicTopology.Cohomology.Singular.Representatives.cochainCocycles K (k+n)) :
    ((K.truncGE' (RelativeCupHomotopy.Constructions.cochainDegreeShiftEmbedding k)).sc n).moduleCatCyclesIso.inv
        (cochainGoodShiftCocycle K k n c) =
      GoodShiftCohomology.Constructions.cochainGoodShiftCyclesMap K k n ((K.sc (k+n)).moduleCatCyclesIso.inv c) := by
  let T := K.truncGE' (RelativeCupHomotopy.Constructions.cochainDegreeShiftEmbedding k)
  apply (ModuleCat.mono_iff_injective (T.iCycles n)).mp inferInstance
  have hT := ConcreteCategory.congr_hom ((T.sc n).moduleCatCyclesIso_inv_iCycles)
    (cochainGoodShiftCocycle K k n c)
  have hK := ConcreteCategory.congr_hom ((K.sc (k+n)).moduleCatCyclesIso_inv_iCycles) c
  have hs := ConcreteCategory.congr_hom (GoodShiftCohomology.Constructions.cochainGoodShiftCyclesMap_inclusion K k n)
    ((K.sc (k+n)).moduleCatCyclesIso.inv c)
  change T.iCycles n ((T.sc n).moduleCatCyclesIso.inv (cochainGoodShiftCocycle K k n c)) =
    (K.restrictionToTruncGE' (RelativeCupHomotopy.Constructions.cochainDegreeShiftEmbedding k)).f n c.val at hT
  change K.iCycles (k+n) ((K.sc (k+n)).moduleCatCyclesIso.inv c) = c.val at hK
  change T.iCycles n (GoodShiftCohomology.Constructions.cochainGoodShiftCyclesMap K k n ((K.sc (k+n)).moduleCatCyclesIso.inv c)) =
    (K.restrictionToTruncGE' (RelativeCupHomotopy.Constructions.cochainDegreeShiftEmbedding k)).f n
      (K.iCycles (k+n) ((K.sc (k+n)).moduleCatCyclesIso.inv c)) at hs
  rw [hK] at hs
  exact hT.trans hs.symm

theorem cochainGoodShiftHomologyIso_class (c : AlgebraicTopology.Cohomology.Singular.Representatives.cochainCocycles K (k+n)) :
    (GoodShiftCohomology.Constructions.cochainGoodShiftHomologyIso K k n).hom
        (AlgebraicTopology.Cohomology.Singular.Representatives.cochainClass (K.truncGE' (RelativeCupHomotopy.Constructions.cochainDegreeShiftEmbedding k)) n (cochainGoodShiftCocycle K k n c)) =
      AlgebraicTopology.Cohomology.Singular.Representatives.cochainClass K (k+n) c := by
  rw [AlgebraicTopology.Cohomology.Singular.Representatives.cochainClass_eq_homologyπ, cochainGoodShiftCocycle_cycles, AlgebraicTopology.Cohomology.Singular.Representatives.cochainClass_eq_homologyπ]
  exact ConcreteCategory.congr_hom (GoodShiftCohomology.Constructions.cochainGoodShiftCyclesMap_homologyπ K k n)
    ((K.sc (k+n)).moduleCatCyclesIso.inv c)

end

end OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.GoodShiftRepresentatives.Constructions
