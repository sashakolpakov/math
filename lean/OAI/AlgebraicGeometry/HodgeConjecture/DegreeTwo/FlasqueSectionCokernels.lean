import OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.ThomGoodShiftFlasque

/-! # Flasque Section Cokernels -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.FlasqueSectionCokernels.Constructions

noncomputable section

/-! Actual open sections preserve the incoming cokernels below the first cohomology sheaf. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.TopologicalSpace Opposite

set_option backward.isDefEq.respectTransparency false

variable {X : TopCat.{0}}

theorem rationalFlasqueSequence_sections_shortExact (U : Opens X)
    (S : ShortComplex (TopCat.Sheaf (ModuleCat.{0} ℚ) X)) (hS : S.ShortExact)
    [TopCat.Sheaf.IsFlasque S.X₁] : (S.map (CycleClass.Geometric.SheafClosedSupport.Cohomology.moduleSheafSections U)).ShortExact := by
  have hleft := (Functor.preservesFiniteLimits_iff_forall_exact_map_and_mono
    (CycleClass.Geometric.SheafClosedSupport.Cohomology.moduleSheafSections U)).mp inferInstance S hS
  have := hS.mono_f
  have := hS.epi_g
  have hA : (S.map (AlgebraicTopology.DeRham.Comparison.RationalSheafForget.rationalSheafForget X)).ShortExact := hS.map (AlgebraicTopology.DeRham.Comparison.RationalSheafForget.rationalSheafForget X)
  have : TopCat.Sheaf.IsFlasque (S.map (AlgebraicTopology.DeRham.Comparison.RationalSheafForget.rationalSheafForget X)).X₁ :=
    AlgebraicTopology.DeRham.Comparison.RationalSheafForget.rationalSheafForget_isFlasque S.X₁
  have hE : Epi (((S.map (AlgebraicTopology.DeRham.Comparison.RationalSheafForget.rationalSheafForget X)).g).hom.app (op U)) :=
    TopCat.Sheaf.IsFlasque.epi_of_shortExact hA
  have hQ : Epi ((CycleClass.Geometric.SheafClosedSupport.Cohomology.moduleSheafSections U).map S.g) := AlgebraicTopology.DeRham.Comparison.RationalSheafForget.rationalForget.epi_of_epi_map hE
  exact ShortComplex.ShortExact.mk' hleft.1 hleft.2 hQ

variable (K : CochainComplex (TopCat.Sheaf (ModuleCat.{0} ℚ) X) ℕ)
variable (hK : ∀ n, TopCat.Sheaf.IsFlasque (K.X n))
variable (k : ℕ) (he : ∀ n, n<k → K.ExactAt n)

include hK he

theorem rationalFlasqueSections_pOpcycles_epi (U : Opens X) (n : ℕ) (hn : n≤k) :
    Epi ((CycleClass.Geometric.SheafClosedSupport.Cohomology.moduleSheafSections U).map (K.pOpcycles n)) := by
  cases n with
  | zero => infer_instance
  | succ n =>
    have := ThomGoodShiftFlasque.Constructions.rationalFlasque_opcycles_of_exact_below K hK k he n (Nat.le_of_succ_le hn)
    exact (rationalFlasqueSequence_sections_shortExact U (CycleClass.Geometric.FlasqueLowDegree.Cycles.opcyclesSuccessorSequence K n)
      (CycleClass.Geometric.FlasqueLowDegree.Cycles.opcyclesSuccessorSequence_shortExact K n (he n (Nat.lt_of_succ_le hn)))).epi_g

theorem rationalFlasqueSections_preserves_incoming_cokernel (U : Opens X) (n : ℕ) (hn : n≤k) :
    PreservesColimit (parallelPair (K.sc n).f 0) (CycleClass.Geometric.SheafClosedSupport.Cohomology.moduleSheafSections U) := by
  cases n with
  | zero =>
    apply preservesCokernel_zero'
    change K.d ((ComplexShape.up ℕ).prev 0) 0 = 0
    simp
  | succ n =>
    change PreservesColimit (parallelPair (K.d ((ComplexShape.up ℕ).prev (n+1)) (n+1)) 0)
      (CycleClass.Geometric.SheafClosedSupport.Cohomology.moduleSheafSections U)
    rw [CochainComplex.prev_nat_succ]
    have := ThomGoodShiftFlasque.Constructions.rationalFlasque_opcycles_of_exact_below K hK k he n (Nat.le_of_succ_le hn)
    have := rationalFlasqueSections_pOpcycles_epi K hK k he U n (Nat.le_of_succ_le hn)
    let S := CycleClass.Geometric.FlasqueLowDegree.Cycles.opcyclesSuccessorSequence K n
    have hS := rationalFlasqueSequence_sections_shortExact U S
      (CycleClass.Geometric.FlasqueLowDegree.Cycles.opcyclesSuccessorSequence_shortExact K n (he n (Nat.lt_of_succ_le hn)))
    have := hS.epi_g
    refine preservesColimit_of_preserves_colimit_cocone
      (K.opcyclesIsCokernel n (n+1) (by simp)) ?_
    apply (CokernelCofork.isColimitMapCoconeEquiv _ (CycleClass.Geometric.SheafClosedSupport.Cohomology.moduleSheafSections U)).2
    exact isCokernelEpiComp hS.exact.gIsCokernel
      ((CycleClass.Geometric.SheafClosedSupport.Cohomology.moduleSheafSections U).map (K.pOpcycles n)) (by
        change (CycleClass.Geometric.SheafClosedSupport.Cohomology.moduleSheafSections U).map (K.d n (n+1)) =
          (CycleClass.Geometric.SheafClosedSupport.Cohomology.moduleSheafSections U).map (K.pOpcycles n) ≫
            (CycleClass.Geometric.SheafClosedSupport.Cohomology.moduleSheafSections U).map (K.fromOpcycles n (n+1))
        rw [← Functor.map_comp, HomologicalComplex.p_fromOpcycles])

theorem rationalFlasqueSections_preservesRightHomologyOf (U : Opens X) (n : ℕ) (hn : n≤k) :
    (CycleClass.Geometric.SheafClosedSupport.Cohomology.moduleSheafSections U).PreservesRightHomologyOf (K.sc n) := by
  have := rationalFlasqueSections_preserves_incoming_cokernel K hK k he U n hn
  constructor
  intro h
  exact { f := inferInstance, g' := inferInstance }

def rationalFlasqueSections_opcyclesIso (U : Opens X) (n : ℕ) (hn : n≤k) :
    (CycleClass.Geometric.SupportStalkVanishes.Cohomology.moduleSheafSectionsComplex U K).opcycles n ≅ (CycleClass.Geometric.SheafClosedSupport.Cohomology.moduleSheafSections U).obj (K.opcycles n) := by
  have := rationalFlasqueSections_preservesRightHomologyOf K hK k he U n hn
  exact (K.sc n).mapOpcyclesIso (CycleClass.Geometric.SheafClosedSupport.Cohomology.moduleSheafSections U)

end

end OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.FlasqueSectionCokernels.Constructions
