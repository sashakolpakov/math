import OAI.AlgebraicGeometry.CycleClass.Geometric.FlasqueSectionComparison

/-! # Flasque Comparison -/

namespace OAI.AlgebraicGeometry.DivisorClass.Chern.Open.FlasqueComparison

noncomputable section

/-!
# ChernClass: the canonical first-cohomology comparison on every open set

Flasqueness gives the required cokernel surjections on any open set. Hence
the actual section comparison is invertible in the first possible degree,
with the original rational sheaf and section maps throughout.
-/

open _root_.CategoryTheory _root_.CategoryTheory.Limits Opposite _root_.TopologicalSpace
open OAI.AlgebraicGeometry.CycleClass.Geometric.FlasqueSectionComparison.Cycles

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

variable {X : TopCat.{0}}

instance additiveOpenSections_preservesFiniteLimits (U : Opens X) :
    PreservesFiniteLimits (AlgebraicTopology.DeRham.Comparison.RationalSheafForget.additiveSheafSections U) := by
  have : PreservesFiniteLimits (TopCat.Sheaf.forget AddCommGrpCat X) := inferInstance
  have : PreservesFiniteLimits
      ((evaluation (Opens X)ᵒᵖ AddCommGrpCat).obj (op U)) := inferInstance
  exact comp_preservesFiniteLimits (TopCat.Sheaf.forget AddCommGrpCat X)
    ((evaluation (Opens X)ᵒᵖ AddCommGrpCat).obj (op U))

theorem flasqueSequence_open_shortExact (U : Opens X)
    (S : ShortComplex (TopCat.Sheaf AddCommGrpCat X))
    (hS : S.ShortExact) [TopCat.Sheaf.IsFlasque S.X₁] :
    (S.map (AlgebraicTopology.DeRham.Comparison.RationalSheafForget.additiveSheafSections U)).ShortExact := by
  have hleft := (Functor.preservesFiniteLimits_iff_forall_exact_map_and_mono
    (AlgebraicTopology.DeRham.Comparison.RationalSheafForget.additiveSheafSections U)).1 inferInstance S hS
  exact ShortComplex.ShortExact.mk' hleft.1 hleft.2
    (TopCat.Sheaf.IsFlasque.epi_of_shortExact hS)

theorem epi_openSections_pOpcycles (U : Opens X)
    (K : CochainComplex (TopCat.Sheaf AddCommGrpCat X) ℕ)
    (hK : ∀ j, TopCat.Sheaf.IsFlasque (K.X j))
    (d : ℕ) (he : ∀ j, j < d → K.ExactAt j) (n : ℕ) (hn : n ≤ d) :
    Epi ((AlgebraicTopology.DeRham.Comparison.RationalSheafForget.additiveSheafSections U).map (K.pOpcycles n)) := by
  cases n with
  | zero => infer_instance
  | succ n =>
      have := CycleClass.Geometric.FlasqueLowDegree.Cycles.flasque_opcycles_of_exact_below K hK d he n (Nat.le_of_succ_le hn)
      exact (flasqueSequence_open_shortExact U (CycleClass.Geometric.FlasqueLowDegree.Cycles.opcyclesSuccessorSequence K n)
        (CycleClass.Geometric.FlasqueLowDegree.Cycles.opcyclesSuccessorSequence_shortExact K n (he n (Nat.lt_of_succ_le hn)))).epi_g

theorem openSections_preserves_incoming_cokernel (U : Opens X)
    (K : CochainComplex (TopCat.Sheaf AddCommGrpCat X) ℕ)
    (hK : ∀ j, TopCat.Sheaf.IsFlasque (K.X j))
    (d : ℕ) (he : ∀ j, j < d → K.ExactAt j) (n : ℕ) (hn : n ≤ d) :
    PreservesColimit (parallelPair (K.sc n).f 0) (AlgebraicTopology.DeRham.Comparison.RationalSheafForget.additiveSheafSections U) := by
  cases n with
  | zero =>
      apply preservesCokernel_zero'
      change K.d ((ComplexShape.up ℕ).prev 0) 0 = 0
      simp
  | succ n =>
      change PreservesColimit
        (parallelPair (K.d ((ComplexShape.up ℕ).prev (n + 1)) (n + 1)) 0)
        (AlgebraicTopology.DeRham.Comparison.RationalSheafForget.additiveSheafSections U)
      rw [CochainComplex.prev_nat_succ]
      have := CycleClass.Geometric.FlasqueLowDegree.Cycles.flasque_opcycles_of_exact_below K hK d he n (Nat.le_of_succ_le hn)
      have := epi_openSections_pOpcycles U K hK d he n (Nat.le_of_succ_le hn)
      let S := CycleClass.Geometric.FlasqueLowDegree.Cycles.opcyclesSuccessorSequence K n
      have hS := flasqueSequence_open_shortExact U S
        (CycleClass.Geometric.FlasqueLowDegree.Cycles.opcyclesSuccessorSequence_shortExact K n (he n (Nat.lt_of_succ_le hn)))
      have := hS.epi_g
      refine preservesColimit_of_preserves_colimit_cocone
        (K.opcyclesIsCokernel n (n + 1) (by simp)) ?_
      apply (CokernelCofork.isColimitMapCoconeEquiv _ (AlgebraicTopology.DeRham.Comparison.RationalSheafForget.additiveSheafSections U)).2
      exact isCokernelEpiComp hS.exact.gIsCokernel
        ((AlgebraicTopology.DeRham.Comparison.RationalSheafForget.additiveSheafSections U).map (K.pOpcycles n)) (by
          change (AlgebraicTopology.DeRham.Comparison.RationalSheafForget.additiveSheafSections U).map (K.d n (n + 1)) =
            (AlgebraicTopology.DeRham.Comparison.RationalSheafForget.additiveSheafSections U).map (K.pOpcycles n) ≫
              (AlgebraicTopology.DeRham.Comparison.RationalSheafForget.additiveSheafSections U).map (K.fromOpcycles n (n + 1))
          rw [← Functor.map_comp, HomologicalComplex.p_fromOpcycles])

theorem openSections_preservesRightHomologyOf (U : Opens X)
    (K : CochainComplex (TopCat.Sheaf AddCommGrpCat X) ℕ)
    (hK : ∀ j, TopCat.Sheaf.IsFlasque (K.X j))
    (d : ℕ) (he : ∀ j, j < d → K.ExactAt j) (n : ℕ) (hn : n ≤ d) :
    (AlgebraicTopology.DeRham.Comparison.RationalSheafForget.additiveSheafSections U).PreservesRightHomologyOf (K.sc n) := by
  have := openSections_preserves_incoming_cokernel U K hK d he n hn
  constructor
  intro h
  exact { f := inferInstance, g' := inferInstance }

/-- The original rational section comparison is invertible on every open
in the first possible cohomology degree. -/
theorem rationalFlasqueOpenSectionMap_isIso (U : Opens X)
    (K : CochainComplex (TopCat.Sheaf (ModuleCat ℚ) X) ℕ)
    (hK : ∀ j, TopCat.Sheaf.IsFlasque (K.X j))
    (d : ℕ) (he : ∀ j, j < d → K.ExactAt j) :
    IsIso (AlgebraicTopology.Cohomology.Singular.SheafSections.sheafCohomologySectionMap K U d) := by
  have hKA : ∀ j, TopCat.Sheaf.IsFlasque ((AlgebraicTopology.DeRham.Comparison.RationalSheafForget.rationalSheafForgetComplex K).X j) := by
    intro j
    have := hK j
    exact inferInstanceAs (TopCat.Sheaf.IsFlasque ((AlgebraicTopology.DeRham.Comparison.RationalSheafForget.rationalSheafForget X).obj (K.X j)))
  have heA : ∀ j, j < d → (AlgebraicTopology.DeRham.Comparison.RationalSheafForget.rationalSheafForgetComplex K).ExactAt j :=
    fun j hj => (AlgebraicTopology.DeRham.Comparison.RationalSheafForget.rationalSheafForgetComplex_exactAt_iff K j).mpr (he j hj)
  have : (AlgebraicTopology.DeRham.Comparison.RationalSheafForget.additiveSheafSections U).PreservesRightHomologyOf
      ((K.sc d).map (AlgebraicTopology.DeRham.Comparison.RationalSheafForget.rationalSheafForget X)) :=
    openSections_preservesRightHomologyOf U (AlgebraicTopology.DeRham.Comparison.RationalSheafForget.rationalSheafForgetComplex K) hKA d heA d le_rfl
  have hcomp : IsIso (AlgebraicTopology.Cohomology.Singular.LeftExactHomology.leftExactHomologyComparison (K.sc d)
      (AlgebraicTopology.DeRham.Comparison.RationalSheafForget.rationalSheafForget X ⋙ AlgebraicTopology.DeRham.Comparison.RationalSheafForget.additiveSheafSections U)) := by
    rw [← AlgebraicTopology.Cohomology.Singular.LeftExactHomologyComposition.leftExactHomologyComparison_comp,
      AlgebraicTopology.Cohomology.Singular.LeftExactHomologyIso.leftExactHomologyComparison_eq_mapHomologyIso',
      AlgebraicTopology.Cohomology.Singular.LeftExactHomologyIso.leftExactHomologyComparison_eq_mapHomologyIso']
    infer_instance
  have hsame : IsIso (AlgebraicTopology.Cohomology.Singular.LeftExactHomology.leftExactHomologyComparison (K.sc d)
      (AlgebraicTopology.DeRham.Comparison.RationalSheafForget.rationalSheafSections U ⋙ AlgebraicTopology.DeRham.Comparison.RationalSheafForget.rationalForget)) := hcomp
  rw [← AlgebraicTopology.Cohomology.Singular.LeftExactHomologyComposition.leftExactHomologyComparison_comp] at hsame
  have hfirst : IsIso (AlgebraicTopology.Cohomology.Singular.LeftExactHomology.leftExactHomologyComparison ((K.sc d).map (AlgebraicTopology.DeRham.Comparison.RationalSheafForget.rationalSheafSections U))
      AlgebraicTopology.DeRham.Comparison.RationalSheafForget.rationalForget) := by
    rw [AlgebraicTopology.Cohomology.Singular.LeftExactHomologyIso.leftExactHomologyComparison_eq_mapHomologyIso']
    infer_instance
  have : IsIso (AlgebraicTopology.DeRham.Comparison.RationalSheafForget.rationalForget.map (AlgebraicTopology.Cohomology.Singular.LeftExactHomology.leftExactHomologyComparison (K.sc d) (AlgebraicTopology.DeRham.Comparison.RationalSheafForget.rationalSheafSections U))) :=
    IsIso.of_isIso_comp_left
      (AlgebraicTopology.Cohomology.Singular.LeftExactHomology.leftExactHomologyComparison ((K.sc d).map (AlgebraicTopology.DeRham.Comparison.RationalSheafForget.rationalSheafSections U)) AlgebraicTopology.DeRham.Comparison.RationalSheafForget.rationalForget)
      (AlgebraicTopology.DeRham.Comparison.RationalSheafForget.rationalForget.map (AlgebraicTopology.Cohomology.Singular.LeftExactHomology.leftExactHomologyComparison (K.sc d) (AlgebraicTopology.DeRham.Comparison.RationalSheafForget.rationalSheafSections U)))
  rw [CycleClass.Geometric.FlasqueSectionComparison.Cycles.sheafCohomologySectionMap_eq_leftExactHomologyComparison]
  exact isIso_of_reflects_iso _ AlgebraicTopology.DeRham.Comparison.RationalSheafForget.rationalForget

end

end OAI.AlgebraicGeometry.DivisorClass.Chern.Open.FlasqueComparison
