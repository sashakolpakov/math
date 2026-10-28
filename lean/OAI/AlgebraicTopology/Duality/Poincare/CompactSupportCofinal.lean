import OAI.AlgebraicTopology.Duality.Poincare.CompactExhaustionCofinal
import OAI.AlgebraicTopology.Duality.Poincare.CompactSupportColimit

/-! # Compact Support Cofinal -/

namespace OAI.AlgebraicTopology.Duality.Poincare.CompactSupportCofinal

noncomputable section

/-!
# Computing compact support along a cofinal family

The actual relative cochain complexes and their cohomology may be indexed by
any final functor into the compact subsets. The comparison is the canonical
colimit comparison, and its formulas identify the maps from every relative
stage. In particular this applies to each genuine `CompactExhaustion`, whose
finality is proved from its defining geometric properties.
-/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.TopologicalSpace

set_option backward.isDefEq.respectTransparency false

variable {R : Type} [Ring R]

section Cofinal

variable (M : ModuleCat.{0} R) (X : TopCat.{0})
  {J : Type} [SmallCategory J] (F : J ⥤ Compacts X) [F.Final]

/-- The canonical comparison of actual support-cochain colimits along a cofinal family. -/
def compactSupportCochainCofinalIso :
    colimit (F ⋙ CompactSupportCohomology.compactSupportCochainDiagram M X) ≅ CompactSupportCohomology.compactSupportedCochains M X :=
  Functor.Final.colimitIso F (CompactSupportCohomology.compactSupportCochainDiagram M X)

@[reassoc (attr := simp)]
theorem compactSupportCochainCofinalIso_ι (j : J) :
    colimit.ι (F ⋙ CompactSupportCohomology.compactSupportCochainDiagram M X) j ≫
        (compactSupportCochainCofinalIso M X F).hom =
      CompactSupportCohomology.compactSupportCochainι M X (F.obj j) :=
  Functor.Final.ι_colimitIso_hom F (CompactSupportCohomology.compactSupportCochainDiagram M X) j

@[reassoc (attr := simp)]
theorem compactSupportCochainCofinalIso_inv_ι (j : J) :
    CompactSupportCohomology.compactSupportCochainι M X (F.obj j) ≫
        (compactSupportCochainCofinalIso M X F).inv =
      colimit.ι (F ⋙ CompactSupportCohomology.compactSupportCochainDiagram M X) j :=
  Functor.Final.ι_colimitIso_inv F (CompactSupportCohomology.compactSupportCochainDiagram M X) j

/-- The actual compact-support complex is a colimit of a cofinal family of stages. -/
def compactSupportCochainCofinalIsColimit :
    IsColimit ((colimit.cocone (CompactSupportCohomology.compactSupportCochainDiagram M X)).whisker F) :=
  (Functor.Final.isColimitWhiskerEquiv F _).symm
    (colimit.isColimit (CompactSupportCohomology.compactSupportCochainDiagram M X))

/-- Forget support from the cofinal presentation using the genuine stage inclusions. -/
def compactSupportCochainCofinalForget :
    colimit (F ⋙ CompactSupportCohomology.compactSupportCochainDiagram M X) ⟶ Cohomology.Singular.Basic.singularCochains M X :=
  colimit.desc (F ⋙ CompactSupportCohomology.compactSupportCochainDiagram M X)
    ((CompactSupportCohomology.compactSupportCochainCocone M X).whisker F)

omit [F.Final] in
@[reassoc (attr := simp)]
theorem compactSupportCochainCofinalForget_ι (j : J) :
    colimit.ι (F ⋙ CompactSupportCohomology.compactSupportCochainDiagram M X) j ≫
        compactSupportCochainCofinalForget M X F =
      CompactSupportCohomology.compactSupportCochainStageInclusion M X (F.obj j) :=
  colimit.ι_desc ((CompactSupportCohomology.compactSupportCochainCocone M X).whisker F) j

@[reassoc (attr := simp)]
theorem compactSupportCochainCofinalIso_forget :
    (compactSupportCochainCofinalIso M X F).hom ≫ CompactSupportCohomology.compactSupportedCochainForget M X =
      compactSupportCochainCofinalForget M X F := by
  apply colimit.hom_ext
  intro j
  simp

/-- Taking cohomology of the cofinal cochain presentation gives the actual `Hc`. -/
def compactSupportCofinalCohomologyIso (n : ℕ) :
    (colimit (F ⋙ CompactSupportCohomology.compactSupportCochainDiagram M X)).homology n ≅
      CompactSupportCohomology.compactSupportedCohomology M X n :=
  HomologicalComplex.homologyMapIso (compactSupportCochainCofinalIso M X F) n

@[reassoc (attr := simp)]
theorem compactSupportCofinalCohomologyIso_ι (n : ℕ) (j : J) :
    HomologicalComplex.homologyMap
        (colimit.ι (F ⋙ CompactSupportCohomology.compactSupportCochainDiagram M X) j) n ≫
        (compactSupportCofinalCohomologyIso M X F n).hom =
      CompactSupportCohomology.compactSupportCohomologyι M X (F.obj j) n := by
  change HomologicalComplex.homologyMap _ n ≫
    HomologicalComplex.homologyMap (compactSupportCochainCofinalIso M X F).hom n = _
  rw [← HomologicalComplex.homologyMap_comp, compactSupportCochainCofinalIso_ι]

@[reassoc (attr := simp)]
theorem compactSupportCofinalCohomologyIso_forget (n : ℕ) :
    (compactSupportCofinalCohomologyIso M X F n).hom ≫
        CompactSupportCohomology.compactSupportedCohomologyForget M X n =
      HomologicalComplex.homologyMap (compactSupportCochainCofinalForget M X F) n := by
  change HomologicalComplex.homologyMap (compactSupportCochainCofinalIso M X F).hom n ≫
    HomologicalComplex.homologyMap (CompactSupportCohomology.compactSupportedCochainForget M X) n = _
  rw [← HomologicalComplex.homologyMap_comp, compactSupportCochainCofinalIso_forget]

/-- The colimit of actual relative cohomology along a cofinal family is `Hc`. -/
def compactSupportCohomologyCofinalIso (n : ℕ) :
    colimit (F ⋙ CompactSupportCohomology.compactSupportCohomologyDiagram M X n) ≅
      CompactSupportCohomology.compactSupportedCohomology M X n :=
  Functor.Final.colimitIso F (CompactSupportCohomology.compactSupportCohomologyDiagram M X n) ≪≫
    CompactSupportColimit.compactSupportCohomologyColimitIso M X n

@[reassoc (attr := simp)]
theorem compactSupportCohomologyCofinalIso_ι (n : ℕ) (j : J) :
    colimit.ι (F ⋙ CompactSupportCohomology.compactSupportCohomologyDiagram M X n) j ≫
        (compactSupportCohomologyCofinalIso M X F n).hom =
      CompactSupportCohomology.compactSupportCohomologyι M X (F.obj j) n := by
  simp [compactSupportCohomologyCofinalIso]

@[reassoc (attr := simp)]
theorem compactSupportCohomologyCofinalIso_inv_ι (n : ℕ) (j : J) :
    CompactSupportCohomology.compactSupportCohomologyι M X (F.obj j) n ≫
        (compactSupportCohomologyCofinalIso M X F n).inv =
      colimit.ι (F ⋙ CompactSupportCohomology.compactSupportCohomologyDiagram M X n) j := by
  rw [← compactSupportCohomologyCofinalIso_ι M X F n j,
    Category.assoc, Iso.hom_inv_id, Category.comp_id]

/-- The actual stage maps into `Hc` satisfy the colimit property on a cofinal family. -/
def compactSupportCohomologyCofinalIsColimit (n : ℕ) :
    IsColimit ((CompactSupportColimit.compactSupportCohomologyCocone M X n).whisker F) :=
  (Functor.Final.isColimitWhiskerEquiv F _).symm
    (CompactSupportColimit.compactSupportCohomologyIsColimit M X n)

/-- The cochain comparison is compatible with a morphism between cofinal families. -/
@[reassoc]
theorem compactSupportCochainCofinalIso_naturality
    (G : J ⥤ Compacts X) [G.Final] (α : F ⟶ G) :
    colimMap (Functor.whiskerRight α (CompactSupportCohomology.compactSupportCochainDiagram M X)) ≫
        (compactSupportCochainCofinalIso M X G).hom =
      (compactSupportCochainCofinalIso M X F).hom := by
  apply colimit.hom_ext
  intro j
  simp [compactSupportCochainCofinalIso, Functor.Final.colimitIso]

/-- The cohomology comparison is compatible with a morphism between cofinal families. -/
@[reassoc]
theorem compactSupportCohomologyCofinalIso_naturality
    (G : J ⥤ Compacts X) [G.Final] (α : F ⟶ G) (n : ℕ) :
    colimMap (Functor.whiskerRight α (CompactSupportCohomology.compactSupportCohomologyDiagram M X n)) ≫
        (compactSupportCohomologyCofinalIso M X G n).hom =
      (compactSupportCohomologyCofinalIso M X F n).hom := by
  apply colimit.hom_ext
  intro j
  simp [compactSupportCohomologyCofinalIso]
  exact CompactSupportColimit.compactSupportCohomologyMap_ι M (leOfHom (α.app j)) n

end Cofinal

variable (M : ModuleCat.{0} R) (X : TopCat.{0}) (K : CompactExhaustion X)

/-- An actual compact exhaustion computes compactly supported cochains. -/
def compactSupportCochainExhaustionIso :
    colimit (CompactExhaustionCofinal.compactExhaustionFunctor K ⋙ CompactSupportCohomology.compactSupportCochainDiagram M X) ≅
      CompactSupportCohomology.compactSupportedCochains M X :=
  compactSupportCochainCofinalIso M X (CompactExhaustionCofinal.compactExhaustionFunctor K)

@[reassoc (attr := simp)]
theorem compactSupportCochainExhaustionIso_ι (j : ℕ) :
    colimit.ι (CompactExhaustionCofinal.compactExhaustionFunctor K ⋙ CompactSupportCohomology.compactSupportCochainDiagram M X) j ≫
        (compactSupportCochainExhaustionIso M X K).hom =
      CompactSupportCohomology.compactSupportCochainι M X (CompactExhaustionCofinal.compactExhaustionSupport K j) :=
  compactSupportCochainCofinalIso_ι M X (CompactExhaustionCofinal.compactExhaustionFunctor K) j

/-- Relative cohomology on an actual compact exhaustion computes `Hc`. -/
def compactSupportCohomologyExhaustionIso (n : ℕ) :
    colimit (CompactExhaustionCofinal.compactExhaustionFunctor K ⋙ CompactSupportCohomology.compactSupportCohomologyDiagram M X n) ≅
      CompactSupportCohomology.compactSupportedCohomology M X n :=
  compactSupportCohomologyCofinalIso M X (CompactExhaustionCofinal.compactExhaustionFunctor K) n

@[reassoc (attr := simp)]
theorem compactSupportCohomologyExhaustionIso_ι (n j : ℕ) :
    colimit.ι (CompactExhaustionCofinal.compactExhaustionFunctor K ⋙ CompactSupportCohomology.compactSupportCohomologyDiagram M X n) j ≫
        (compactSupportCohomologyExhaustionIso M X K n).hom =
      CompactSupportCohomology.compactSupportCohomologyι M X (CompactExhaustionCofinal.compactExhaustionSupport K j) n :=
  compactSupportCohomologyCofinalIso_ι M X (CompactExhaustionCofinal.compactExhaustionFunctor K) n j

end

end OAI.AlgebraicTopology.Duality.Poincare.CompactSupportCofinal
