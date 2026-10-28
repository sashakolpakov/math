import OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.GodementEmbedding
import OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.FlasqueSectionCokernels

/-! # Flasque Injectives -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.FlasqueInjectives.Constructions

noncomputable section

/-! Injective module sheaves are flasque; exact flasque complexes remain exact on actual open sections. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.TopologicalSpace Opposite

set_option backward.isDefEq.respectTransparency false

variable {R : Type} [Ring R] {X : TopCat.{0}}

theorem moduleSheafFlasque_of_retract
    {F G : TopCat.Sheaf (ModuleCat.{0} R) X} (i : F ⟶ G) (r : G ⟶ F)
    (hir : i ≫ r = 𝟙 F) [TopCat.Sheaf.IsFlasque G] : TopCat.Sheaf.IsFlasque F where
  epi {U W} j := by
    have hW : i.hom.app W ≫ r.hom.app W = 𝟙 _ :=
      congrArg (fun f => f.hom.app W) hir
    have : Epi (r.hom.app W) := (show SplitEpi (r.hom.app W) from
      { section_ := i.hom.app W, id := hW }).epi
    have : Epi (r.hom.app U ≫ F.obj.map j) := by
      rw [← r.hom.naturality]
      infer_instance
    exact epi_of_epi (r.hom.app U) (F.obj.map j)

theorem injectiveModuleSheaf_isFlasque (F : TopCat.Sheaf (ModuleCat.{0} R) X) [Injective F] :
    TopCat.Sheaf.IsFlasque F := by
  have := GodementEmbedding.Constructions.stalkFamilyEmbedding_mono F
  have := GodementEmbedding.Constructions.stalkFamilySheaf_isFlasque F
  exact moduleSheafFlasque_of_retract (GodementEmbedding.Constructions.stalkFamilyEmbedding F)
    (Injective.factorThru (𝟙 F) (GodementEmbedding.Constructions.stalkFamilyEmbedding F))
    (Injective.comp_factorThru (𝟙 F) (GodementEmbedding.Constructions.stalkFamilyEmbedding F))

theorem rationalFlasqueSections_acyclic
    (K : CochainComplex (TopCat.Sheaf (ModuleCat.{0} ℚ) X) ℕ)
    (hK : ∀ n, TopCat.Sheaf.IsFlasque (K.X n)) (he : K.Acyclic) (U : Opens X) :
    (CycleClass.Geometric.SupportStalkVanishes.Cohomology.moduleSheafSectionsComplex U K).Acyclic := by
  intro n
  have := FlasqueSectionCokernels.Constructions.rationalFlasqueSections_preservesRightHomologyOf K hK n (fun i _ => he i) U n le_rfl
  apply (HomologicalComplex.exactAt_iff_isZero_homology _ _).mpr
  exact ((CycleClass.Geometric.SheafClosedSupport.Cohomology.moduleSheafSections U).map_isZero (he n).isZero_homology).of_iso
    ((K.sc n).mapHomologyIso' (CycleClass.Geometric.SheafClosedSupport.Cohomology.moduleSheafSections U))

end

end OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.FlasqueInjectives.Constructions
