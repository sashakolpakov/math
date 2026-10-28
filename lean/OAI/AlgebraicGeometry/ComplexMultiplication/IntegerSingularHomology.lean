import OAI.AlgebraicGeometry.ComplexMultiplication.ScalarExtendHomologyCoherence
import OAI.AlgebraicGeometry.ComplexMultiplication.CanonicalSheafComparison
import OAI.AlgebraicTopology.Singular.SheafCochainOpenCone

/-! # Integer Singular Homology -/

namespace OAI.AlgebraicGeometry.ComplexMultiplication.IntegerSingularHomology

noncomputable section

/-! # The raw integer comparison computes the actual ordinary singular class -/

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open _root_.CategoryTheory _root_.HomologicalComplex OAI.AlgebraicTopology.Singular

variable (R : Type) [Field R] (Y : TopCat.{0}) (n : ℕ)
local notation "F" => forget₂ (ModuleCat R) AddCommGrpCat
local notation "K" => OAI.AlgebraicTopology.Singular.CohomologyTo.SingularCochainComplex R (TopCat.of (⊤ : TopologicalSpace.Opens Y))
local notation "FNK" => Functor.obj (Functor.mapHomologicalComplex (F) (ComplexShape.up ℕ)) (K)

theorem openRawGlobalIsoDual_eq :
    AlgebraicTopology.Singular.SheafCochainOpenCone.openRawSingularCochainComplexIsoDual R Y ⊤ = AlgebraicTopology.Singular.SheafSubdivisionCochain.globalRawSingularCochainComplexIso R Y := by
  apply Iso.ext
  apply HomologicalComplex.hom_ext
  intro i
  apply AddCommGrpCat.hom_ext
  ext a
  rfl

theorem rawIntegerSingularHomology_normalization
    (b : (((F).mapHomologicalComplex (ComplexShape.up ℤ)).obj
      ((K).extend ComplexShape.embeddingUpNat)).homology (n : ℤ)) :
    (Coefficient.SheafComparison.rawSingularHomologyIso R Y n).hom
      (((AlgebraicTopology.Singular.SheafSubdivisionCochain.globalRawSingularCochainComplex R Y).extendHomologyIso
        ComplexShape.embeddingUpNat rfl).hom
        (HomologicalComplex.homologyMap (AlgebraicTopology.Singular.SheafCochainOpenCone.openRawSingularCochainComplexIntIsoDual R Y ⊤).inv (n : ℤ) b)) =
    HomologicalComplex.homologyMap (AlgebraicTopology.Singular.SheafSubdivisionCochain.singularCochainComplexIsoTopOpen R Y).inv n
      (((K).extendHomologyIso ComplexShape.embeddingUpNat rfl).hom
        (((((K).extend ComplexShape.embeddingUpNat).sc (n : ℤ)).mapHomologyIso (F)).hom b)) := by
  let m := Algebra.Homology.MapExtend.HomologicalComplex.mapExtendCanonicalIso (F) (K) ComplexShape.embeddingUpNat
  let b' := HomologicalComplex.homologyMap m.hom (n : ℤ) b
  dsimp only [AlgebraicTopology.Singular.SheafCochainOpenCone.openRawSingularCochainComplexIntIsoDual, Iso.trans_inv,
    Iso.symm_inv, CategoryTheory.Functor.mapIso_inv]
  rw [openRawGlobalIsoDual_eq]
  simp only [HomologicalComplex.homologyMap_comp, AddCommGrpCat.comp_apply]
  change (Coefficient.SheafComparison.rawSingularHomologyIso R Y n).hom
    (((AlgebraicTopology.Singular.SheafSubdivisionCochain.globalRawSingularCochainComplex R Y).extendHomologyIso
      ComplexShape.embeddingUpNat rfl).hom
      (HomologicalComplex.homologyMap (extendMap (AlgebraicTopology.Singular.SheafSubdivisionCochain.globalRawSingularCochainComplexIso R Y).inv
        ComplexShape.embeddingUpNat) (n : ℤ) b')) = _
  rw [show ((AlgebraicTopology.Singular.SheafSubdivisionCochain.globalRawSingularCochainComplex R Y).extendHomologyIso
      ComplexShape.embeddingUpNat rfl).hom
      (HomologicalComplex.homologyMap (extendMap (AlgebraicTopology.Singular.SheafSubdivisionCochain.globalRawSingularCochainComplexIso R Y).inv
        ComplexShape.embeddingUpNat) (n : ℤ) b') =
      HomologicalComplex.homologyMap (AlgebraicTopology.Singular.SheafSubdivisionCochain.globalRawSingularCochainComplexIso R Y).inv n
        (((FNK).extendHomologyIso ComplexShape.embeddingUpNat rfl).hom b') from
    ConcreteCategory.congr_hom
      (extendHomologyIso_hom_naturality (AlgebraicTopology.Singular.SheafSubdivisionCochain.globalRawSingularCochainComplexIso R Y).inv
        ComplexShape.embeddingUpNat (j := n) (j' := (n : ℤ)) rfl) b']
  dsimp only [Coefficient.SheafComparison.rawSingularHomologyIso, Iso.trans_hom, homologyMapIso_hom,
    CategoryTheory.Functor.mapIso_hom, Iso.symm_hom]
  simp only [HomologicalComplex.homologyMap_comp, AddCommGrpCat.comp_apply]
  have he : HomologicalComplex.homologyMap (AlgebraicTopology.Singular.SheafSubdivisionCochain.globalRawSingularCochainComplexIso R Y).hom n
      (HomologicalComplex.homologyMap (AlgebraicTopology.Singular.SheafSubdivisionCochain.globalRawSingularCochainComplexIso R Y).inv n
        (((FNK).extendHomologyIso ComplexShape.embeddingUpNat rfl).hom b')) =
      ((FNK).extendHomologyIso ComplexShape.embeddingUpNat rfl).hom b' :=
    ConcreteCategory.congr_hom
      (homologyMapIso (AlgebraicTopology.Singular.SheafSubdivisionCochain.globalRawSingularCochainComplexIso R Y) n).inv_hom_id _
  rw [he]
  have hn := SingularDualMap.forgottenModuleComplex_homology_naturality R
    (AlgebraicTopology.Singular.SheafSubdivisionCochain.singularCochainComplexIsoTopOpen R Y).inv n
  have hc := ConcreteCategory.congr_hom (ScalarExtendHomologyCoherence.scalarExtendHomologyCoherence (F) (K) n) b
  exact (ConcreteCategory.congr_hom hn _).trans
    (congrArg (fun a => HomologicalComplex.homologyMap (AlgebraicTopology.Singular.SheafSubdivisionCochain.singularCochainComplexIsoTopOpen R Y).inv n a) hc)

end

end OAI.AlgebraicGeometry.ComplexMultiplication.IntegerSingularHomology
