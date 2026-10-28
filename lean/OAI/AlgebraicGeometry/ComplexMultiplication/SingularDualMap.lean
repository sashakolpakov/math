import OAI.AlgebraicGeometry.ComplexMultiplication.SingularScalars
import OAI.AlgebraicGeometry.ComplexMultiplication.Coefficient.SheafComparison

/-! # Singular Dual Map -/

namespace OAI.AlgebraicGeometry.ComplexMultiplication.SingularDualMap

noncomputable section

/-! # The raw singular comparison respects the actual coefficient action -/

open _root_.CategoryTheory Limits OAI.AlgebraicTopology.Singular

variable (R : Type) [Field R] (Y : TopCat.{0}) (q : R)

/-- The original raw global cochain complex and the ordinary linear dual complex. -/
def rawSingularCochainIso :
    AlgebraicTopology.Singular.SheafSubdivisionCochain.globalRawSingularCochainComplex R Y ≅
      ((forget₂ (ModuleCat R) AddCommGrpCat).mapHomologicalComplex (ComplexShape.up ℕ)).obj
        (AlgebraicTopology.Singular.CohomologyTo.SingularCochainComplex R Y) :=
  AlgebraicTopology.Singular.SheafSubdivisionCochain.globalRawSingularCochainComplexIso R Y ≪≫
    ((forget₂ (ModuleCat R) AddCommGrpCat).mapHomologicalComplex (ComplexShape.up ℕ)).mapIso
      (AlgebraicTopology.Singular.SheafSubdivisionCochain.singularCochainComplexIsoTopOpen R Y).symm

set_option backward.isDefEq.respectTransparency false in
/-- The scalar cochain map is the ordinary scalar map under the original cochain comparison. -/
lemma rawGlobalSingularScalar_cochainIso :
    SingularScalars.rawGlobalSingularScalar R Y q ≫ (rawSingularCochainIso R Y).hom =
      (rawSingularCochainIso R Y).hom ≫
        ((forget₂ (ModuleCat R) AddCommGrpCat).mapHomologicalComplex (ComplexShape.up ℕ)).map
          (q • 𝟙 (AlgebraicTopology.Singular.CohomologyTo.SingularCochainComplex R Y)) := by
  apply HomologicalComplex.hom_ext
  intro n
  apply AddCommGrpCat.hom_ext
  ext φ
  change AlgebraicTopology.Singular.SheafCochain.OpenCochains R Y (.op ⊤) n at φ
  change ((AlgebraicTopology.Singular.SheafSubdivisionCochain.singularCochainComplexIsoTopOpen R Y).inv.f n).hom (q • φ) =
    q • ((AlgebraicTopology.Singular.SheafSubdivisionCochain.singularCochainComplexIsoTopOpen R Y).inv.f n).hom φ
  exact map_smul _ q φ

/-- Forgetting coefficients commutes with the actual homology maps. -/
lemma forgottenModuleComplex_homology_naturality
    {K L : CochainComplex (ModuleCat R) ℕ} (f : K ⟶ L) (n : ℕ) :
    HomologicalComplex.homologyMap
        (((forget₂ (ModuleCat R) AddCommGrpCat).mapHomologicalComplex (ComplexShape.up ℕ)).map f)
        n ≫ ((L.sc n).mapHomologyIso (forget₂ (ModuleCat R) AddCommGrpCat)).hom =
      ((K.sc n).mapHomologyIso (forget₂ (ModuleCat R) AddCommGrpCat)).hom ≫
        (forget₂ (ModuleCat R) AddCommGrpCat).map (HomologicalComplex.homologyMap f n) :=
  ShortComplex.mapHomologyIso_hom_naturality
    ((HomologicalComplex.shortComplexFunctor (ModuleCat R) (ComplexShape.up ℕ) n).map f)
    (forget₂ (ModuleCat R) AddCommGrpCat)

set_option backward.isDefEq.respectTransparency false in
/-- The raw-to-ordinary comparison carries the original raw scalar action to scalar
multiplication on ordinary singular cohomology. -/
lemma rawSingularHomologyIso_scalar (n : ℕ)
    (z : (AlgebraicTopology.Singular.SheafSubdivisionCochain.globalRawSingularCochainComplex R Y).homology n) :
    (Coefficient.SheafComparison.rawSingularHomologyIso R Y n).hom
        (HomologicalComplex.homologyMap (SingularScalars.rawGlobalSingularScalar R Y q) n z) =
      q • (show AlgebraicTopology.Singular.CohomologyTo.Cohomology R Y n from (Coefficient.SheafComparison.rawSingularHomologyIso R Y n).hom z) := by
  have h : HomologicalComplex.homologyMap (SingularScalars.rawGlobalSingularScalar R Y q) n ≫
      (Coefficient.SheafComparison.rawSingularHomologyIso R Y n).hom =
    (Coefficient.SheafComparison.rawSingularHomologyIso R Y n).hom ≫
      (forget₂ (ModuleCat R) AddCommGrpCat).map
        (q • 𝟙 (AlgebraicTopology.Singular.CohomologyTo.Cohomology R Y n)) := by
    change HomologicalComplex.homologyMap (SingularScalars.rawGlobalSingularScalar R Y q) n ≫
        HomologicalComplex.homologyMap (rawSingularCochainIso R Y).hom n ≫ _ =
      (HomologicalComplex.homologyMap (rawSingularCochainIso R Y).hom n ≫ _) ≫ _
    rw [← Category.assoc, ← HomologicalComplex.homologyMap_comp,
      rawGlobalSingularScalar_cochainIso, HomologicalComplex.homologyMap_comp,
      Category.assoc, forgottenModuleComplex_homology_naturality,
      SingularScalars.moduleComplex_homologyMap_smul, HomologicalComplex.homologyMap_id]
    exact (Category.assoc _ _ _).symm
  exact congrArg (fun f => f z) h

end

end OAI.AlgebraicGeometry.ComplexMultiplication.SingularDualMap
