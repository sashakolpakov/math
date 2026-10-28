import OAI.AlgebraicGeometry.Comparison.Betti.BrutalMappedIsomorphism
import OAI.AlgebraicGeometry.Comparison.Betti.Complex.Extension

/-! # Brutal Mapped Extension -/

namespace OAI.AlgebraicGeometry.Comparison.Betti.BrutalMappedExtension.Hodge

noncomputable section

/-! Integer extension preserves the canonical truncated coefficient map and its inclusion square. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits

open OAI.AlgebraicGeometry.Crystalline.Cohomology.HodgeFiltrationD.HodgeFiltration OAI.AlgebraicGeometry.Crystalline.Cohomology.HodgeTruncationTerm.HodgeTruncationFactor

variable {C D : Type*} [Category* C] [Category* D]
  [Preadditive C] [HasZeroObject C] [Preadditive D] [HasZeroObject D]
  (F : C ⥤ D) [F.Additive] (K : CochainComplex C ℕ) {L : CochainComplex D ℕ}
  (f : (F.mapHomologicalComplex (.up ℕ)).obj K ⟶ L) (r : ℤ)

def brutalMappedExtension :
    ((F.mapHomologicalComplex (.up ℤ)).obj ((Crystalline.Cohomology.HodgeFiltrationD.HodgeFiltration.brutal K r).extend (ComplexShape.embeddingUpIntGE 0))) ⟶
      (Crystalline.Cohomology.HodgeFiltrationD.HodgeFiltration.brutal L r).extend (ComplexShape.embeddingUpIntGE 0) :=
  (Complex.Extension.mapExtendIso F (ComplexShape.embeddingUpIntGE 0) (Crystalline.Cohomology.HodgeFiltrationD.HodgeFiltration.brutal K r)).hom ≫
    HomologicalComplex.extendMap (Crystalline.Cohomology.HodgeTruncationTerm.HodgeTruncationFactor.mappedFactor r F K f) (ComplexShape.embeddingUpIntGE 0)

theorem brutalMappedExtension_inclusion :
    brutalMappedExtension F K f r ≫
      HomologicalComplex.extendMap (Crystalline.Cohomology.HodgeFiltrationD.HodgeFiltration.inclusion L r) (ComplexShape.embeddingUpIntGE 0) =
    ((F.mapHomologicalComplex (.up ℤ)).map
      (HomologicalComplex.extendMap (Crystalline.Cohomology.HodgeFiltrationD.HodgeFiltration.inclusion K r) (ComplexShape.embeddingUpIntGE 0))) ≫
      (Complex.Extension.mapExtendIso F (ComplexShape.embeddingUpIntGE 0) K).hom ≫
        HomologicalComplex.extendMap f (ComplexShape.embeddingUpIntGE 0) := by
  let e := ComplexShape.embeddingUpIntGE 0
  change (_ ≫ HomologicalComplex.extendMap (Crystalline.Cohomology.HodgeTruncationTerm.HodgeTruncationFactor.mappedFactor r F K f) e) ≫
    HomologicalComplex.extendMap (Crystalline.Cohomology.HodgeFiltrationD.HodgeFiltration.inclusion L r) e = _
  rw [Category.assoc, ← HomologicalComplex.extendMap_comp, Crystalline.Cohomology.HodgeTruncationTerm.HodgeTruncationFactor.mappedFactor_inclusion,
    HomologicalComplex.extendMap_comp, ← Category.assoc,
    ← Complex.Extension.mapExtendIso_naturality]
  exact Category.assoc _ _ _

theorem brutalMappedExtension_isIso [hf : IsIso f] : IsIso (brutalMappedExtension F K f r) := by
  have h : IsIso (Crystalline.Cohomology.HodgeTruncationTerm.HodgeTruncationFactor.mappedFactor r F K f) := BrutalMappedIsomorphism.Hodge.brutalMappedFactor_isIso F K f r
  exact ((Complex.Extension.mapExtendIso F (ComplexShape.embeddingUpIntGE 0) (Crystalline.Cohomology.HodgeFiltrationD.HodgeFiltration.brutal K r)) ≪≫
    ((ComplexShape.embeddingUpIntGE 0).extendFunctor D).mapIso
      (@asIso _ _ _ _ (Crystalline.Cohomology.HodgeTruncationTerm.HodgeTruncationFactor.mappedFactor r F K f) h)).isIso_hom

end

end OAI.AlgebraicGeometry.Comparison.Betti.BrutalMappedExtension.Hodge
