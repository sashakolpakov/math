import OAI.AlgebraicGeometry.Crystalline.Cohomology.HodgeTruncationTerm
import OAI.AlgebraicGeometry.Comparison.Betti.BrutalComplexMap

/-! # Brutal Mapped Isomorphism -/

namespace OAI.AlgebraicGeometry.Comparison.Betti.BrutalMappedIsomorphism.Hodge

noncomputable section

/-! The canonical map from a functorial degree truncation is invertible whenever the original coefficient map is invertible. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits

open OAI.AlgebraicGeometry.Crystalline.Cohomology.HodgeFiltrationD.HodgeFiltration OAI.AlgebraicGeometry.Crystalline.Cohomology.HodgeTruncationTerm.HodgeTruncationFactor

variable {C D : Type*} [Category* C] [Category* D]
  [HasZeroMorphisms C] [HasZeroObject C] [HasZeroMorphisms D] [HasZeroObject D]
  (F : C ⥤ D) [F.PreservesZeroMorphisms]
  (K : CochainComplex C ℕ) {L : CochainComplex D ℕ}
  (f : (F.mapHomologicalComplex (.up ℕ)).obj K ⟶ L) [hf : IsIso f] (r : ℤ)

include hf in
theorem brutalMappedFactor_isIso : IsIso (Crystalline.Cohomology.HodgeTruncationTerm.HodgeTruncationFactor.mappedFactor r F K f) := by
  have (n : ℕ) : IsIso ((Crystalline.Cohomology.HodgeTruncationTerm.HodgeTruncationFactor.mappedFactor r F K f).f n) := by
    by_cases h : r ≤ (n : ℤ)
    · have hi : IsIso (Crystalline.Cohomology.HodgeFiltrationD.HodgeFiltration.inclusionTerm K r n) :=
        (BrutalComplexMap.Hodge.brutalRetainedTermIso_inclusion K r n h) ▸ inferInstance
      change IsIso (Crystalline.Cohomology.HodgeTruncationTerm.HodgeTruncationFactor.term _ r n)
      rw [Crystalline.Cohomology.HodgeTruncationTerm.HodgeTruncationFactor.term, dite_eq_left h]
      change IsIso ((F.map (Crystalline.Cohomology.HodgeFiltrationD.HodgeFiltration.inclusionTerm K r n) ≫ f.f n) ≫ _)
      exact ((F.mapIso (@asIso _ _ _ _ (Crystalline.Cohomology.HodgeFiltrationD.HodgeFiltration.inclusionTerm K r n) hi) ≪≫
        (HomologicalComplex.eval D (.up ℕ) n).mapIso (@asIso _ _ _ _ f hf)) ≪≫
          eqToIso (by simp only [Crystalline.Cohomology.HodgeFiltrationD.HodgeFiltration.term, ite_eq_left h]; rfl)).isIso_hom
    · have hK := Crystalline.Cohomology.HodgeTruncationTerm.HodgeTruncationFactor.mapped_zero_below r F K n h
      have hL := BrutalComplexMap.Hodge.brutalTerm_isZero L r n h
      let e : ((F.mapHomologicalComplex (.up ℕ)).obj (Crystalline.Cohomology.HodgeFiltrationD.HodgeFiltration.brutal K r)).X n ≅ (Crystalline.Cohomology.HodgeFiltrationD.HodgeFiltration.brutal L r).X n :=
        { hom := (Crystalline.Cohomology.HodgeTruncationTerm.HodgeTruncationFactor.mappedFactor r F K f).f n
          inv := 0
          hom_inv_id := hK.eq_of_src _ _
          inv_hom_id := hL.eq_of_src _ _ }
      exact e.isIso_hom
  exact HomologicalComplex.Hom.isIso_of_components _

end

end OAI.AlgebraicGeometry.Comparison.Betti.BrutalMappedIsomorphism.Hodge
