import OAI.AlgebraicGeometry.Comparison.Betti.BrutalComplexMap
import OAI.AlgebraicGeometry.Comparison.Betti.Complex.MonoLift

/-! # Brutal Relative -/

namespace OAI.AlgebraicGeometry.Comparison.Betti.BrutalRelative.Hodge

noncomputable section

/-! A coefficient map across a mono-preserving additive functor restricts to the independent Hodge truncations. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits

open OAI.AlgebraicGeometry.Crystalline.Cohomology.HodgeFiltrationD.HodgeFiltration

variable {C D : Type*} [Category* C] [Category* D] [Preadditive C] [Preadditive D]
  [HasZeroObject C] [HasZeroObject D] (F : C ⥤ D) [F.Additive]
  {K : CochainComplex D ℕ} {L : CochainComplex C ℕ}
  (α : K ⟶ (F.mapHomologicalComplex (.up ℕ)).obj L) (r : ℤ)

def brutalRelativeTermMap (n : ℕ) : Crystalline.Cohomology.HodgeFiltrationD.HodgeFiltration.term K r n ⟶ F.obj (Crystalline.Cohomology.HodgeFiltrationD.HodgeFiltration.term L r n) :=
  if h : r ≤ (n : ℤ) then
    (BrutalComplexMap.Hodge.brutalRetainedTermIso K r n h).hom ≫ α.f n ≫ F.map (BrutalComplexMap.Hodge.brutalRetainedTermIso L r n h).inv
  else 0

theorem brutalRelativeTermMap_inclusion (n : ℕ) :
    brutalRelativeTermMap F α r n ≫ F.map (Crystalline.Cohomology.HodgeFiltrationD.HodgeFiltration.inclusionTerm L r n) = Crystalline.Cohomology.HodgeFiltrationD.HodgeFiltration.inclusionTerm K r n ≫ α.f n := by
  by_cases h : r ≤ (n : ℤ)
  · simp only [brutalRelativeTermMap, dite_eq_left h]
    rw [← BrutalComplexMap.Hodge.brutalRetainedTermIso_inclusion L r n h, ← BrutalComplexMap.Hodge.brutalRetainedTermIso_inclusion K r n h]
    erw [Category.assoc, Category.assoc, ← F.map_comp, Iso.inv_hom_id, F.map_id, Category.comp_id]
  · simp only [brutalRelativeTermMap, Crystalline.Cohomology.HodgeFiltrationD.HodgeFiltration.inclusionTerm, dite_eq_right h, zero_comp]

variable [F.PreservesMonomorphisms]

omit [Preadditive D] [HasZeroObject D] [F.Additive] in
theorem brutalMappedInclusion_mono (n : ℕ) : Mono (F.map (Crystalline.Cohomology.HodgeFiltrationD.HodgeFiltration.inclusionTerm L r n)) := by
  have := BrutalComplexMap.Hodge.brutalInclusionTerm_mono L r n
  exact F.map_mono _

def brutalRelativeComplexMap : Crystalline.Cohomology.HodgeFiltrationD.HodgeFiltration.brutal K r ⟶ (F.mapHomologicalComplex (.up ℕ)).obj (Crystalline.Cohomology.HodgeFiltrationD.HodgeFiltration.brutal L r) :=
  Complex.MonoLift.liftAlongMono (Crystalline.Cohomology.HodgeFiltrationD.HodgeFiltration.inclusion K r ≫ α)
    ((F.mapHomologicalComplex (.up ℕ)).map (Crystalline.Cohomology.HodgeFiltrationD.HodgeFiltration.inclusion L r))
    (brutalMappedInclusion_mono F (L := L) r) (brutalRelativeTermMap F α r)
    (brutalRelativeTermMap_inclusion F α r)

theorem brutalRelativeComplexMap_inclusion :
    brutalRelativeComplexMap F α r ≫ (F.mapHomologicalComplex (.up ℕ)).map (Crystalline.Cohomology.HodgeFiltrationD.HodgeFiltration.inclusion L r) =
      Crystalline.Cohomology.HodgeFiltrationD.HodgeFiltration.inclusion K r ≫ α :=
  Complex.MonoLift.liftAlongMono_factorization (Crystalline.Cohomology.HodgeFiltrationD.HodgeFiltration.inclusion K r ≫ α)
    ((F.mapHomologicalComplex (.up ℕ)).map (Crystalline.Cohomology.HodgeFiltrationD.HodgeFiltration.inclusion L r))
    (brutalMappedInclusion_mono F (L := L) r) (brutalRelativeTermMap F α r)
    (brutalRelativeTermMap_inclusion F α r)

end

end OAI.AlgebraicGeometry.Comparison.Betti.BrutalRelative.Hodge
