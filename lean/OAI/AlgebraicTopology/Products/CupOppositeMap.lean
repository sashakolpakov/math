import OAI.AlgebraicTopology.Products.CupCohomologyAlgebra
import OAI.AlgebraicTopology.Cohomology.Singular.RepresentativesNaturality

/-! # Cup Opposite Map -/

namespace OAI.AlgebraicTopology.Products.CupOppositeMap

/-!
A concrete reversal identity for a cochain map descends to the actual cup
product on cohomology. This lemma only performs descent through representatives;
the signed singular reversal and its identity action are supplied separately.
-/

open _root_.CategoryTheory
open OAI.AlgebraicTopology.Cohomology.Singular.RepresentativesNaturality

variable {R : Type} [CommRing R]

/-- A signed opposite-cup identity for actual cochains descends to cohomology. -/
theorem cohomologyCup_opposite_of_cochain (K : SSet.{0})
    (f : Cohomology.Singular.Basic.simplicialCochains K (ModuleCat.of R R) ⟶
      Cohomology.Singular.Basic.simplicialCochains K (ModuleCat.of R R)) (p q : ℕ) (c : R)
    (hcup : ∀ (a : (Cohomology.Singular.Basic.simplicialCochains K (ModuleCat.of R R)).X p)
      (b : (Cohomology.Singular.Basic.simplicialCochains K (ModuleCat.of R R)).X q),
      f.f (p + q) (Cup.cup K a b) =
        c • Cup.cochainCast K (ModuleCat.of R R) (Nat.add_comm q p)
          (Cup.cup K (f.f q b) (f.f p a)))
    (a : (Cohomology.Singular.Basic.simplicialCochains K (ModuleCat.of R R)).homology p)
    (b : (Cohomology.Singular.Basic.simplicialCochains K (ModuleCat.of R R)).homology q) :
    HomologicalComplex.homologyMap f (p + q) (CupCohomology.cohomologyCup K p q a b) =
      c • CupCohomologyAlgebra.cohomologyCast K (ModuleCat.of R R) (Nat.add_comm q p)
        (CupCohomology.cohomologyCup K q p (HomologicalComplex.homologyMap f q b)
          (HomologicalComplex.homologyMap f p a)) := by
  obtain ⟨a, rfl⟩ := Cohomology.Singular.Representatives.cochainClass_surjective (Cohomology.Singular.Basic.simplicialCochains K (ModuleCat.of R R)) p a
  obtain ⟨b, rfl⟩ := Cohomology.Singular.Representatives.cochainClass_surjective (Cohomology.Singular.Basic.simplicialCochains K (ModuleCat.of R R)) q b
  simp only [CupCohomology.cohomologyCupWith_class_class, Cohomology.Singular.RepresentativesNaturality.cochainClass_naturality, CupCohomologyAlgebra.cohomologyCast_class]
  rw [← map_smul]
  apply congrArg (Cohomology.Singular.Representatives.cochainClass (Cohomology.Singular.Basic.simplicialCochains K (ModuleCat.of R R)) (p + q))
  apply Subtype.ext
  simpa only [Cohomology.Singular.RepresentativesNaturality.cochainCocycleMap_val, CupCohomology.cocycleCupWith_val, Submodule.coe_smul,
    CupCohomologyAlgebra.cocycleCast_val, Cup.cup] using hcup a.val b.val

end OAI.AlgebraicTopology.Products.CupOppositeMap
