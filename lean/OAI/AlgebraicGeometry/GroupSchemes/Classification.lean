import OAI.AlgebraicGeometry.GroupSchemes.EtaleClassification
import OAI.AlgebraicGeometry.GroupSchemes.MultiplicativeClassification

/-! # Classification -/

namespace OAI.AlgebraicGeometry.GroupSchemes.Classification.FiniteEtale

/-!
# FiniteEtale: unconditional geometric height-one classification

The actual finite group schemes and closed transition maps determine which
branch occurs. Both alternatives are natural on every affine algebra and
commute with the original tower inclusions. No Dieudonné comparison or
classification hypothesis is used.
-/

universe u

/-- Every height-one p-divisible tower over an algebraically closed field of
characteristic p is the étale or multiplicative standard tower. -/
theorem height_one_classification
    (k : Type u) [Field k] [IsAlgClosed k]
    (p : ℕ) [Fact p.Prime] [CharP k p]
    (G : FiniteEtale.PDivisibleGroup k p 1) :
    Nonempty (FiniteEtale.GroupTower.Iso k (G.points k) (FiniteEtale.etaleTower k p)) ∨
      Nonempty (FiniteEtale.GroupTower.Iso k (G.points k) (FiniteEtale.multiplicativeTower k p)) := by
  rcases G.first_local_or_split with hlocal | hsplit
  · exact Or.inr (G.multiplicative_classification_of_first_local hlocal)
  · exact Or.inl (G.etale_classification_of_first_split hsplit)

end OAI.AlgebraicGeometry.GroupSchemes.Classification.FiniteEtale
