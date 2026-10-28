import OAI.AlgebraicGeometry.PELModuli.IntegralModel.LieRankCharacter

/-! # Scheme Character Lie Predicate -/

namespace OAI.AlgebraicGeometry.PELModuli.IntegralModel.SchemeCharacterLiePredicate

noncomputable section

/-! The actual geometric character Lie condition as a scheme-point
subfunctor, including its geometric-test detection property. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

variable {S : Scheme.{0}} {g : ℕ} {R : Type} [CommRing R]
  (A : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme g S) (ρ : AbelianModuli.ReferenceFamily.ActionData.IntegralAction R A)
  (χ : R →+* Γ(S, ⊤)) (r : ℕ)

def HasCharacterLieRankOnSchemeMap {T : Scheme.{0}} (x : T ⟶ S) : Prop :=
  ∀ (k : Type) [Field k] [IsAlgClosed k] (p : Spec (.of k) ⟶ T),
    LieRankCharacter.CharacterLieRank A ρ χ r (p ≫ x)

theorem hasCharacterLieRankOnSchemeMap_comp {T U : Scheme.{0}} (x : T ⟶ S)
    (h : HasCharacterLieRankOnSchemeMap A ρ χ r x) (f : U ⟶ T) :
    HasCharacterLieRankOnSchemeMap A ρ χ r (f ≫ x) := by
  intro k hk ha p
  exact (LieRankCharacter.characterLieRank_congr A ρ χ r (Category.assoc p f x)).mp (h k (p ≫ f))

def schemeCharacterLieRankSubfunctor : Subfunctor (yoneda.obj S) where
  obj _T := {x | HasCharacterLieRankOnSchemeMap A ρ χ r x}
  map f x hx := hasCharacterLieRankOnSchemeMap_comp A ρ χ r x hx f.unop

theorem schemeCharacterLieRank_geometric_detection (T : Scheme.{0}) (x : T ⟶ S)
    (h : ∀ (k : Type) [Field k] [IsAlgClosed k] (p : Spec (.of k) ⟶ T),
      p ≫ x ∈ (schemeCharacterLieRankSubfunctor A ρ χ r).obj (.op (Spec (.of k)))) :
    x ∈ (schemeCharacterLieRankSubfunctor A ρ χ r).obj (.op T) := by
  intro k hk ha p
  exact (LieRankCharacter.characterLieRank_congr A ρ χ r (Category.id_comp (p ≫ x))).mp
    (h k p k (𝟙 (Spec (.of k))))

end

end OAI.AlgebraicGeometry.PELModuli.IntegralModel.SchemeCharacterLiePredicate
