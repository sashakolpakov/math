import OAI.AlgebraicGeometry.PELModuli.IntegralModel.LieRanks
import OAI.AlgebraicGeometry.HilbertScheme.Presentations.PointCoefficients

/-! # Lie Rank Character -/

namespace OAI.AlgebraicGeometry.PELModuli.IntegralModel.LieRankCharacter

noncomputable section

/-! The original geometric Lie-rank condition for a specified
integral character is an actual subfunctor of the parameter scheme's points. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

variable {S : Scheme.{0}} {g : ℕ} {R : Type} [CommRing R]
  (A : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme g S) (ρ : AbelianModuli.ReferenceFamily.ActionData.IntegralAction R A)
  (χ : R →+* Γ(S, ⊤)) (r : ℕ)

def CharacterLieRank {k : Type} [Field k] (q : Spec (.of k) ⟶ S) : Prop :=
  AbelianModuli.ReferenceFamily.LieRanks.HasLieRank (A.pullback q) (ρ.pullback q) ((HilbertScheme.Presentations.PointCoefficients.schemePointCoefficientMap q).comp χ) r

theorem characterLieRank_congr {k : Type} [Field k] {p q : Spec (.of k) ⟶ S} (h : p = q) :
    CharacterLieRank A ρ χ r p ↔ CharacterLieRank A ρ χ r q := by
  cases h
  rfl

def HasCharacterLieRankOnMap {B : Scheme.{0}} {M T : Over B}
    (A : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme g M.left) (ρ : AbelianModuli.ReferenceFamily.ActionData.IntegralAction R A)
    (χ : R →+* Γ(M.left, ⊤)) (r : ℕ) (x : T ⟶ M) : Prop :=
  ∀ (k : Type) [Field k] [IsAlgClosed k] (p : Spec (.of k) ⟶ T.left),
    CharacterLieRank A ρ χ r (p ≫ x.left)

theorem hasCharacterLieRankOnMap_comp {B : Scheme.{0}} {M T U : Over B}
    (A : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme g M.left) (ρ : AbelianModuli.ReferenceFamily.ActionData.IntegralAction R A)
    (χ : R →+* Γ(M.left, ⊤)) (r : ℕ) (x : T ⟶ M)
    (h : HasCharacterLieRankOnMap A ρ χ r x) (f : U ⟶ T) :
    HasCharacterLieRankOnMap A ρ χ r (f ≫ x) := by
  intro k hk ha p
  exact (characterLieRank_congr A ρ χ r (Category.assoc p f.left x.left)).mp (h k (p ≫ f.left))

def characterLieRankSubfunctor {B : Scheme.{0}} (M : Over B)
    (A : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme g M.left) (ρ : AbelianModuli.ReferenceFamily.ActionData.IntegralAction R A)
    (χ : R →+* Γ(M.left, ⊤)) (r : ℕ) : Subfunctor (yoneda.obj M) where
  obj _T := {x | HasCharacterLieRankOnMap A ρ χ r x}
  map f x hx := hasCharacterLieRankOnMap_comp A ρ χ r x hx f.unop

end

end OAI.AlgebraicGeometry.PELModuli.IntegralModel.LieRankCharacter
