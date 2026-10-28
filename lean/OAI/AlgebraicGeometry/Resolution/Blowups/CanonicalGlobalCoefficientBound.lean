import OAI.AlgebraicGeometry.Resolution.Blowups.GlobalCoefficient.BoundRestriction
import OAI.AlgebraicGeometry.Resolution.Blowups.GlobalComponent.FiniteBound

/-! # Canonical Global Coefficient Bound -/

namespace OAI.AlgebraicGeometry.Resolution.Blowups

noncomputable section

/-! The least global coefficient bound is independent of the finite atlas and cannot increase under étale restriction. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

variable {X : Scheme} {f : X ⟶ Foundations.Scheme.ProjectiveSpace.complexBase} {J : X.IdealSheafData} {n : ℕ}

theorem GlobalComponent.ChoiceAtlas.Construction.GlobalComponentChoiceAtlas.hasBound_iff_atlas (A B : GlobalComponent.ChoiceAtlas.Construction.GlobalComponentChoiceAtlas f J n) (m : ℕ) :
    (∀ i, (A.choice i).HasBound m) ↔ ∀ i, (B.choice i).HasBound m := by
  constructor
  · intro h i
    exact A.hasBound_restrict_etale m h (B.rings i) (B.map i) (B.ground i)
      (B.ideals i) (B.ideal_eq i) (B.choice i)
  · intro h i
    exact B.hasBound_restrict_etale m h (A.rings i) (A.map i) (A.ground i)
      (A.ideals i) (A.ideal_eq i) (A.choice i)

def GlobalComponent.ChoiceAtlas.Construction.GlobalComponentChoiceAtlas.coefficientBound (A : GlobalComponent.ChoiceAtlas.Construction.GlobalComponentChoiceAtlas f J n) (hc : A.center = ⊤) : ℕ := by
  classical
  exact Nat.find (A.exists_uniform_bound hc)

theorem GlobalComponent.ChoiceAtlas.Construction.GlobalComponentChoiceAtlas.hasBound_coefficientBound (A : GlobalComponent.ChoiceAtlas.Construction.GlobalComponentChoiceAtlas f J n) (hc : A.center = ⊤) :
    ∀ i, (A.choice i).HasBound (A.coefficientBound hc) := by
  classical
  exact Nat.find_spec (A.exists_uniform_bound hc)

theorem GlobalComponent.ChoiceAtlas.Construction.GlobalComponentChoiceAtlas.coefficientBound_le_iff (A : GlobalComponent.ChoiceAtlas.Construction.GlobalComponentChoiceAtlas f J n) (hc : A.center = ⊤) (m : ℕ) :
    A.coefficientBound hc ≤ m ↔ ∀ i, (A.choice i).HasBound m := by
  classical
  constructor
  · intro h i
    exact (A.choice i).hasBound_mono (A.hasBound_coefficientBound hc i) h
  · intro h
    exact Nat.find_min' (A.exists_uniform_bound hc) h

theorem GlobalComponent.ChoiceAtlas.Construction.GlobalComponentChoiceAtlas.coefficientBound_eq (A B : GlobalComponent.ChoiceAtlas.Construction.GlobalComponentChoiceAtlas f J n)
    (hA : A.center = ⊤) (hB : B.center = ⊤) : A.coefficientBound hA = B.coefficientBound hB := by
  apply Nat.le_antisymm
  · apply (A.coefficientBound_le_iff hA _).mpr
    exact (A.hasBound_iff_atlas B _).mpr (B.hasBound_coefficientBound hB)
  · apply (B.coefficientBound_le_iff hB _).mpr
    exact (A.hasBound_iff_atlas B _).mp (A.hasBound_coefficientBound hA)

theorem GlobalComponent.ChoiceAtlas.Construction.GlobalComponentChoiceAtlas.hasBound_comap_etale (A : GlobalComponent.ChoiceAtlas.Construction.GlobalComponentChoiceAtlas f J n) (m : ℕ)
    (hb : ∀ i, (A.choice i).HasBound m) {Y : Scheme} (g : Y ⟶ X) [Etale g]
    (B : GlobalComponent.ChoiceAtlas.Construction.GlobalComponentChoiceAtlas (g ≫ f) (J.comap g) n) : ∀ i, (B.choice i).HasBound m := by
  intro i
  apply A.hasBound_restrict_etale m hb (B.rings i) (B.map i ≫ g)
  · rw [Category.assoc]
    exact B.ground i
  · rw [Scheme.IdealSheafData.comap_comp]
    exact B.ideal_eq i

theorem GlobalComponent.ChoiceAtlas.Construction.GlobalComponentChoiceAtlas.coefficientBound_comap_etale_le (A : GlobalComponent.ChoiceAtlas.Construction.GlobalComponentChoiceAtlas f J n) (hA : A.center = ⊤)
    {Y : Scheme} (g : Y ⟶ X) [Etale g]
    (B : GlobalComponent.ChoiceAtlas.Construction.GlobalComponentChoiceAtlas (g ≫ f) (J.comap g) n) (hB : B.center = ⊤) :
    B.coefficientBound hB ≤ A.coefficientBound hA :=
  (B.coefficientBound_le_iff hB _).mpr
    (A.hasBound_comap_etale _ (A.hasBound_coefficientBound hA) g B)

end

end OAI.AlgebraicGeometry.Resolution.Blowups
