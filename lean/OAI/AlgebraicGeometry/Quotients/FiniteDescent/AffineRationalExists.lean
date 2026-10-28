import OAI.AlgebraicGeometry.Quotients.FiniteDescent.AffineRationalOf
import Mathlib.AlgebraicGeometry.Morphisms.FiniteType

/-! # Affine Rational Exists -/

namespace OAI.AlgebraicGeometry.Quotients.FiniteDescent.AffineRationalExists.Construction.AffineRationalCoordinates

noncomputable section

/-! Finitely many rational coordinate functions detect an affine open of a separated scheme. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

theorem exists_finset {X Y : Scheme.{u}} [IsIntegral X] [X.IsSeparated] [IsAffine Y]
    (f : X ⟶ Y) [LocallyOfFiniteType f] (U : X.affineOpens) [Nonempty U.1] :
    ∃ T : Finset X.functionField, ∀ x : X, x ∈ U.1 ↔
      ∀ r ∈ T, ∃ b : X.presheaf.stalk x, algebraMap _ X.functionField b = r := by
  classical
  let β := (f.appLE ⊤ U.1 le_top).hom
  let : Algebra Γ(Y, ⊤) Γ(X, U) := β.toAlgebra
  have : Algebra.FiniteType Γ(Y, ⊤) Γ(X, U) :=
    f.finiteType_appLE (isAffineOpen_top Y) U.2 le_top
  obtain ⟨T, hT⟩ := (inferInstance : Algebra.FiniteType Γ(Y, ⊤) Γ(X, U)).out
  refine ⟨T.image (X.germToFunctionField U.1), fun x => ?_⟩
  constructor
  · intro hx r hr
    obtain ⟨a, _, rfl⟩ := Finset.mem_image.mp hr
    exact ⟨X.presheaf.germ U.1 x hx a, X.algebraMap_germ_eq_germToFunctionField hx a⟩
  · intro hx
    apply AffineRationalOf.Construction.AffineRationalDomain.mem_of_regular_coordinates U x
    intro a
    have ha : a ∈ Algebra.adjoin Γ(Y, ⊤) (T : Set Γ(X, U)) := by rw [hT]; trivial
    induction ha using Algebra.adjoin_induction with
    | mem a ha => exact hx _ (Finset.mem_image.mpr ⟨a, ha, rfl⟩)
    | algebraMap c =>
      have : Nonempty (⊤ : X.Opens) := ⟨⟨x, trivial⟩⟩
      refine ⟨X.presheaf.germ ⊤ x trivial (f.appTop c),
        (X.algebraMap_germ_eq_germToFunctionField (U := ⊤)
          (show x ∈ (⊤ : X.Opens) from trivial) (f.appTop c)).trans ?_⟩
      change X.germToFunctionField ⊤ (f.appTop c) =
        X.germToFunctionField U.1 (X.presheaf.map (homOfLE (show U.1 ≤ ⊤ from le_top)).op
          (f.appTop c))
      exact (X.presheaf.germ_res_apply (homOfLE (show U.1 ≤ ⊤ from le_top))
        (genericPoint X) _ (f.appTop c)).symm
    | add a b _ _ ha hb =>
      obtain ⟨a', ha'⟩ := ha
      obtain ⟨b', hb'⟩ := hb
      exact ⟨a' + b', by rw [map_add, map_add, ha', hb']⟩
    | mul a b _ _ ha hb =>
      obtain ⟨a', ha'⟩ := ha
      obtain ⟨b', hb'⟩ := hb
      exact ⟨a' * b', by rw [map_mul, map_mul, ha', hb']⟩

end

end OAI.AlgebraicGeometry.Quotients.FiniteDescent.AffineRationalExists.Construction.AffineRationalCoordinates
