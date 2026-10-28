import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Moduli.Isomorphisms
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Level.BaseChange
import Mathlib.NumberTheory.NumberField.CMField

/-! # Action Data -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.ActionData

noncomputable section

/-! Integral endomorphism actions and the Rosati condition, expressed by
actual group-scheme morphisms and the normalized Poincare bundle. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj

universe u v

variable {R : Type v} [CommRing R] {g : ℕ} {S T : Scheme.{u}}

/-- A unital ring action by endomorphisms of an abelian scheme.
Addition of endomorphisms is multiplication in its abelian group law. -/
structure IntegralAction (R : Type v) [CommRing R] (A : HilbertConstruction.Abelian.Schemes.AbelianScheme g S) where
  map : R → (A.scheme ⟶ A.scheme)
  preservesGroup : ∀ a, IsMonHom (map a)
  map_zero : map 0 = 1
  map_one : map 1 = 𝟙 A.scheme
  map_add : ∀ a b, map (a + b) = map a * map b
  map_mul : ∀ a b, map (a * b) = map b ≫ map a

attribute [instance] IntegralAction.preservesGroup

namespace IntegralAction

/-- Base change of the action uses the actual pullback functor. -/
def pullback {A : HilbertConstruction.Abelian.Schemes.AbelianScheme g S} (ρ : IntegralAction R A)
    (f : T ⟶ S) : IntegralAction R (A.pullback f) where
  map a := (Over.pullback f).map (ρ.map a)
  preservesGroup a := by
    let := ρ.preservesGroup a
    exact inferInstanceAs (IsMonHom ((Over.pullback f).map (ρ.map a)))
  map_zero := by
    dsimp only [HilbertConstruction.Abelian.Schemes.AbelianScheme.pullback]
    rw [ρ.map_zero]
    exact (Over.pullback f).map_one
  map_one := by
    dsimp only [HilbertConstruction.Abelian.Schemes.AbelianScheme.pullback]
    rw [ρ.map_one]
    exact (Over.pullback f).map_id _
  map_add a b := by
    dsimp only [HilbertConstruction.Abelian.Schemes.AbelianScheme.pullback]
    rw [ρ.map_add]
    exact (Over.pullback f).map_mul _ _
  map_mul a b := by
    dsimp only [HilbertConstruction.Abelian.Schemes.AbelianScheme.pullback]
    rw [ρ.map_mul]
    exact (Over.pullback f).map_comp _ _

/-- The action commutes with change of the test scheme. -/
theorem points_naturality {A : HilbertConstruction.Abelian.Schemes.AbelianScheme g S}
    (ρ : IntegralAction R A) (a : R) {X Y : Over S}
    (f : X ⟶ Y) (x : Y ⟶ A.scheme) :
    (f ≫ x) ≫ ρ.map a = f ≫ (x ≫ ρ.map a) := Category.assoc _ _ _

end IntegralAction

variable {E : Type v} [Field E] [NumberField E] [NumberField.IsCMField E]
  {N : ℕ} {δ : Fin g → ℕ}

/-- The dual endomorphism is characterized by its Poincare pullback,
and its polarization adjoint is the action of CM conjugation. -/
def RosatiConjugation (A : HilbertConstruction.PolarizationData.PolarizedAbelianWithFullLevel g δ N S)
    (ρ : IntegralAction (NumberField.RingOfIntegers E) A.abelian) : Prop :=
  ∀ a : NumberField.RingOfIntegers E,
    ∃ dualMap : A.dual.abelian.scheme ⟶ A.dual.abelian.scheme,
      IsMonHom dualMap ∧
      HilbertConstruction.Line.Bundles.LineBundle.pullbackClass (dualMap ⊗ₘ 𝟙 A.abelian.scheme).left
          (HilbertConstruction.Line.Bundles.LineBundle.classOf A.dual.poincare) =
        HilbertConstruction.Line.Bundles.LineBundle.pullbackClass (𝟙 A.dual.abelian.scheme ⊗ₘ ρ.map a).left
          (HilbertConstruction.Line.Bundles.LineBundle.classOf A.dual.poincare) ∧
      A.polarization.isogeny.hom ≫ dualMap =
        ρ.map (NumberField.IsCMField.ringOfIntegersComplexConj E a) ≫
          A.polarization.isogeny.hom

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.ActionData
