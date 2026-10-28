import OAI.AlgebraicGeometry.AbelianScheme.TateComparison.FieldExtension
import OAI.AlgebraicGeometry.AbelianScheme.TateComparison.TateProducts

/-! # Tate Base Change -/

namespace OAI.AlgebraicGeometry.AbelianScheme.TateComparison.TateBaseChange

noncomputable section

/-! The pullback adjunction on actual abelian-scheme points induces
natural integral and rational Tate comparisons. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj TensorProduct

universe u

variable {S S' : Scheme.{u}} {g g' : ℕ}
  (A : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme g S) (f : S' ⟶ S) (T : Over S') (q : ℕ) [Fact q.Prime]

instance abelianPullbackMap_isMonHom {B : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme g' S}
    (a : A.scheme ⟶ B.scheme) [IsMonHom a] :
    IsMonHom (show (A.pullback f).scheme ⟶ (B.pullback f).scheme from
      (Over.pullback f).map a) :=
  Functor.map.instIsMonHom (F := Over.pullback f) (f := a)

def baseChangeTateEquiv :
    Add.schemeTateModule (A.pullback f).scheme T q ≃ₗ[ℤ_[q]]
      Add.schemeTateModule A.scheme ((Over.map f).obj T) q :=
  TateProducts.Tate.mapEquiv q (A.baseChangePointsMulEquiv f T).toAdditive

theorem baseChangeTateEquiv_natural {B : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme g' S}
    (a : A.scheme ⟶ B.scheme) [IsMonHom a]
    (z : Add.schemeTateModule (A.pullback f).scheme T q) :
    baseChangeTateEquiv B f T q
      (Add.schemeTateMap (A.pullback f).scheme (B := (B.pullback f).scheme) T q
        ((Over.pullback f).map a) z) =
        Add.schemeTateMap A.scheme ((Over.map f).obj T) q a (baseChangeTateEquiv A f T q z) := by
  apply Subtype.ext
  funext n
  apply Subtype.ext
  apply Additive.toMul.injective
  exact AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme.baseChangePointsEquiv_map a f T (z.val n).val.toMul

def baseChangeRationalTateEquiv :
    Rational.rationalTateModule (A.pullback f).scheme T q ≃ₗ[ℚ_[q]]
      Rational.rationalTateModule A.scheme ((Over.map f).obj T) q :=
  LinearEquiv.baseChange ℤ_[q] ℚ_[q] _ _ (baseChangeTateEquiv A f T q)

theorem baseChangeRationalTateEquiv_natural {B : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme g' S}
    (a : A.scheme ⟶ B.scheme) [IsMonHom a]
    (z : Rational.rationalTateModule (A.pullback f).scheme T q) :
    baseChangeRationalTateEquiv B f T q
      (Rational.rationalTateMap (A := (A.pullback f).scheme) (B := (B.pullback f).scheme)
        (T := T) (q := q) ((Over.pullback f).map a) z) =
        Rational.rationalTateMap (T := (Over.map f).obj T) (q := q) a
          (baseChangeRationalTateEquiv A f T q z) := by
  induction z using TensorProduct.inductionOn with
  | add z w hz hw => simp only [LinearEquiv.map_add, LinearMap.map_add, hz, hw]
  | tmul c z =>
    change c ⊗ₜ[ℤ_[q]] baseChangeTateEquiv B f T q
        (Add.schemeTateMap (A.pullback f).scheme (B := (B.pullback f).scheme) T q
          ((Over.pullback f).map a) z) =
      c ⊗ₜ[ℤ_[q]] Add.schemeTateMap A.scheme ((Over.map f).obj T) q a
        (baseChangeTateEquiv A f T q z)
    rw [baseChangeTateEquiv_natural]

end

end OAI.AlgebraicGeometry.AbelianScheme.TateComparison.TateBaseChange
