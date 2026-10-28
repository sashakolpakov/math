import OAI.NumberTheory.PadicHodge.GeometricComparison.CechPresheaf.QuotientProjection
import OAI.NumberTheory.PadicHodge.IntegralComparison.Module.IdealQuotientProduct
import OAI.NumberTheory.PadicHodge.IntegralComparison.Presheaf.CohomologyProduct

/-! # Ideal Quotient Product -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Presheaf.IdealQuotientProduct

noncomputable section

/-! The original pointwise coefficient quotient of a presheaf complex
inherits its product; the literal Čech reduction preserves that product. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits

universe u v
variable {R : Type} [CommRing R] (I : Ideal R) {C : Type u} [Category.{v} C]
  (P : CochainComplex (Cᵒᵖ ⥤ ModuleCat.{0} R) ℕ)
  (μ : ∀ i j (U : Cᵒᵖ), (P.X i).obj U →ₗ[R] (P.X j).obj U →ₗ[R] (P.X (i+j)).obj U)

abbrev complex := GeometricComparison.CechPresheaf.CoefficientTotal.CechPresheafCoefficientTotal.mappedComplex (Module.IdealQuotient.functor R I) P

def pairing (i j : ℕ) (U : Cᵒᵖ) :
    ((complex I P).X i).obj U →ₗ[R] ((complex I P).X j).obj U →ₗ[R]
      ((complex I P).X (i+j)).obj U := Module.IdealQuotientProduct.pairing I (μ i j U)

theorem projection_pairing (i j : ℕ) (U : Cᵒᵖ) (x : (P.X i).obj U) (y : (P.X j).obj U) :
    ((GeometricComparison.CechPresheaf.QuotientProjection.CechPresheafQuotientProjection.complex R I P).f (i+j)).app U (μ i j U x y) =
      pairing I P μ i j U
        (((GeometricComparison.CechPresheaf.QuotientProjection.CechPresheafQuotientProjection.complex R I P).f i).app U x)
        (((GeometricComparison.CechPresheaf.QuotientProjection.CechPresheafQuotientProjection.complex R I P).f j).app U y) := rfl

variable (hμ : ∀ i j {U V : Cᵒᵖ} (f : U ⟶ V) (x : (P.X i).obj U) (y : (P.X j).obj U),
  (P.X (i+j)).map f (μ i j U x y) = μ i j V ((P.X i).map f x) ((P.X j).map f y))

include hμ in
theorem natural (i j : ℕ) {U V : Cᵒᵖ} (f : U ⟶ V)
    (x : ((complex I P).X i).obj U) (y : ((complex I P).X j).obj U) :
    ((complex I P).X (i+j)).map f (pairing I P μ i j U x y) =
      pairing I P μ i j V (((complex I P).X i).map f x) (((complex I P).X j).map f y) :=
  Module.IdealQuotientProduct.pairing_natural I (μ i j U) (μ i j V)
    ((P.X i).map f) ((P.X j).map f) ((P.X (i+j)).map f) (hμ i j f) x y

theorem projection_cast {i j : ℕ} (h : i=j) (U : Cᵒᵖ) (x : (P.X i).obj U) :
    (I • ⊤ : Submodule R ((P.X j).obj U)).mkQ
      (CechProduct.sectionDegreeCast P h U x) =
    CechProduct.sectionDegreeCast (complex I P) h U
      ((I • ⊤ : Submodule R ((P.X i).obj U)).mkQ x) := by
  subst j
  rfl

variable (dμ : ∀ i j (U : Cᵒᵖ) (x : (P.X i).obj U) (y : (P.X j).obj U),
  (P.d (i+j) (i+j+1)).app U (μ i j U x y) =
    CechProduct.sectionDegreeCast P (by omega) U
      (μ (i+1) j U ((P.d i (i+1)).app U x) y) +
    (-1 : ℤ)^i • CechProduct.sectionDegreeCast P (by omega) U
      (μ i (j+1) U x ((P.d j (j+1)).app U y)))

include dμ in
theorem differential (i j : ℕ) (U : Cᵒᵖ)
    (x : ((complex I P).X i).obj U) (y : ((complex I P).X j).obj U) :
    ((complex I P).d (i+j) (i+j+1)).app U (pairing I P μ i j U x y) =
      CechProduct.sectionDegreeCast (complex I P) (by omega) U
        (pairing I P μ (i+1) j U (((complex I P).d i (i+1)).app U x) y) +
      (-1 : ℤ)^i • CechProduct.sectionDegreeCast (complex I P) (by omega) U
        (pairing I P μ i (j+1) U x (((complex I P).d j (j+1)).app U y)) := by
  obtain ⟨x, rfl⟩ := (I • ⊤ : Submodule R ((P.X i).obj U)).mkQ_surjective x
  obtain ⟨y, rfl⟩ := (I • ⊤ : Submodule R ((P.X j).obj U)).mkQ_surjective y
  change (I • ⊤ : Submodule R ((P.X (i+j+1)).obj U)).mkQ
    ((P.d (i+j) (i+j+1)).app U (μ i j U x y)) = _
  rw [dμ, map_add, map_zsmul, projection_cast, projection_cast]
  rfl

variable (N : SimplicialObject (FormalCoproduct.{0} C))

abbrev cohomologyCup := CohomologyProduct.Cech.cohomologyCup N (complex I P)
  (pairing I P μ) (natural I P μ hμ) (differential I P μ dμ)

abbrev map_cohomologyCup := CohomologyProduct.Cech.totalMap_cohomologyCup N P μ hμ dμ
  (complex I P) (pairing I P μ) (natural I P μ hμ) (differential I P μ dμ)
  (GeometricComparison.CechPresheaf.QuotientProjection.CechPresheafQuotientProjection.complex R I P) (projection_pairing I P μ)

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Presheaf.IdealQuotientProduct
