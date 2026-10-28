import OAI.NumberTheory.PadicHodge.IntegralComparison.Crystalline.CoefficientPairing
import OAI.NumberTheory.PadicHodge.IntegralComparison.Sheafified.CochainUnit
import OAI.NumberTheory.PadicHodge.IntegralComparison.Module.SheafTensor

/-! # Sheaf Complex Product -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Crystalline.SheafComplexProduct

noncomputable section

/-! Native crystalline coefficient lifting and sheafification preserve
a presheaf-complex product and its actual graded differential rule. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits

universe u v w
variable {D : Type v} [Category.{w} D] (B : Type u) [CommRing B]
  (J : GrothendieckTopology D)
  [HasSheafify J (ModuleCat.{u + 1} (ExactRestriction.Coeff (B := B)))]
  (P : CochainComplex (Dᵒᵖ ⥤ ModuleCat.{u} B) ℕ)

local notation "CR" => OAI.NumberTheory.PadicHodge.IntegralComparison.Crystalline.ExactRestriction.Coeff (B := B)

abbrev coefficients := (Functor.whiskeringRight Dᵒᵖ (ModuleCat.{u} B) (ModuleCat.{u + 1} CR)).obj
  (RelativeResolution.coefficientFunctor (B := B))

def coefficientComplex := ((coefficients B).mapHomologicalComplex (.up ℕ)).obj P

variable (μ : ∀ a b (T : Dᵒᵖ), (P.X a).obj T →ₗ[B] (P.X b).obj T →ₗ[B] (P.X (a + b)).obj T)
  (hμ : ∀ a b {T T' : Dᵒᵖ} (α : T ⟶ T') x y,
    (P.X (a + b)).map α (μ a b T x y) = μ a b T' ((P.X a).map α x) ((P.X b).map α y))

def coefficientPairing (a b : ℕ) (T : Dᵒᵖ) := CoefficientPairing.lift B
  ((P.X a).obj T) ((P.X b).obj T) ((P.X (a + b)).obj T) (μ a b T)

include hμ in
theorem coefficientPairing_natural (a b : ℕ) {T T' : Dᵒᵖ} (α : T ⟶ T')
    (x : ((coefficientComplex B P).X a).obj T) (y : ((coefficientComplex B P).X b).obj T) :
    ((coefficientComplex B P).X (a + b)).map α (coefficientPairing B P μ a b T x y) =
      coefficientPairing B P μ a b T'
        (((coefficientComplex B P).X a).map α x) (((coefficientComplex B P).X b).map α y) :=
  CoefficientPairing.map_lift B _ _ _ (P.X a |>.map α) (P.X b |>.map α)
    (P.X (a + b) |>.map α) (μ a b T) (μ a b T') (hμ a b α) x y

theorem degreeCast_down {a b : ℕ} (h : a = b) (T : Dᵒᵖ)
    (x : ((coefficientComplex B P).X a).obj T) :
    (Presheaf.CechProduct.sectionDegreeCast (coefficientComplex B P) h T x).down =
      Presheaf.CechProduct.sectionDegreeCast P h T x.down := by
  subst b
  rfl

variable (dμ : ∀ a b (T : Dᵒᵖ) x y,
  (P.d (a + b) (a + b + 1)).app T (μ a b T x y) =
    Presheaf.CechProduct.sectionDegreeCast P (by omega : (a + 1) + b = a + b + 1) T
      (μ (a + 1) b T ((P.d a (a + 1)).app T x) y) +
    (-1 : ℤ) ^ a • Presheaf.CechProduct.sectionDegreeCast P
      (by omega : a + (b + 1) = a + b + 1) T (μ a (b + 1) T x ((P.d b (b + 1)).app T y)))

include dμ in
theorem coefficientPairing_differential (a b : ℕ) (T : Dᵒᵖ)
    (x : ((coefficientComplex B P).X a).obj T) (y : ((coefficientComplex B P).X b).obj T) :
    ((coefficientComplex B P).d (a + b) (a + b + 1)).app T (coefficientPairing B P μ a b T x y) =
      Presheaf.CechProduct.sectionDegreeCast (coefficientComplex B P)
        (by omega : (a + 1) + b = a + b + 1) T
        (coefficientPairing B P μ (a + 1) b T (((coefficientComplex B P).d a (a + 1)).app T x) y) +
      (-1 : ℤ) ^ a • Presheaf.CechProduct.sectionDegreeCast (coefficientComplex B P)
        (by omega : a + (b + 1) = a + b + 1) T
        (coefficientPairing B P μ a (b + 1) T x (((coefficientComplex B P).d b (b + 1)).app T y)) := by
  apply ULift.ext
  change (P.d (a + b) (a + b + 1)).app T (μ a b T x.down y.down) =
    (Presheaf.CechProduct.sectionDegreeCast (coefficientComplex B P)
      (by omega : (a + 1) + b = a + b + 1) T
      (coefficientPairing B P μ (a + 1) b T (((coefficientComplex B P).d a (a + 1)).app T x) y)).down +
    (-1 : ℤ) ^ a • (Presheaf.CechProduct.sectionDegreeCast (coefficientComplex B P)
      (by omega : a + (b + 1) = a + b + 1) T
      (coefficientPairing B P μ a (b + 1) T x (((coefficientComplex B P).d b (b + 1)).app T y))).down
  erw [degreeCast_down, degreeCast_down]
  exact dμ a b T x.down y.down

variable [hmonoidal : (J.W (A := ModuleCat.{u + 1} (ExactRestriction.Coeff (B := B)))).IsMonoidal]

def underlyingComplex := Sheafified.CochainPairing.complex J CR (coefficientComplex B P)
def sectionPairing := Sheafified.CochainPairing.pairing J CR (coefficientComplex B P)
  (coefficientPairing B P μ) (coefficientPairing_natural B P μ hμ)
abbrev sectionPairing_natural := Sheafified.CochainUnit.Pairing.pairing_natural.{v,w,u + 1} J CR (coefficientComplex B P)
  (coefficientPairing B P μ) (coefficientPairing_natural B P μ hμ)
abbrev sectionPairing_differential := Sheafified.CochainPairing.differential J CR (coefficientComplex B P)
  (coefficientPairing B P μ) (coefficientPairing_natural B P μ hμ)
  (coefficientPairing_differential B P μ dμ)
abbrev unit_pairing := Sheafified.CochainUnit.Pairing.unit_pairing.{v,w,u + 1} J CR (coefficientComplex B P)
  (coefficientPairing B P μ) (coefficientPairing_natural B P μ hμ)

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Crystalline.SheafComplexProduct
