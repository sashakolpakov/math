import OAI.NumberTheory.PadicHodge.IntegralComparison.CechCoefficient.CohomologyCup
import Mathlib.Algebra.Category.ModuleCat.ChangeOfRingsExact

/-! # Restrict Scalars Presheaf Cup -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.RestrictScalarsPresheafCup

noncomputable section

/-! Scalar restriction preserves the native presheaf wedge and its
actual finite Čech cohomology product. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits Opposite Simplicial

universe u v w r s
variable {C : Type u} [Category.{v} C]
  (R : Type r) (S : Type s) [CommRing R] [CommRing S] [Algebra R S]
  (P : CochainComplex (Cᵒᵖ ⥤ ModuleCat.{w} S) ℕ)
  (μ : ∀ i j U, (P.X i).obj U →ₗ[S] (P.X j).obj U →ₗ[S] (P.X (i+j)).obj U)

local notation "F" => ModuleCat.restrictScalars (algebraMap R S)
local notation "Q" => OAI.NumberTheory.PadicHodge.GeometricComparison.CechPresheaf.CoefficientTotal.CechPresheafCoefficientTotal.mappedComplex F P
local instance restrictedModule (V : ModuleCat.{w} S) : Module R V :=
  Module.compHom V (algebraMap R S)
local instance tower (V : ModuleCat.{w} S) : IsScalarTower R S V where
  smul_assoc r s x := by rw [Algebra.smul_def]; exact mul_smul _ _ _

def pairing (i j : ℕ) (U : Cᵒᵖ) :
    ((Q).X i).obj U →ₗ[R] ((Q).X j).obj U →ₗ[R] ((Q).X (i+j)).obj U :=
  (μ i j U).restrictScalars₁₂ R R

variable
  (hμ : ∀ p q {U V : Cᵒᵖ} (f : U ⟶ V) (x : (P.X p).obj U) (y : (P.X q).obj U),
    (P.X (p+q)).map f (μ p q U x y) = μ p q V ((P.X p).map f x) ((P.X q).map f y))
  (dμ : ∀ p q U (x : (P.X p).obj U) (y : (P.X q).obj U),
    (P.d (p+q) (p+q+1)).app U (μ p q U x y) =
      Presheaf.CechProduct.sectionDegreeCast P (by omega : (p+1)+q=p+q+1) U (μ (p+1) q U ((P.d p (p+1)).app U x) y) +
      (-1 : ℤ)^p • Presheaf.CechProduct.sectionDegreeCast P (by omega : p+(q+1)=p+q+1) U
        (μ p (q+1) U x ((P.d q (q+1)).app U y)))

include hμ in
theorem natural (p q : ℕ) {U V : Cᵒᵖ} (f : U ⟶ V)
    (x : ((Q).X p).obj U) (y : ((Q).X q).obj U) :
    ((Q).X (p+q)).map f (pairing R S P μ p q U x y) =
      pairing R S P μ p q V (((Q).X p).map f x) (((Q).X q).map f y) := hμ p q f x y

private theorem cast_eq {i j : ℕ} (h : i=j) (U : Cᵒᵖ) (x : (P.X i).obj U) :
    Presheaf.CechProduct.sectionDegreeCast Q h U x = Presheaf.CechProduct.sectionDegreeCast P h U x := by subst j; rfl

include dμ in
theorem differential (p q : ℕ) (U : Cᵒᵖ)
    (x : ((Q).X p).obj U) (y : ((Q).X q).obj U) :
    ((Q).d (p+q) (p+q+1)).app U (pairing R S P μ p q U x y) =
      Presheaf.CechProduct.sectionDegreeCast Q (by omega : (p+1)+q=p+q+1) U
        (pairing R S P μ (p+1) q U (((Q).d p (p+1)).app U x) y) +
      (-1 : ℤ)^p • Presheaf.CechProduct.sectionDegreeCast Q (by omega : p+(q+1)=p+q+1) U
        (pairing R S P μ p (q+1) U x (((Q).d q (q+1)).app U y)) := by
  change (P.d (p+q) (p+q+1)).app U (μ p q U x y) =
    Presheaf.CechProduct.sectionDegreeCast Q (by omega : (p+1)+q=p+q+1) U (μ (p+1) q U ((P.d p (p+1)).app U x) y) +
    (-1 : ℤ)^p • Presheaf.CechProduct.sectionDegreeCast Q (by omega : p+(q+1)=p+q+1) U
      (μ p (q+1) U x ((P.d q (q+1)).app U y))
  rw [cast_eq, cast_eq]
  exact dμ p q U x y

variable (E : SimplicialObject (FormalCoproduct.{0} C))
  (hE : ∀ n, Finite (E.obj (op n)).I)

def map (i : ℕ) := CechCoefficient.CohomologyCup.Total.homologyMap F
  (fun M => AddMonoidHom.id M) E hE P i

abbrev map_cup := CechCoefficient.CohomologyCup.Total.homologyMap_cup F
  (fun M => AddMonoidHom.id M) (fun _ _ => rfl) E hE P μ
  (pairing R S P μ) hμ dμ (natural R S P μ hμ) (differential R S P μ dμ)
  (fun _ _ _ _ _ => rfl)

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.RestrictScalarsPresheafCup
