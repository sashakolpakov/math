import OAI.NumberTheory.PadicHodge.IntegralComparison.Cech.DiagramSectionCoordinates
import OAI.NumberTheory.PadicHodge.IntegralComparison.Cochain.PairingTransport
import OAI.NumberTheory.PadicHodge.IntegralComparison.Presheaf.TotalLeibniz
import OAI.NumberTheory.PadicHodge.IntegralComparison.Presheaf.CechProductNaturality

/-! # Presheaf Diagram Product -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Cech.PresheafDiagramProduct

noncomputable section

/-! The actual presheaf-valued Čech total carries the signed local
product, with restriction naturality and the original differential rule. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits Opposite

open OAI.NumberTheory.PadicHodge.IntegralComparison.Cech.DiagramSectionCoordinates
universe u v d e r t
variable {C : Type u} [Category.{v} C] [HasBinaryProducts C]
  {D : Type d} [Category.{e} D] (R : Type r) [CommRing R]
  {ι : Type} [Finite ι] (U : ι → C)
  (P : Cᵒᵖ ⥤ CochainComplex (Dᵒᵖ ⥤ ModuleCat.{t} R) ℕ)

local notation "N" => OAI.NumberTheory.PadicHodge.IntegralComparison.NonemptyCechNerve.nerve U
local notation "K" => OAI.NumberTheory.PadicHodge.GeometricComparison.CechCone.Total.CechConeTotal.total U P

variable (μ : ∀ n m (V : Cᵒᵖ) (T : Dᵒᵖ), ((P.obj V).X n).obj T →ₗ[R]
  ((P.obj V).X m).obj T →ₗ[R] ((P.obj V).X (n + m)).obj T)

def nativePairing (T : Dᵒᵖ) (n m : ℕ) (V : Cᵒᵖ) :
    ((DiagramSectionCoordinates.complex R P T).X n).obj V →ₗ[R] ((DiagramSectionCoordinates.complex R P T).X m).obj V →ₗ[R]
      ((DiagramSectionCoordinates.complex R P T).X (n + m)).obj V := μ n m V T

def nativeCup (T : Dᵒᵖ) := Presheaf.TotalCup.CechProduct.totalCup.{u,v,0,t,r}
  N (DiagramSectionCoordinates.complex R P T) (nativePairing R P μ T)

def pairing (n m : ℕ) (T : Dᵒᵖ) : ((K).X n).obj T →ₗ[R] ((K).X m).obj T →ₗ[R]
    ((K).X (n + m)).obj T :=
  Cochain.PairingTransport.cup (DiagramSectionCoordinates.totalIso R U P T) (nativeCup R U P μ T) n m

variable (hD : ∀ n m (V : Cᵒᵖ) {T T' : Dᵒᵖ} (α : T ⟶ T') x y,
  ((P.obj V).X (n + m)).map α (μ n m V T x y) =
    μ n m V T' (((P.obj V).X n).map α x) (((P.obj V).X m).map α y))

include hD in
theorem naturality (n m : ℕ) {T T' : Dᵒᵖ} (α : T ⟶ T')
    (x : ((K).X n).obj T) (y : ((K).X m).obj T) :
    ((K).X (n + m)).map α (pairing R U P μ n m T x y) =
      pairing R U P μ n m T' (((K).X n).map α x) (((K).X m).map α y) :=
  Cochain.PairingTransport.naturality (DiagramSectionCoordinates.totalIso R U P T) (nativeCup R U P μ T)
    (DiagramSectionCoordinates.totalIso R U P T') (nativeCup R U P μ T')
    (((DiagramSectionCoordinates.evaluationMap R α).mapHomologicalComplex (.up ℕ)).app K) (DiagramSectionCoordinates.totalMap R U P α)
    (DiagramSectionCoordinates.total_natural R U P α)
    (Presheaf.CechProductNaturality.totalMap_pairing N (nativePairing R P μ T)
      (nativePairing R P μ T') (DiagramSectionCoordinates.complexMap R P α) (fun n m V x y => hD n m V α x y))
    n m x y

variable (hC : ∀ n m {V V' : Cᵒᵖ} (α : V ⟶ V') (T : Dᵒᵖ) x y,
  ((P.map α).f (n + m)).app T (μ n m V T x y) =
    μ n m V' T (((P.map α).f n).app T x) (((P.map α).f m).app T y))
  (dμ : ∀ n m (T : Dᵒᵖ) (V : Cᵒᵖ) x y,
    ((DiagramSectionCoordinates.complex R P T).d (n + m) (n + m + 1)).app V (μ n m V T x y) =
      Presheaf.CechProduct.sectionDegreeCast (DiagramSectionCoordinates.complex R P T)
        (by omega : (n + 1) + m = n + m + 1) V
        (μ (n + 1) m V T (((DiagramSectionCoordinates.complex R P T).d n (n + 1)).app V x) y) +
      (-1 : ℤ) ^ n • Presheaf.CechProduct.sectionDegreeCast (DiagramSectionCoordinates.complex R P T)
        (by omega : n + (m + 1) = n + m + 1) V
        (μ n (m + 1) V T x (((DiagramSectionCoordinates.complex R P T).d m (m + 1)).app V y)))

include hC dμ in
theorem differential (n m : ℕ) (T : Dᵒᵖ)
    (x : ((K).X n).obj T) (y : ((K).X m).obj T) :
    ((K).d (n + m) (n + m + 1)).app T (pairing R U P μ n m T x y) =
      Presheaf.CechProduct.sectionDegreeCast K (by omega : (n + 1) + m = n + m + 1) T
        (pairing R U P μ (n + 1) m T (((K).d n (n + 1)).app T x) y) +
      (-1 : ℤ) ^ n • Presheaf.CechProduct.sectionDegreeCast K
        (by omega : n + (m + 1) = n + m + 1) T
        (pairing R U P μ n (m + 1) T x (((K).d m (m + 1)).app T y)) :=
  Cochain.PairingTransport.differential (DiagramSectionCoordinates.totalIso R U P T) (nativeCup R U P μ T)
    (Presheaf.TotalLeibniz.CechProduct.differential_totalCup N (DiagramSectionCoordinates.complex R P T) (nativePairing R P μ T)
      (fun n m _ _ α x y => hC n m α T x y) (fun n m V x y => dμ n m T V x y)) n m x y

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Cech.PresheafDiagramProduct
