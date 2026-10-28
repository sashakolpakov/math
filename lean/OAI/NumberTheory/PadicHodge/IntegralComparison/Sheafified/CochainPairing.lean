import OAI.NumberTheory.PadicHodge.IntegralComparison.Sheafified.BilinearDifferential
import OAI.NumberTheory.PadicHodge.IntegralComparison.Presheaf.CechProduct

/-! # Cochain Pairing -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Sheafified.CochainPairing

noncomputable section

/-! Sheafification preserves the graded Leibniz identity, including the
literal degree transports in the native presheaf Čech construction. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits

universe u v w

variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)
  (R : Type w) [CommRing R] [HasSheafify J (ModuleCat.{w} R)]
  [(J.W (A := ModuleCat.{w} R)).IsMonoidal]
  (P : CochainComplex (Cᵒᵖ ⥤ ModuleCat.{w} R) ℕ)

local notation "S" => presheafToSheaf J (ModuleCat R)
local notation "U" => sheafToPresheaf J (ModuleCat R)

def complex := (((S ⋙ U).mapHomologicalComplex (.up ℕ))).obj P

variable (μ : ∀ a b (V : Cᵒᵖ), (P.X a).obj V →ₗ[R]
  (P.X b).obj V →ₗ[R] (P.X (a + b)).obj V)
  (hμ : ∀ a b {V W : Cᵒᵖ} (f : V ⟶ W) x y,
    (P.X (a + b)).map f (μ a b V x y) = μ a b W ((P.X a).map f x) ((P.X b).map f y))

def pairing (a b : ℕ) (V : Cᵒᵖ) :=
  BilinearPairing.pairing R (P.X a) (P.X b) (P.X (a + b))
    (μ a b) (hμ a b) J V

def castPairing (a b c : ℕ) (h : a + b = c) :
    ∀ V, (P.X a).obj V →ₗ[R] (P.X b).obj V →ₗ[R] (P.X c).obj V := h ▸ μ a b

theorem castPairing_apply (a b c : ℕ) (h : a + b = c) (V : Cᵒᵖ)
    (x : (P.X a).obj V) (y : (P.X b).obj V) :
    castPairing R P μ a b c h V x y =
      Presheaf.CechProduct.sectionDegreeCast P h V (μ a b V x y) := by
  subst c
  rfl

include hμ in
theorem castPairing_natural (a b c : ℕ) (h : a + b = c)
    {V W : Cᵒᵖ} (f : V ⟶ W) (x : (P.X a).obj V) (y : (P.X b).obj V) :
    (P.X c).map f (castPairing R P μ a b c h V x y) =
      castPairing R P μ a b c h W ((P.X a).map f x) ((P.X b).map f y) := by
  subst c
  exact hμ a b f x y

theorem pairing_cast (a b c : ℕ) (h : a + b = c) (V : Cᵒᵖ)
    (x : ((complex J R P).X a).obj V) (y : ((complex J R P).X b).obj V) :
    BilinearPairing.pairing R (P.X a) (P.X b) (P.X c)
      (castPairing R P μ a b c h) (castPairing_natural R P μ hμ a b c h) J V x y =
      Presheaf.CechProduct.sectionDegreeCast (complex J R P) h V
        (pairing J R P μ hμ a b V x y) := by
  subst c
  rfl

variable (dμ : ∀ a b (V : Cᵒᵖ) x y,
  (P.d (a + b) (a + b + 1)).app V (μ a b V x y) =
    Presheaf.CechProduct.sectionDegreeCast P (by omega : (a + 1) + b = a + b + 1) V
      (μ (a + 1) b V ((P.d a (a + 1)).app V x) y) +
    (-1 : ℤ) ^ a • Presheaf.CechProduct.sectionDegreeCast P
      (by omega : a + (b + 1) = a + b + 1) V
      (μ a (b + 1) V x ((P.d b (b + 1)).app V y)))

include dμ in
theorem differential (a b : ℕ) (V : Cᵒᵖ)
    (x : ((complex J R P).X a).obj V) (y : ((complex J R P).X b).obj V) :
    ((complex J R P).d (a + b) (a + b + 1)).app V (pairing J R P μ hμ a b V x y) =
      Presheaf.CechProduct.sectionDegreeCast (complex J R P)
        (by omega : (a + 1) + b = a + b + 1) V
        (pairing J R P μ hμ (a + 1) b V (((complex J R P).d a (a + 1)).app V x) y) +
      (-1 : ℤ) ^ a • Presheaf.CechProduct.sectionDegreeCast (complex J R P)
        (by omega : a + (b + 1) = a + b + 1) V
        (pairing J R P μ hμ a (b + 1) V x (((complex J R P).d b (b + 1)).app V y)) := by
  have hd : ∀ W s t, (P.d (a + b) (a + b + 1)).app W (μ a b W s t) =
      castPairing R P μ (a + 1) b (a + b + 1) (by omega) W ((P.d a (a + 1)).app W s) t +
      (-1 : ℤ) ^ a • castPairing R P μ a (b + 1) (a + b + 1) (by omega) W s
        ((P.d b (b + 1)).app W t) := by
    intro W s t
    simpa only [castPairing_apply] using dμ a b W s t
  have h := BilinearDifferential.differential J R
    (P.X a) (P.X b) (P.X (a + b)) (P.X (a + 1)) (P.X (b + 1)) (P.X (a + b + 1))
    (P.d a (a + 1)) (P.d b (b + 1)) (P.d (a + b) (a + b + 1))
    (μ a b) (castPairing R P μ (a + 1) b (a + b + 1) (by omega))
    (castPairing R P μ a (b + 1) (a + b + 1) (by omega))
    (hμ a b) (castPairing_natural R P μ hμ (a + 1) b (a + b + 1) (by omega))
    (castPairing_natural R P μ hμ a (b + 1) (a + b + 1) (by omega))
    ((-1 : ℤ) ^ a) hd V x y
  exact h.trans (congrArg₂ (fun s t => s + (-1 : ℤ) ^ a • t)
    (pairing_cast J R P μ hμ (a + 1) b (a + b + 1) (by omega) V
      (((complex J R P).d a (a + 1)).app V x) y)
    (pairing_cast J R P μ hμ a (b + 1) (a + b + 1) (by omega) V x
      (((complex J R P).d b (b + 1)).app V y)))

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Sheafified.CochainPairing
