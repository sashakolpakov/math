import OAI.NumberTheory.PadicHodge.IntegralComparison.FrameCech.Differential

/-! # Transformation -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.FrameCech.Transformation

noncomputable section

/-! Compatible coefficient maps define a morphism of the native frame Čech complexes. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits Opposite

universe u v

variable {C D : Type (max u v)} [Category.{v} C] [Category.{v} D]
  [HasBinaryProducts C] [HasBinaryProducts D] {ι : Type v} (F : ι → C) (G : ι → D)
  (R : Type (max u v)) [CommRing R]

local instance moduleProducts : HasProducts.{v} (ModuleCat.{max u v} R) := by
  let h : HasLimitsOfSize.{v, v} (ModuleCat.{max u v} R) :=
    ModuleCat.hasLimitsOfSize.{v, v, max u v, max u v}
  exact fun I => h.has_limits_of_shape (Discrete I)

variable (H : Cᵒᵖ ⥤ ModuleCat.{max u v} R) (J : Dᵒᵖ ⥤ ModuleCat.{max u v} R)
  (c : ∀ (a : ℕ) (t : Fin (a + 1) → ι),
    H.obj (op (Presentation.TupleProducts.family F a t)) ⟶
      J.obj (op (Presentation.TupleProducts.family G a t)))

def term (a : ℕ) : (Differential.complex F R H).X a ⟶
    (Differential.complex G R J).X a := Limits.Pi.map (c a)

theorem coordinate (a : ℕ) (t : Fin (a + 1) → ι) (x : (Differential.complex F R H).X a) :
    Differential.coordinate G R J a t (term F G R H J c a x) =
      c a t (Differential.coordinate F R H a t x) :=
  congrArg (fun f => f x) (Pi.map_π (c a) t)

variable (hc : ∀ (a b : ℕ) (θ : Fin (b + 1) → Fin (a + 1)) (t : Fin (a + 1) → ι),
  c b (t ∘ θ) ≫ J.map (Presentation.ResolutionFaceMaps.productMap G θ t).op =
    H.map (Presentation.ResolutionFaceMaps.productMap F θ t).op ≫ c a t)

include hc in
theorem comm (a : ℕ) : term F G R H J c a ≫ (Differential.complex G R J).d a (a + 1) =
    (Differential.complex F R H).d a (a + 1) ≫ term F G R H J c (a + 1) := by
  apply Pi.hom_ext
  intro t
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  have hs := Finset.sum_congr (s₁ := Finset.univ) (s₂ := Finset.univ) rfl
    (fun (i : Fin (a + 2)) _ => congrArg (fun y => (-1 : ℤ) ^ (i : ℕ) • y)
      ((congrArg (fun y => J.map (Presentation.ResolutionFaceMaps.productMap G i.succAbove t).op y)
        (coordinate F G R H J c a (t ∘ i.succAbove) x)).trans
          (congrArg (fun f => f (Differential.coordinate F R H a (t ∘ i.succAbove) x))
            (hc (a + 1) a i.succAbove t))))
  have hm : c (a + 1) t (∑ i : Fin (a + 2), (-1 : ℤ) ^ (i : ℕ) •
      H.map (Presentation.ResolutionFaceMaps.productMap F i.succAbove t).op
        (Differential.coordinate F R H a (t ∘ i.succAbove) x)) =
      ∑ i : Fin (a + 2), (-1 : ℤ) ^ (i : ℕ) • c (a + 1) t
        (H.map (Presentation.ResolutionFaceMaps.productMap F i.succAbove t).op
          (Differential.coordinate F R H a (t ∘ i.succAbove) x)) := by
    simp only [map_sum, map_zsmul]
  exact (Differential.coordinates G R J a t (term F G R H J c a x)).trans
    (hs.trans (hm.symm.trans ((congrArg (fun y => c (a + 1) t y)
      (Differential.coordinates F R H a t x).symm).trans
        (coordinate F G R H J c (a + 1) t ((Differential.complex F R H).d a (a + 1) x)).symm)))

def map : Differential.complex F R H ⟶ Differential.complex G R J where
  f := term F G R H J c
  comm' i j hij := by
    have h : i + 1 = j := hij
    subst j
    exact comm F G R H J c hc i

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.FrameCech.Transformation
