import Mathlib.Algebra.Homology.Homotopy

/-! # Quotient Homotopy -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.QuotientHomotopy.Constructions

noncomputable section

/-! A homotopy descends once its actual components factor through a degreewise epimorphism. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits

variable {V : Type*} [Category* V] [Preadditive V]
variable {ι : Type*} {c : ComplexShape ι}
variable {C D C' D' : HomologicalComplex V c}

def quotientHomotopyOfComponents (π : C ⟶ C') (ρ : D ⟶ D')
    [∀ n, Epi (π.f n)] {f g : C ⟶ D} {f' g' : C' ⟶ D'}
    (hf : π ≫ f' = f ≫ ρ) (hg : π ≫ g' = g ≫ ρ) (H : Homotopy f g)
    (K : ∀ a b, C'.X a ⟶ D'.X b)
    (hK : ∀ a b, π.f a ≫ K a b = H.hom a b ≫ ρ.f b) : Homotopy f' g' := by
  refine { hom := K, zero := ?_, comm := ?_ }
  · intro a b hab
    apply (cancel_epi (π.f a)).mp
    rw [hK, H.zero a b hab, zero_comp, comp_zero]
  · intro n
    apply (cancel_epi (π.f n)).mp
    have hf' : π.f n ≫ f'.f n = f.f n ≫ ρ.f n := HomologicalComplex.congr_hom hf n
    have hg' : π.f n ≫ g'.f n = g.f n ≫ ρ.f n := HomologicalComplex.congr_hom hg n
    have hd : π.f n ≫ dNext n K = dNext n H.hom ≫ ρ.f n := by
      calc
        _ = dNext n (fun a b => π.f a ≫ K a b) := (dNext_comp_left π K n).symm
        _ = dNext n (fun a b => H.hom a b ≫ ρ.f b) := by simp only [hK]
        _ = _ := dNext_comp_right H.hom ρ n
    have hp : π.f n ≫ prevD n K = prevD n H.hom ≫ ρ.f n := by
      calc
        _ = prevD n (fun a b => π.f a ≫ K a b) := (prevD_comp_left π K n).symm
        _ = prevD n (fun a b => H.hom a b ≫ ρ.f b) := by simp only [hK]
        _ = _ := prevD_comp_right H.hom ρ n
    calc
      _ = f.f n ≫ ρ.f n := hf'
      _ = (dNext n H.hom + prevD n H.hom + g.f n) ≫ ρ.f n := by rw [H.comm n]
      _ = _ := by
        simp only [Preadditive.add_comp, Preadditive.comp_add]
        rw [hd, hp, hg']

end

end OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.QuotientHomotopy.Constructions
