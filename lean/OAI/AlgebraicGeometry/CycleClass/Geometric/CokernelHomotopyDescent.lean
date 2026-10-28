import Mathlib.Algebra.Homology.HomologicalComplexAbelian
import Mathlib.Algebra.Homology.Homotopy

/-! # Cokernel Homotopy Descent -/

namespace OAI.AlgebraicGeometry.CycleClass.Geometric.CokernelHomotopyDescent.Cycles

noncomputable section

/-!
# Descending actual homotopies through quotient complexes

For a short exact sequence of complexes, every ambient homotopy component
annihilating the subcomplex after projection has a unique quotient component.
The homotopy identity descends by the epimorphism from the ambient complex.
-/

open _root_.CategoryTheory _root_.CategoryTheory.Limits

universe u v w

variable {V : Type u} [Category.{v} V] [Abelian V]
  {ι : Type w} {c : ComplexShape ι}
  (S T : ShortComplex (HomologicalComplex V c))
  (hS : S.ShortExact) {f g : S.X₂ ⟶ T.X₂}

/-- The uniquely descended component of an actual ambient homotopy. -/
def quotientHomotopyComponent (h : Homotopy f g)
    (hz : ∀ a b, S.f.f a ≫ h.hom a b ≫ T.g.f b = 0) (a b : ι) :
    S.X₃.X a ⟶ T.X₃.X b :=
  (CokernelCofork.IsColimit.desc'
    ((HomologicalComplex.shortExact_iff_degreewise_shortExact S).1 hS a).gIsCokernel
    (h.hom a b ≫ T.g.f b) (hz a b)).val

/-- Projection identifies the descended component with the ambient one. -/
@[reassoc]
theorem quotientHomotopyComponent_projection (h : Homotopy f g)
    (hz : ∀ a b, S.f.f a ≫ h.hom a b ≫ T.g.f b = 0) (a b : ι) :
    S.g.f a ≫ quotientHomotopyComponent S T hS h hz a b =
      h.hom a b ≫ T.g.f b :=
  (CokernelCofork.IsColimit.desc'
    ((HomologicalComplex.shortExact_iff_degreewise_shortExact S).1 hS a).gIsCokernel
    (h.hom a b ≫ T.g.f b) (hz a b)).property

/-- Descend an actual chain homotopy to quotient complexes, with proved
endpoint compatibility and vanishing on the source subcomplex. -/
def descendHomotopy {fQ gQ : S.X₃ ⟶ T.X₃}
    (hf : S.g ≫ fQ = f ≫ T.g) (hg : S.g ≫ gQ = g ≫ T.g)
    (h : Homotopy f g)
    (hz : ∀ a b, S.f.f a ≫ h.hom a b ≫ T.g.f b = 0) : Homotopy fQ gQ := by
  let K := quotientHomotopyComponent S T hS h hz
  have hK (a b : ι) : S.g.f a ≫ K a b = h.hom a b ≫ T.g.f b :=
    quotientHomotopyComponent_projection S T hS h hz a b
  refine { hom := K, zero := ?_, comm := ?_ }
  · intro a b hab
    let : Epi (S.g.f a) :=
      ((HomologicalComplex.shortExact_iff_degreewise_shortExact S).1 hS a).epi_g
    apply (cancel_epi (S.g.f a)).1
    rw [hK, h.zero a b hab, zero_comp, comp_zero]
  · intro n
    let : Epi (S.g.f n) :=
      ((HomologicalComplex.shortExact_iff_degreewise_shortExact S).1 hS n).epi_g
    apply (cancel_epi (S.g.f n)).1
    have hf' : S.g.f n ≫ fQ.f n = f.f n ≫ T.g.f n :=
      HomologicalComplex.congr_hom hf n
    have hg' : S.g.f n ≫ gQ.f n = g.f n ≫ T.g.f n :=
      HomologicalComplex.congr_hom hg n
    have hd : S.g.f n ≫ dNext n K = dNext n h.hom ≫ T.g.f n := by
      calc
        S.g.f n ≫ dNext n K = dNext n (fun a b => S.g.f a ≫ K a b) :=
          (dNext_comp_left S.g K n).symm
        _ = dNext n (fun a b => h.hom a b ≫ T.g.f b) := by simp only [hK]
        _ = dNext n h.hom ≫ T.g.f n := dNext_comp_right h.hom T.g n
    have hp : S.g.f n ≫ prevD n K = prevD n h.hom ≫ T.g.f n := by
      calc
        S.g.f n ≫ prevD n K = prevD n (fun a b => S.g.f a ≫ K a b) :=
          (prevD_comp_left S.g K n).symm
        _ = prevD n (fun a b => h.hom a b ≫ T.g.f b) := by simp only [hK]
        _ = prevD n h.hom ≫ T.g.f n := prevD_comp_right h.hom T.g n
    calc
      S.g.f n ≫ fQ.f n = f.f n ≫ T.g.f n := hf'
      _ = (dNext n h.hom + prevD n h.hom + g.f n) ≫ T.g.f n := by rw [h.comm n]
      _ = S.g.f n ≫ (dNext n K + prevD n K + gQ.f n) := by
        simp only [Preadditive.add_comp, Preadditive.comp_add]
        rw [hd, hp, hg']

/-- The descended homotopy uses the actual quotient components above. -/
theorem descendHomotopy_hom {fQ gQ : S.X₃ ⟶ T.X₃}
    (hf : S.g ≫ fQ = f ≫ T.g) (hg : S.g ≫ gQ = g ≫ T.g)
    (h : Homotopy f g)
    (hz : ∀ a b, S.f.f a ≫ h.hom a b ≫ T.g.f b = 0) (a b : ι) :
    (descendHomotopy S T hS hf hg h hz).hom a b =
      quotientHomotopyComponent S T hS h hz a b := rfl

/-- Projection compatibility for the fully assembled homotopy. -/
@[reassoc]
theorem descendHomotopy_projection {fQ gQ : S.X₃ ⟶ T.X₃}
    (hf : S.g ≫ fQ = f ≫ T.g) (hg : S.g ≫ gQ = g ≫ T.g)
    (h : Homotopy f g)
    (hz : ∀ a b, S.f.f a ≫ h.hom a b ≫ T.g.f b = 0) (a b : ι) :
    S.g.f a ≫ (descendHomotopy S T hS hf hg h hz).hom a b =
      h.hom a b ≫ T.g.f b :=
  quotientHomotopyComponent_projection S T hS h hz a b

end

end OAI.AlgebraicGeometry.CycleClass.Geometric.CokernelHomotopyDescent.Cycles
