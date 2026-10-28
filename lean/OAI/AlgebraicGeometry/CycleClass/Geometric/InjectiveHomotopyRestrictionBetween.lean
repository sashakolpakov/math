import Mathlib.Algebra.Homology.Homotopy
import Mathlib.Algebra.Category.ModuleCat.EpiMono
import Mathlib.Algebra.Module.Submodule.Equiv

/-! # Injective Homotopy Restriction Between -/

namespace OAI.AlgebraicGeometry.CycleClass.Geometric.InjectiveHomotopyRestrictionBetween.Cycles

noncomputable section

/-!
# Restricting homotopies between two different subcomplexes

The given ambient homotopy restricts when each component maps the source
subcomplex into the actual image of the target inclusion. This construction
uses the injectivity of that inclusion and proves the homotopy identity there.
-/

open _root_.CategoryTheory _root_.CategoryTheory.Limits

universe u v w

variable {R : Type u} [Ring R] {ι : Type v} {c : ComplexShape ι}
variable {C D C' D' : HomologicalComplex (ModuleCat.{w} R) c}
variable {f g : C ⟶ D}

def restrictedBetweenComponent (i : C' ⟶ C) (j : D' ⟶ D)
    (hj : ∀ n, Function.Injective (j.f n)) (h : Homotopy f g)
    (hmem : ∀ a b (x : C'.X a), h.hom a b (i.f a x) ∈ LinearMap.range (j.f b).hom)
    (a b : ι) : C'.X a ⟶ D'.X b :=
  ModuleCat.ofHom ((LinearEquiv.ofInjective (j.f b).hom (hj b)).symm.toLinearMap.comp
    (((h.hom a b).hom.comp (i.f a).hom).codRestrict (LinearMap.range (j.f b).hom) (hmem a b)))

@[simp]
theorem restrictedBetweenComponent_apply (i : C' ⟶ C) (j : D' ⟶ D)
    (hj : ∀ n, Function.Injective (j.f n)) (h : Homotopy f g)
    (hmem : ∀ a b (x : C'.X a), h.hom a b (i.f a x) ∈ LinearMap.range (j.f b).hom)
    (a b : ι) (x : C'.X a) :
    j.f b (restrictedBetweenComponent i j hj h hmem a b x) = h.hom a b (i.f a x) := by
  simp [restrictedBetweenComponent]

@[reassoc]
theorem restrictedBetweenComponent_comp (i : C' ⟶ C) (j : D' ⟶ D)
    (hj : ∀ n, Function.Injective (j.f n)) (h : Homotopy f g)
    (hmem : ∀ a b (x : C'.X a), h.hom a b (i.f a x) ∈ LinearMap.range (j.f b).hom)
    (a b : ι) :
    restrictedBetweenComponent i j hj h hmem a b ≫ j.f b = i.f a ≫ h.hom a b := by
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  exact restrictedBetweenComponent_apply i j hj h hmem a b x

/-- Restrict a genuine ambient homotopy through an injective target inclusion. -/
def restrictHomotopyBetween {f' g' : C' ⟶ D'} (i : C' ⟶ C) (j : D' ⟶ D)
    (hj : ∀ n, Function.Injective (j.f n))
    (hf : f' ≫ j = i ≫ f) (hg : g' ≫ j = i ≫ g) (h : Homotopy f g)
    (hmem : ∀ a b (x : C'.X a), h.hom a b (i.f a x) ∈ LinearMap.range (j.f b).hom) :
    Homotopy f' g' := by
  let K := restrictedBetweenComponent i j hj h hmem
  have hK (a b : ι) : K a b ≫ j.f b = i.f a ≫ h.hom a b :=
    restrictedBetweenComponent_comp i j hj h hmem a b
  refine { hom := K, zero := ?_, comm := ?_ }
  · intro a b hab
    let : Mono (j.f b) := (ModuleCat.mono_iff_injective _).mpr (hj b)
    apply (cancel_mono (j.f b)).mp
    rw [hK, h.zero a b hab, comp_zero, zero_comp]
  · intro n
    let : Mono (j.f n) := (ModuleCat.mono_iff_injective _).mpr (hj n)
    apply (cancel_mono (j.f n)).mp
    have hf' : f'.f n ≫ j.f n = i.f n ≫ f.f n := HomologicalComplex.congr_hom hf n
    have hg' : g'.f n ≫ j.f n = i.f n ≫ g.f n := HomologicalComplex.congr_hom hg n
    have hd : dNext n K ≫ j.f n = i.f n ≫ dNext n h.hom := by
      calc
        dNext n K ≫ j.f n = dNext n (fun a b => K a b ≫ j.f b) :=
          (dNext_comp_right K j n).symm
        _ = dNext n (fun a b => i.f a ≫ h.hom a b) := by simp only [hK]
        _ = i.f n ≫ dNext n h.hom := dNext_comp_left i h.hom n
    have hp : prevD n K ≫ j.f n = i.f n ≫ prevD n h.hom := by
      calc
        prevD n K ≫ j.f n = prevD n (fun a b => K a b ≫ j.f b) :=
          (prevD_comp_right K j n).symm
        _ = prevD n (fun a b => i.f a ≫ h.hom a b) := by simp only [hK]
        _ = i.f n ≫ prevD n h.hom := prevD_comp_left i h.hom n
    calc
      f'.f n ≫ j.f n = i.f n ≫ f.f n := hf'
      _ = i.f n ≫ (dNext n h.hom + prevD n h.hom + g.f n) := by rw [h.comm n]
      _ = (dNext n K + prevD n K + g'.f n) ≫ j.f n := by
        simp only [Preadditive.comp_add, Preadditive.add_comp]
        rw [hd, hp, hg']

end

end OAI.AlgebraicGeometry.CycleClass.Geometric.InjectiveHomotopyRestrictionBetween.Cycles
