import Mathlib.Algebra.Homology.Homotopy
import Mathlib.Algebra.Category.ModuleCat.EpiMono
import Mathlib.Algebra.Module.Submodule.Equiv

/-! # Injective Homotopy Restriction -/

namespace OAI.AlgebraicGeometry.CycleClass.Geometric.InjectiveHomotopyRestriction.Cycles

noncomputable section

/-!
# Restricting an actual homotopy through an injective chain map

When the components of a given homotopy preserve the image of a degreewise
injective chain map, they have unique restrictions. The homotopy identity for
those restrictions follows by applying the injection. This construction does
not assume a homotopy on the smaller complex.
-/

open _root_.CategoryTheory _root_.CategoryTheory.Limits

universe u v w

variable {R : Type u} [CommRing R] {ι : Type v} {c : ComplexShape ι}
  {C D : HomologicalComplex (ModuleCat.{w} R) c}
  {fD gD : D ⟶ D}

/-- The unique restriction of one actual homotopy component through an
injective chain map whose image it preserves. -/
def restrictedHomotopyComponent (i : C ⟶ D)
    (hi : ∀ n, Function.Injective (i.f n)) (h : Homotopy fD gD)
    (hmem : ∀ a b (x : C.X a), h.hom a b (i.f a x) ∈ LinearMap.range (i.f b).hom)
    (a b : ι) : C.X a ⟶ C.X b :=
  ModuleCat.ofHom (LinearMap.codRestrictOfInjective
    ((h.hom a b).hom.comp (i.f a).hom) (i.f b).hom (hi b) (hmem a b))

/-- Inclusion recovers the given ambient component exactly. -/
@[simp]
theorem restrictedHomotopyComponent_apply (i : C ⟶ D)
    (hi : ∀ n, Function.Injective (i.f n)) (h : Homotopy fD gD)
    (hmem : ∀ a b (x : C.X a), h.hom a b (i.f a x) ∈ LinearMap.range (i.f b).hom)
    (a b : ι) (x : C.X a) :
    i.f b (restrictedHomotopyComponent i hi h hmem a b x) = h.hom a b (i.f a x) := by
  simp [restrictedHomotopyComponent]

/-- Categorical component compatibility for the restriction. -/
@[reassoc]
theorem restrictedHomotopyComponent_comp (i : C ⟶ D)
    (hi : ∀ n, Function.Injective (i.f n)) (h : Homotopy fD gD)
    (hmem : ∀ a b (x : C.X a), h.hom a b (i.f a x) ∈ LinearMap.range (i.f b).hom)
    (a b : ι) :
    restrictedHomotopyComponent i hi h hmem a b ≫ i.f b = i.f a ≫ h.hom a b := by
  apply ModuleCat.hom_ext
  ext x
  exact restrictedHomotopyComponent_apply i hi h hmem a b x

/-- Restrict an existing chain homotopy to a degreewise injective subcomplex.
The two endpoint chain maps must be intertwined by the same inclusion. -/
def restrictHomotopy {fC gC : C ⟶ C} (i : C ⟶ D)
    (hi : ∀ n, Function.Injective (i.f n))
    (hf : i ≫ fD = fC ≫ i) (hg : i ≫ gD = gC ≫ i)
    (h : Homotopy fD gD)
    (hmem : ∀ a b (x : C.X a), h.hom a b (i.f a x) ∈ LinearMap.range (i.f b).hom) :
    Homotopy fC gC := by
  let K := restrictedHomotopyComponent i hi h hmem
  have hK (a b : ι) : K a b ≫ i.f b = i.f a ≫ h.hom a b :=
    restrictedHomotopyComponent_comp i hi h hmem a b
  refine { hom := K, zero := ?_, comm := ?_ }
  · intro a b hab
    let : Mono (i.f b) := (ModuleCat.mono_iff_injective _).2 (hi b)
    apply (cancel_mono (i.f b)).1
    rw [hK, h.zero a b hab, comp_zero, zero_comp]
  · intro n
    let : Mono (i.f n) := (ModuleCat.mono_iff_injective _).2 (hi n)
    apply (cancel_mono (i.f n)).1
    have hf' : i.f n ≫ fD.f n = fC.f n ≫ i.f n :=
      HomologicalComplex.congr_hom hf n
    have hg' : i.f n ≫ gD.f n = gC.f n ≫ i.f n :=
      HomologicalComplex.congr_hom hg n
    have hd : dNext n K ≫ i.f n = i.f n ≫ dNext n h.hom := by
      calc
        dNext n K ≫ i.f n = dNext n (fun a b => K a b ≫ i.f b) :=
          (dNext_comp_right K i n).symm
        _ = dNext n (fun a b => i.f a ≫ h.hom a b) := by simp only [hK]
        _ = i.f n ≫ dNext n h.hom := dNext_comp_left i h.hom n
    have hp : prevD n K ≫ i.f n = i.f n ≫ prevD n h.hom := by
      calc
        prevD n K ≫ i.f n = prevD n (fun a b => K a b ≫ i.f b) :=
          (prevD_comp_right K i n).symm
        _ = prevD n (fun a b => i.f a ≫ h.hom a b) := by simp only [hK]
        _ = i.f n ≫ prevD n h.hom := prevD_comp_left i h.hom n
    calc
      fC.f n ≫ i.f n = i.f n ≫ fD.f n := hf'.symm
      _ = i.f n ≫ (dNext n h.hom + prevD n h.hom + gD.f n) := by rw [h.comm n]
      _ = (dNext n K + prevD n K + gC.f n) ≫ i.f n := by
        simp only [Preadditive.comp_add, Preadditive.add_comp]
        rw [hd, hp, hg']

/-- The resulting homotopy has exactly the constructed restricted components. -/
theorem restrictHomotopy_hom {fC gC : C ⟶ C} (i : C ⟶ D)
    (hi : ∀ n, Function.Injective (i.f n))
    (hf : i ≫ fD = fC ≫ i) (hg : i ≫ gD = gC ≫ i)
    (h : Homotopy fD gD)
    (hmem : ∀ a b (x : C.X a), h.hom a b (i.f a x) ∈ LinearMap.range (i.f b).hom)
    (a b : ι) :
    (restrictHomotopy i hi hf hg h hmem).hom a b =
      restrictedHomotopyComponent i hi h hmem a b := rfl

end

end OAI.AlgebraicGeometry.CycleClass.Geometric.InjectiveHomotopyRestriction.Cycles
