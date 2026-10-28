import OAI.NumberTheory.PadicHodge.IntegralComparison.FlasqueCechZero
import OAI.NumberTheory.PadicHodge.IntegralComparison.FlasqueCechSubfamily
import OAI.NumberTheory.PadicHodge.IntegralComparison.OrderedCech.Exact
import OAI.NumberTheory.PadicHodge.IntegralComparison.AugmentedOrdered.CechZero
import OAI.NumberTheory.PadicHodge.IntegralComparison.Module.ProductScalarKernel
import Mathlib.Algebra.Homology.ShortComplex.ModuleCat

/-! # Flasque Ordered Rows -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.FlasqueOrderedRows

noncomputable section

/-! The actual augmented ordered rows of a flasque module sheaf are
exact whenever the indexing functor preserves the native nonempty tuple
intersections. Degree one follows from gluing and flasque extension. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.TopologicalSpace Opposite

universe u w
variable (R : Type u) [CommRing R] (X : TopCat.{0})
  {C : Type} [Preorder C] [HasFiniteProducts C] (G : C ⥤ Opens X)
  {ι : Type} [LinearOrder ι] (U : ι → C)
  (F : Sheaf (Opens.grothendieckTopology X) (ModuleCat.{max u w} R))

local notation "P" => G.op ⋙ F.obj
local notation "K" => OAI.NumberTheory.PadicHodge.IntegralComparison.Cech.TupleRestrictionFunctor.complex U P

def augmentation : F.obj.obj (op ⊤) ⟶ (K).X 0 :=
  Pi.lift fun a : Fin 1 → ι =>
    F.obj.map (homOfLE (le_top : G.obj (∏ᶜ (U ∘ a)) ≤ ⊤)).op

omit [LinearOrder ι] in
theorem augmentation_projection (a : Fin 1 → ι) :
    augmentation R X G U F ≫ Cech.TupleRestrictionFunctor.projection U P a =
      F.obj.map (homOfLE (le_top : G.obj (∏ᶜ (U ∘ a)) ≤ ⊤)).op := Pi.lift_comp_π _ a

variable [∀ (n : ℕ) (a : Fin (n + 1) → ι), PreservesLimit (Discrete.functor (U ∘ a)) G]

abbrev comparison := GeometricComparison.NonemptyCech.ProductBaseChange.NonemptyCechProductBaseChange.complexIso G U F.obj

omit [LinearOrder ι] in
theorem comparison_projection (a : Fin 1 → ι) :
    (comparison R X G U F).hom.f 0 ≫
      NonemptyCechDifferential.projection (G.obj ∘ U) F.obj 0 a =
      Cech.TupleRestrictionFunctor.projection U P a ≫
        F.obj.map (PreservesProduct.iso G (U ∘ a)).inv.op := by
  exact Pi.mapIso_hom_π (fun t : Fin 1 → ι =>
    F.obj.mapIso (PreservesProduct.iso G (U ∘ t)).symm.op) a

omit [LinearOrder ι] in
theorem augmentation_comparison (a : Fin 1 → ι) :
    augmentation R X G U F ≫ (comparison R X G U F).hom.f 0 ≫
      NonemptyCechDifferential.projection (G.obj ∘ U) F.obj 0 a =
      F.obj.map (homOfLE (le_top : (∏ᶜ ((G.obj ∘ U) ∘ a)) ≤ ⊤)).op := by
  rw [comparison_projection, ← Category.assoc, augmentation_projection, ← F.obj.map_comp]
  congr 1

omit [LinearOrder ι] in
theorem exists_native [TopCat.Presheaf.IsFlasque (X := X) F.obj]
    (x : (K).X 0) (hx : (K).d 0 1 x = 0) :
    ∃ s : F.obj.obj (op ⊤), augmentation R X G U F s = x := by
  let e := comparison R X G U F
  let y := e.hom.f 0 x
  have hy : ((NonemptyCechNerve.complexFunctor (G.obj ∘ U)).obj F.obj).d 0 1 y = 0 := by
    have h := ConcreteCategory.congr_hom (e.hom.comm 0 1) x
    change ((NonemptyCechNerve.complexFunctor (G.obj ∘ U)).obj F.obj).d 0 1 y =
      e.hom.f 1 ((K).d 0 1 x) at h
    exact h.trans (by rw [hx, map_zero])
  obtain ⟨s, hs⟩ := FlasqueCechZero.exists_global R X F (G.obj ∘ U) y hy
  refine ⟨s, ?_⟩
  apply (ModuleCat.mono_iff_injective (e.hom.f 0)).mp inferInstance
  apply Module.ProductScalarKernel.element_ext
  intro a
  exact (ConcreteCategory.congr_hom (augmentation_comparison R X G U F a) s).trans (hs a)

omit [∀ (n : ℕ) (a : Fin (n + 1) → ι), PreservesLimit (Discrete.functor (U ∘ a)) G] in
theorem first_augmentation :
    F.obj.map (homOfLE (le_top : G.obj (⊤_ C) ≤ ⊤)).op ≫
      (AugmentedOrdered.CechZero.zeroIso U P).inv ≫
        AugmentedOrdered.Cech.differential U P 0 =
      augmentation R X G U F ≫ OrderedCech.Projection.mapF U P 0 := by
  apply Pi.hom_ext
  intro (a : {a : Fin 1 → ι // StrictMono a})
  change _ ≫ OrderedCech.Projection.projection U P 0 a =
    _ ≫ OrderedCech.Projection.projection U P 0 a
  simp only [Category.assoc]
  erw [AugmentedOrdered.CechZero.zeroIso_inv_differential_π,
    OrderedCech.Projection.mapF_projection, augmentation_projection]
  change F.obj.map _ ≫ F.obj.map _ = F.obj.map _
  rw [← F.obj.map_comp]
  congr 1

theorem exactAt_one [TopCat.Presheaf.IsFlasque (X := X) F.obj] :
    (AugmentedOrdered.Cech.complex U P).ExactAt 1 := by
  rw [HomologicalComplex.exactAt_iff' _ 0 1 2 (by simp) (by simp),
    ShortComplex.moduleCat_exact_iff]
  intro x hx
  let y := OrderedCech.Retraction.inclusionF U P 0 x
  have hy : (K).d 0 1 y = 0 := by
    have h := ConcreteCategory.congr_hom (OrderedCech.Retraction.inclusionF_d U P 0) x
    change (K).d 0 1 y = OrderedCech.Retraction.inclusionF U P 1
      (OrderedCech.Projection.differential U P 0 x) at h
    have hz : OrderedCech.Projection.differential U P 0 x = 0 := by
      exact hx
    exact h.trans (by rw [hz, map_zero])
  obtain ⟨s, hs⟩ := exists_native R X G U F y hy
  let t := F.obj.map (homOfLE (le_top : G.obj (⊤_ C) ≤ ⊤)).op s
  refine ⟨(AugmentedOrdered.CechZero.zeroIso U P).inv t, ?_⟩
  have h := ConcreteCategory.congr_hom (first_augmentation R X G U F) s
  change AugmentedOrdered.Cech.differential U P 0 ((AugmentedOrdered.CechZero.zeroIso U P).inv t) =
    OrderedCech.Projection.mapF U P 0 (augmentation R X G U F s) at h
  rw [hs] at h
  exact h.trans (ConcreteCategory.congr_hom (OrderedCech.Retraction.inclusionF_mapF U P 0) x)

theorem exactAt_succ [TopCat.Presheaf.IsFlasque (X := X) F.obj] (n : ℕ) :
    (AugmentedOrdered.Cech.complex U P).ExactAt (n + 1) := by
  cases n with
  | zero => exact exactAt_one R X G U F
  | succ n =>
      apply OrderedCech.Exact.augmented
      exact (FlasqueCechSubfamily.exactAt_succ R X F (G.obj ∘ U) n).of_iso
        (comparison R X G U F).symm

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.FlasqueOrderedRows
