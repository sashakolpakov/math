import Mathlib.Algebra.Category.ModuleCat.Products

/-! # Product Scalar Kernel -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Module.ProductScalarKernel

noncomputable section

/-! Surjectivity and scalar kernel formulas pass to the categorical products of modules. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits

universe u v w

variable {R : Type u} [CommRing R] {ι : Type v}
  (M N : ι → ModuleCat.{max v w} R) [HasProduct M] [HasProduct N]

theorem element_ext (x y : (∏ᶜ M : ModuleCat.{max v w} R)) (h : ∀ i, Pi.π M i x = Pi.π M i y) : x = y := by
  apply (ModuleCat.piIsoPi M).toLinearEquiv.injective
  funext i
  exact (congrArg (fun f => f x) (ModuleCat.piIsoPi_hom_ker_subtype M i)).trans
    ((h i).trans (congrArg (fun f => f y) (ModuleCat.piIsoPi_hom_ker_subtype M i)).symm)

theorem exists_coordinates (x : ∀ i, M i) : ∃ y : (∏ᶜ M : ModuleCat.{max v w} R), ∀ i, Pi.π M i y = x i := by
  refine ⟨(ModuleCat.piIsoPi M).inv x, fun i => ?_⟩
  exact congrArg (fun f => f x) (ModuleCat.piIsoPi_inv_kernel_ι M i)

variable (q : ∀ i, M i ⟶ N i)

theorem surjective (hq : ∀ i, Function.Surjective (q i)) : Function.Surjective (Limits.Pi.map q) := by
  intro y
  choose a ha using fun i => hq i (Pi.π N i y)
  obtain ⟨x, hx⟩ := exists_coordinates M a
  refine ⟨x, element_ext N _ y (fun i => ?_)⟩
  exact (congrArg (fun f => f x) (Pi.map_π q i)).trans
    ((congrArg (q i) (hx i)).trans (ha i))

theorem kernel (r : R) (hk : ∀ i (x : M i), q i x = 0 ↔ r • x = 0) (x : (∏ᶜ M : ModuleCat.{max v w} R)) :
    Limits.Pi.map q x = 0 ↔ r • x = 0 := by
  constructor
  · intro hx
    apply element_ext M
    intro i
    rw [map_smul, map_zero]
    apply (hk i _).mp
    exact (congrArg (fun f => f x) (Pi.map_π q i)).symm.trans
      ((congrArg (Pi.π N i) hx).trans (map_zero (Pi.π N i).hom))
  · intro hx
    apply element_ext N
    intro i
    rw [map_zero]
    refine (congrArg (fun f => f x) (Pi.map_π q i)).trans ((hk i _).mpr ?_)
    exact (map_smul (Pi.π M i).hom r x).symm.trans
      ((congrArg (Pi.π M i) hx).trans (map_zero (Pi.π M i).hom))

theorem scalar_range (r : R) (hk : ∀ i (x : M i), q i x = 0 ↔ ∃ y : M i, r • y = x)
    (x : (∏ᶜ M : ModuleCat.{max v w} R)) : Limits.Pi.map q x = 0 ↔ ∃ y : (∏ᶜ M : ModuleCat.{max v w} R), r • y = x := by
  constructor
  · intro hx
    have hi (i : ι) : ∃ y : M i, r • y = Pi.π M i x := (hk i _).mp
      ((congrArg (fun f => f x) (Pi.map_π q i)).symm.trans
        ((congrArg (Pi.π N i) hx).trans (map_zero (Pi.π N i).hom)))
    choose a ha using hi
    obtain ⟨y, hy⟩ := exists_coordinates M a
    refine ⟨y, element_ext M _ x (fun i => ?_)⟩
    exact (map_smul (Pi.π M i).hom r y).trans ((congrArg (fun z => r • z) (hy i)).trans (ha i))
  · rintro ⟨y, rfl⟩
    apply element_ext N
    intro i
    rw [map_zero]
    refine (congrArg (fun f => f (r • y)) (Pi.map_π q i)).trans ((hk i _).mpr ?_)
    exact ⟨Pi.π M i y, (map_smul (Pi.π M i).hom r y).symm⟩

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Module.ProductScalarKernel
