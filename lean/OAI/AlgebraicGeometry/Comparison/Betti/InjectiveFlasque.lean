import OAI.AlgebraicGeometry.Comparison.Betti.FlasqueBiproduct
import Mathlib

/-! # Injective Flasque -/

namespace OAI.AlgebraicGeometry.Comparison.Betti.InjectiveFlasque

noncomputable section

/-!
# Injective complex sheaves are flasque

The free complex sheaf represented by an open set represents its actual
section module. Inclusions of opens induce monomorphisms of these free
sheaves, so injectivity gives extensions of sections. This is the complex
coefficient version of the argument in `Affine/AffineVanishing`.
-/

open _root_.CategoryTheory _root_.CategoryTheory.Limits Opposite _root_.TopologicalSpace

attribute [local instance] AlgebraicTopology.Cohomology.Singular.StalkExactnessAt.stalkModulesForget₂PreservesFilteredColimits
  AlgebraicTopology.Cohomology.Singular.StalkExactnessAt.stalkModulesForgetPreservesFilteredColimits

local instance complexModuleLimits : HasLimitsOfSize.{0, 0} (ModuleCat.{0} ℂ) :=
  ModuleCat.hasLimitsOfSize.{0, 0, 0, 0}

instance freeComplexPreservesMonomorphisms : (ModuleCat.free ℂ).PreservesMonomorphisms where
  preserves f hf := by
    apply (ModuleCat.mono_iff_injective _).mpr
    exact Finsupp.mapDomain_injective ((CategoryTheory.mono_iff_injective f).mp hf)

variable {X : TopCat.{0}}

def freeComplexRepresentable (U : Opens X) : FlasqueBiproduct.ComplexSheaves X :=
  (presheafToSheaf (Opens.grothendieckTopology X) (ModuleCat.{0} ℂ)).obj
    (yoneda.obj U ⋙ ModuleCat.free ℂ)

def freeComplexRepresentableMap {U V : Opens X} (i : U ⟶ V) :
    freeComplexRepresentable U ⟶ freeComplexRepresentable V :=
  (presheafToSheaf (Opens.grothendieckTopology X) (ModuleCat.{0} ℂ)).map
    (Functor.whiskerRight (yoneda.map i) (ModuleCat.free ℂ))

def freeComplexRepresentableHomEquiv {U : Opens X} {F : FlasqueBiproduct.ComplexSheaves X} :
    (freeComplexRepresentable U ⟶ F) ≃ F.obj.obj (op U) :=
  ((sheafificationAdjunction (Opens.grothendieckTopology X) (ModuleCat.{0} ℂ)).homEquiv _ _).trans
    (((ModuleCat.adj ℂ).whiskerRight (Opens X)ᵒᵖ).homEquiv _ _ |>.trans yonedaEquiv)

theorem freeComplexRepresentableMap_mono {U V : Opens X} (i : U ⟶ V) :
    Mono (freeComplexRepresentableMap i) := by
  let S := presheafToSheaf (Opens.grothendieckTopology X) (ModuleCat.{0} ℂ)
  have : PreservesFiniteLimits S := inferInstance
  have : S.PreservesMonomorphisms := inferInstance
  exact Functor.map_mono S (Functor.whiskerRight (yoneda.map i) (ModuleCat.free ℂ))

theorem freeComplexRepresentableHomEquiv_map {U V : Opens X} (i : U ⟶ V)
    {F : FlasqueBiproduct.ComplexSheaves X} (f : freeComplexRepresentable V ⟶ F) :
    freeComplexRepresentableHomEquiv (freeComplexRepresentableMap i ≫ f) =
      F.obj.map i.op (freeComplexRepresentableHomEquiv f) := by
  let a₁ := sheafificationAdjunction (Opens.grothendieckTopology X) (ModuleCat.{0} ℂ)
  let a₂ := (ModuleCat.adj ℂ).whiskerRight (Opens X)ᵒᵖ
  let α := Functor.whiskerRight (yoneda.map i) (ModuleCat.free ℂ)
  have h₁ := a₁.homEquiv_naturality_left α f
  have h₂ := a₂.homEquiv_naturality_left (yoneda.map i) (a₁.homEquiv _ _ f)
  change yonedaEquiv (a₂.homEquiv _ _ (a₁.homEquiv _ _
      ((presheafToSheaf (Opens.grothendieckTopology X) (ModuleCat.{0} ℂ)).map α ≫ f))) = _
  erw [h₁, h₂]
  exact (yonedaEquiv_naturality _ _).symm

/-- Injectivity extends every actual section along every inclusion of opens. -/
theorem injective_flasque (F : FlasqueBiproduct.ComplexSheaves X) [Injective F] : TopCat.Sheaf.IsFlasque F := by
  constructor
  intro U V i
  apply (ModuleCat.epi_iff_surjective _).mpr
  intro s
  let g : freeComplexRepresentable V.unop ⟶ F := freeComplexRepresentableHomEquiv.symm s
  let m : freeComplexRepresentable V.unop ⟶ freeComplexRepresentable U.unop :=
    freeComplexRepresentableMap i.unop
  have : Mono m := freeComplexRepresentableMap_mono i.unop
  let h : freeComplexRepresentable U.unop ⟶ F := Injective.factorThru g m
  refine ⟨freeComplexRepresentableHomEquiv h, ?_⟩
  have hnat : F.obj.map i (freeComplexRepresentableHomEquiv h) =
      freeComplexRepresentableHomEquiv (m ≫ h) := by
    exact (freeComplexRepresentableHomEquiv_map i.unop h).symm
  rw [hnat, Injective.comp_factorThru]
  exact Equiv.apply_symm_apply _ _

end

end OAI.AlgebraicGeometry.Comparison.Betti.InjectiveFlasque
