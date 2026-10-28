import Mathlib.CategoryTheory.Generator.Sheaf
import Mathlib.Topology.Sheaves.Flasque
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Zariski.Cohomology

/-! # Injective Sheaf Flasqueness -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.InjectiveSheafFlasqueness.ZariskiCohomology.FlasqueAcyclicity

noncomputable section

universe u
open _root_.CategoryTheory Limits Opposite _root_.TopologicalSpace _root_.AlgebraicGeometry

abbrev AbSheaf (X : TopCat.{u}) :=
  CategoryTheory.Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}

noncomputable abbrev freeAbelianRepresentable
    {X : TopCat.{u}} (U : Opens X) : AbSheaf X :=
  (presheafToSheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}).obj
    (yoneda.obj U ⋙ AddCommGrpCat.free)

noncomputable def freeAbelianRepresentableMap
    {X : TopCat.{u}} {U V : Opens X} (i : U ⟶ V) :
    freeAbelianRepresentable U ⟶ freeAbelianRepresentable V :=
  (presheafToSheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}).map
    (Functor.whiskerRight (yoneda.map i) AddCommGrpCat.free)

noncomputable def freeAbelianRepresentableHomEquiv
    {X : TopCat.{u}} {U : Opens X} {F : AbSheaf X} :
    (freeAbelianRepresentable U ⟶ F) ≃ F.obj.obj (op U) :=
  ((sheafificationAdjunction
      (Opens.grothendieckTopology X) AddCommGrpCat.{u}).homEquiv _ _).trans <|
    ((AddCommGrpCat.adj.whiskerRight (Opens X)ᵒᵖ).homEquiv _ _).trans
      yonedaEquiv

theorem freeAbelianRepresentableMap_mono
    {X : TopCat.{u}} {U V : Opens X} (i : U ⟶ V) :
    Mono (freeAbelianRepresentableMap i) := by
  dsimp [freeAbelianRepresentableMap]
  apply Functor.map_mono

theorem freeAbelianRepresentableHomEquiv_map
    {X : TopCat.{u}} {U V : Opens X} (i : U ⟶ V)
    {F : AbSheaf X} (f : freeAbelianRepresentable V ⟶ F) :
    freeAbelianRepresentableHomEquiv
        (freeAbelianRepresentableMap i ≫ f) =
      F.obj.map i.op (freeAbelianRepresentableHomEquiv f) := by
  let a₁ := sheafificationAdjunction
    (Opens.grothendieckTopology X) AddCommGrpCat.{u}
  let a₂ := AddCommGrpCat.adj.whiskerRight (Opens X)ᵒᵖ
  let α := Functor.whiskerRight (yoneda.map i) AddCommGrpCat.free
  have h₁ := a₁.homEquiv_naturality_left α f
  have h₂ := a₂.homEquiv_naturality_left (yoneda.map i)
    (a₁.homEquiv _ _ f)
  dsimp [freeAbelianRepresentableHomEquiv,
    freeAbelianRepresentableMap, freeAbelianRepresentable, a₁, a₂, α] at h₁ h₂ ⊢
  rw [h₁, h₂]
  exact (yonedaEquiv_naturality _ _).symm

/-- An injective abelian sheaf is flasque. This is the section-extension
property needed after restricting an injective resolution to an open set. -/
theorem injectiveSheaf_isFlasque
    {X : TopCat.{u}} (F : AbSheaf X) [Injective F] :
    TopCat.Sheaf.IsFlasque F := by
  constructor
  intro U V i
  rw [AddCommGrpCat.epi_iff_surjective]
  intro s
  let g : freeAbelianRepresentable V.unop ⟶ F :=
    freeAbelianRepresentableHomEquiv.symm s
  let m : freeAbelianRepresentable V.unop ⟶
      freeAbelianRepresentable U.unop :=
    freeAbelianRepresentableMap i.unop
  let : Mono m := freeAbelianRepresentableMap_mono i.unop
  let h : freeAbelianRepresentable U.unop ⟶ F :=
    Injective.factorThru g m
  refine ⟨freeAbelianRepresentableHomEquiv h, ?_⟩
  have hnat : F.obj.map i (freeAbelianRepresentableHomEquiv h) =
      freeAbelianRepresentableHomEquiv (m ≫ h) := by
    simpa only [m, Quiver.Hom.op_unop, Opposite.op_unop] using
      (freeAbelianRepresentableHomEquiv_map i.unop h).symm
  rw [hnat, Injective.comp_factorThru]
  exact Equiv.apply_symm_apply _ _

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.InjectiveSheafFlasqueness.ZariskiCohomology.FlasqueAcyclicity
