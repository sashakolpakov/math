import Mathlib.Algebra.Category.ModuleCat.Sheaf.Quasicoherent

/-! # Presentations -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Finite.Presentations

noncomputable section

/-!
Finite presentations of the structure module and their transport. These give
the local algebra needed to apply the affine quasi-coherent sheaf API to the
line bundles used in HilbertConstruction.
-/

open _root_.CategoryTheory Limits

universe u v v' w w'

section Presentation

variable {C : Type w} [Category.{v} C] {J : GrothendieckTopology C}
  (R : Sheaf J RingCat.{u}) [HasSheafify J AddCommGrpCat.{u}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{u}]

/-- The structure module is the free module on one generator. -/
def freeSingletonUnitIso : SheafOfModules.free (R := R) PUnit.{u + 1} ≅
    SheafOfModules.unit R :=
  coproductUniqueIso (fun _ : PUnit.{u + 1} => SheafOfModules.unit R)

/-- An explicit presentation with one generator and no relations. -/
def unitFinitePresentation : (SheafOfModules.unit R).Presentation :=
  SheafOfModules.presentationOfIsCokernelFree
    (0 : SheafOfModules.free (R := R) PEmpty.{u + 1} ⟶
      SheafOfModules.free (R := R) PUnit.{u + 1})
    (freeSingletonUnitIso R).hom zero_comp <|
    CokernelCofork.IsColimit.ofπ _ zero_comp
      (fun g _ => (freeSingletonUnitIso R).inv ≫ g)
      (fun g _ => by simp)
      (fun g _ m hm => by rw [← hm]; simp)

instance unitFinitePresentation_isFinite : (unitFinitePresentation R).IsFinite where
  isFiniteType_generators := ⟨inferInstanceAs (Finite PUnit.{u + 1})⟩
  isFiniteType_relations := ⟨inferInstanceAs (Finite PEmpty.{u + 1})⟩

variable {D : Type w'} [Category.{v'} D] {K : GrothendieckTopology D}
  {S : Sheaf K RingCat.{u}} [HasSheafify K AddCommGrpCat.{u}]
  [K.WEqualsLocallyBijective AddCommGrpCat.{u}]

/-- Colimit-preserving transport with a structure-module comparison preserves
the finiteness of both the generator and relation families. -/
theorem finitePresentation_map {M : SheafOfModules.{u} R}
    (P : M.Presentation) [P.IsFinite]
    (F : SheafOfModules.{u} R ⥤ SheafOfModules.{u} S)
    [PreservesColimitsOfSize.{u, u} F]
    (e : SheafOfModules.unit S ≅ F.obj (SheafOfModules.unit R)) :
    (P.map F e).IsFinite where
  isFiniteType_generators := ⟨by
    rw [SheafOfModules.Presentation.map_generators_I]
    exact SheafOfModules.GeneratingSections.IsFiniteType.finite⟩
  isFiniteType_relations := ⟨by
    rw [SheafOfModules.Presentation.map_relations_I]
    exact SheafOfModules.GeneratingSections.IsFiniteType.finite⟩

end Presentation

variable {C : Type w} [Category.{v} C] [HasBinaryProducts C]
  {J : GrothendieckTopology C} {R : Sheaf J RingCat.{u}}
  [HasSheafify J AddCommGrpCat.{u}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [∀ X, HasSheafify (J.over X) AddCommGrpCat.{u}]
  [∀ X, (J.over X).WEqualsLocallyBijective AddCommGrpCat.{u}]

/-- A finite global presentation is also a finite local presentation. -/
theorem finitePresentation_quasicoherentData {M : SheafOfModules.{u} R}
    (P : M.Presentation) [P.IsFinite] : P.quasicoherentData.IsFinitePresentation where
  isFinite_presentation X := by
    constructor
    · constructor
      change Finite P.generators.I
      exact SheafOfModules.GeneratingSections.IsFiniteType.finite
    · constructor
      change Finite P.relations.I
      exact SheafOfModules.GeneratingSections.IsFiniteType.finite

/-- Global finite presentations imply the usual sheaf-theoretic property. -/
theorem isFinitePresentation_of_presentation {M : SheafOfModules.{u} R}
    (P : M.Presentation) [P.IsFinite] : M.IsFinitePresentation :=
  ⟨P.quasicoherentData, finitePresentation_quasicoherentData P⟩

theorem unit_isFinitePresentation : (SheafOfModules.unit R).IsFinitePresentation :=
  isFinitePresentation_of_presentation (unitFinitePresentation R)

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Finite.Presentations
