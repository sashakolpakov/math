import OAI.NumberTheory.PadicHodge.IntegralComparison.Acyclic.SectionTransportFactor
import OAI.NumberTheory.PadicHodge.IntegralComparison.Sheaf.ExtRestrictionCoordinates

/-! # Ext Transport Coordinates -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Sheaf.ExtTransportCoordinates

noncomputable section

/-! Exact transport through a sheaf-complex map retains the original presheaf-section coordinates. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits

private theorem combine {Z : Type*} [Category* Z] {A B C A' B' C' : Z}
    (r : A ⟶ B) (s : B ⟶ C) (eA : A ⟶ A') (eB : B ⟶ B') (eC : C ⟶ C')
    (q : A' ⟶ B') (v : B' ⟶ C')
    (hr : r ≫ eB = eA ≫ q) (hs : s ≫ eC = eB ≫ v) :
    (r ≫ s) ≫ eC = eA ≫ q ≫ v := by
  rw [Category.assoc, hs, ← Category.assoc r, hr, Category.assoc]

universe u v z

variable {C D : Type u} [Category.{v} C] [Category.{v} D]
  (F : C ⥤ D) (R : Type u) [CommRing R]
  (J : GrothendieckTopology C) (K : GrothendieckTopology D)
  [F.IsContinuous J K] [F.IsCocontinuous J K]
  [HasSheafify J (ModuleCat.{u} R)] [HasSheafify K (ModuleCat.{u} R)]
  [∀ P : Cᵒᵖ ⥤ ModuleCat.{u} R, F.op.HasPointwiseRightKanExtension P]
  [HasExt.{max u z} (Sheaf J (ModuleCat.{u} R))]
  [HasExt.{max u z} (Sheaf K (ModuleCat.{u} R))]
  [(F.sheafPushforwardContinuous (ModuleCat.{u} R) J K).Linear R]
  [PreservesFiniteLimits (F.sheafPushforwardContinuous (ModuleCat.{u} R) J K)]
  [PreservesFiniteColimits (F.sheafPushforwardContinuous (ModuleCat.{u} R) J K)]

local notation "T" => OAI.NumberTheory.PadicHodge.IntegralComparison.Sheaf.ExtRestrictionCoordinates.restriction F R J K
local notation "A" => OAI.NumberTheory.PadicHodge.IntegralComparison.Ext.ZeroPresheafSections.constantUnit R K
local notation "e" => OAI.NumberTheory.PadicHodge.IntegralComparison.ConstantSection.SectionRestriction.constantIso F R J K (ModuleCat.of R R)

variable (N : CochainComplex (Sheaf K (ModuleCat.{u} R)) ℕ)
  (L : CochainComplex (Sheaf J (ModuleCat.{u} R)) ℕ)
  (b : ((F.sheafPushforwardContinuous (ModuleCat.{u} R) J K).mapHomologicalComplex (.up ℕ)).obj N ⟶ L)

def presheafMap : PresheafSectionComplex.complex.{u, v, u, z} R K N ⟶
    PresheafSectionComplex.complex.{u, v, u, z} R J L :=
  PresheafSectionRestriction.complexMap F R J K N ≫
    ((PresheafSectionComplex.sectionFunctor R J).mapHomologicalComplex (.up ℕ)).map b

def leftMap : Acyclic.Resolution.Comparison.complex R A N ⟶
    PresheafSectionComplex.complex.{u, v, u, z} R J L :=
  AlgebraicGeometry.Crystalline.Cohomology.Acyclic.TransportNaturality.AcyclicTransportNaturality.sectionMap R T A (e).inv b ≫
    (PresheafSectionComplex.complexIso R J L).hom

def rightMap : Acyclic.Resolution.Comparison.complex R A N ⟶
    PresheafSectionComplex.complex.{u, v, u, z} R J L :=
  (PresheafSectionComplex.complexIso R K N).hom ≫ presheafMap F R J K N L b

private def middleMap : Acyclic.Resolution.Comparison.complex R A N ⟶
    PresheafSectionComplex.complex.{u, v, u, z} R J L :=
  Acyclic.SectionTransportFactor.factor R T A (e).inv b ≫
    (PresheafSectionComplex.complexIso R J L).hom

private theorem first : leftMap F R J K N L b = middleMap F R J K N L b :=
  congrArg (fun a => a ≫ (PresheafSectionComplex.complexIso R J L).hom)
    (Acyclic.SectionTransportFactor.eq_factor R T A (e).inv b)

private theorem last_component (i : ℕ) :
    (middleMap F R J K N L b).f i = (rightMap F R J K N L b).f i :=
  combine (Ext.ExtPullbackComparison.component T R A (e).inv 0 (N.X i))
    ((Ext.ModuleFunctor.functor R (Ext.ZeroPresheafSections.constantUnit R J) 0).map (b.f i))
    _ _ _ _ _ (ExtRestrictionCoordinates.component F R J K (N.X i))
    ((Ext.ZeroPresheafSections.iso.{u, v, u, z} R J).hom.naturality (b.f i))

private theorem last : middleMap F R J K N L b = rightMap F R J K N L b := by
  apply HomologicalComplex.Hom.ext
  funext i
  exact last_component F R J K N L b i

theorem complexes : leftMap F R J K N L b = rightMap F R J K N L b :=
  (first F R J K N L b).trans (last F R J K N L b)

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Sheaf.ExtTransportCoordinates
