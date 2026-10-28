import OAI.NumberTheory.PadicHodge.IntegralComparison.Cech.StructurePullbackUnit
import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.ArtinianGlobalFunctions

/-! # Iterated Cech Structure Unit -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.IteratedCechStructureUnit

noncomputable section

/-! The actual unit is a basis of degree-zero cohomology also for an
iterated direct image. The construction uses its literal section module,
so no choice of a direct-image composition isomorphism is needed. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

open OAI.NumberTheory.PadicHodge.IntegralComparison.Cech.StructurePullbackUnit

variable {Y X Z S : Scheme.{u}} (f : Y ⟶ X) (i : X ⟶ Z) (π : Z ⟶ S)
  {ι : Type u} [LinearOrder ι] (U : ι → Z.Opens) (hU : iSup U = ⊤)

def sectionMap : ModuleCat.of Γ(S, ⊤) Γ(S, ⊤) ⟶
    (OrderedCech.Augmentation.sections π).obj (Cech.StructurePullbackUnit.coefficients f i) :=
  ModuleCat.ofHom (X := ModuleCat.of Γ(S, ⊤) Γ(S, ⊤))
    (Y := (OrderedCech.Augmentation.sections π).obj (Cech.StructurePullbackUnit.coefficients f i))
    { toFun := fun r => f.appTop (i.appTop (π.appTop r))
      map_add' := by intro r s; simp only [map_add]
      map_smul' := by
        intro r s
        change f.appTop (i.appTop (π.appTop (r * s))) =
          f.appTop (i.appTop (π.appTop r)) * f.appTop (i.appTop (π.appTop s))
        simp only [map_mul] }

theorem sectionMap_one : sectionMap f i π 1 = (1 : Γ(Y, ⊤)) := by
  change f.appTop.hom (i.appTop.hom (π.appTop.hom 1)) = 1
  simp only [map_one]

theorem sectionMap_bijective [IsIso (f ≫ i ≫ π).appTop] :
    Function.Bijective (sectionMap f i π) := by
  have h := ConcreteCategory.bijective_of_isIso (f ≫ i ≫ π).appTop
  rw [Scheme.Hom.comp_appTop, Scheme.Hom.comp_appTop] at h
  exact h

instance sectionMap_isIso [IsIso (f ≫ i ≫ π).appTop] : IsIso (sectionMap f i π) :=
  (ConcreteCategory.isIso_iff_bijective _).mpr (sectionMap_bijective f i π)

def map : ModuleCat.of Γ(S, ⊤) Γ(S, ⊤) ⟶
    (AlgebraicGeometry.SheafCohomology.Projective.OrderedBaseCech.Scheme.Modules.orderedBaseCechComplex π (Cech.StructurePullbackUnit.coefficients f i) U).homology 0 :=
  sectionMap f i π ≫ (Cech.ZeroSections.iso π U hU (Cech.StructurePullbackUnit.coefficients f i)).hom

theorem map_one : map f i π U hU 1 = Cech.StructurePullbackUnit.unit f i π U hU := by
  change (Cech.ZeroSections.iso π U hU (Cech.StructurePullbackUnit.coefficients f i)).hom (sectionMap f i π 1) = _
  rw [sectionMap_one]
  rfl

instance map_isIso [IsIso (f ≫ i ≫ π).appTop] : IsIso (map f i π U hU) := by
  unfold map
  infer_instance

def iso [IsIso (f ≫ i ≫ π).appTop] : ModuleCat.of Γ(S, ⊤) Γ(S, ⊤) ≅
    (AlgebraicGeometry.SheafCohomology.Projective.OrderedBaseCech.Scheme.Modules.orderedBaseCechComplex π (Cech.StructurePullbackUnit.coefficients f i) U).homology 0 :=
  asIso (map f i π U hU)

theorem iso_one [IsIso (f ≫ i ≫ π).appTop] :
    (iso f i π U hU).toLinearEquiv 1 = Cech.StructurePullbackUnit.unit f i π U hU :=
  IteratedCechStructureUnit.map_one f i π U hU

variable {R : Type u} [CommRing R] [IsArtinianRing R] [IsLocalRing R]
  {Y X Z : Scheme.{u}} (f : Y ⟶ X) (i : X ⟶ Z) (π : Z ⟶ Spec (.of R))
  [IsProper (f ≫ i ≫ π)] [Smooth (f ≫ i ≫ π)] [GeometricallyConnected (f ≫ i ≫ π)]
  (s : Spec (.of R) ⟶ Y) (hs : s ≫ (f ≫ i ≫ π) = 𝟙 _)
  {ι : Type u} [LinearOrder ι] (U : ι → Z.Opens) (hU : iSup U = ⊤)

def artinianIso := by
  let : IsIso (f ≫ i ≫ π).appTop :=
    AlgebraicGeometry.AbelianScheme.IsogenyQuotient.ArtinianGlobalFunctions.Construction.artinianLocal_globalFunctions_isIso (f ≫ i ≫ π) s hs
  exact iso f i π U hU

theorem artinianIso_one :
    (artinianIso f i π s hs U hU).toLinearEquiv 1 = Cech.StructurePullbackUnit.unit f i π U hU := by
  let : IsIso (f ≫ i ≫ π).appTop :=
    AlgebraicGeometry.AbelianScheme.IsogenyQuotient.ArtinianGlobalFunctions.Construction.artinianLocal_globalFunctions_isIso (f ≫ i ≫ π) s hs
  exact iso_one f i π U hU

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.IteratedCechStructureUnit
