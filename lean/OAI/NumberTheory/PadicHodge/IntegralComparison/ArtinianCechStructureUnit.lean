import OAI.NumberTheory.PadicHodge.IntegralComparison.Cech.StructureUnit
import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.ArtinianGlobalFunctions

/-! # Artinian Cech Structure Unit -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.ArtinianCechStructureUnit

noncomputable section

/-! The actual Čech unit is a basis of degree-zero structure-sheaf
cohomology for a pointed proper smooth geometrically connected family
over an Artinian local ring. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

variable {R : Type u} [CommRing R] [IsArtinianRing R] [IsLocalRing R]
  {X Y : Scheme.{u}} (f : X ⟶ Y) (π : Y ⟶ Spec (.of R))
  [IsProper (f ≫ π)] [Smooth (f ≫ π)] [GeometricallyConnected (f ≫ π)]
  (s : Spec (.of R) ⟶ X) (hs : s ≫ (f ≫ π) = 𝟙 _)
  {ι : Type u} [LinearOrder ι] (U : ι → Y.Opens) (hU : iSup U = ⊤)

def iso : ModuleCat.of Γ(Spec (.of R), ⊤) Γ(Spec (.of R), ⊤) ≅
    Cech.StructureUnit.cohomology f π U := by
  letI : IsIso (f ≫ π).appTop :=
    AlgebraicGeometry.AbelianScheme.IsogenyQuotient.ArtinianGlobalFunctions.Construction.artinianLocal_globalFunctions_isIso (f ≫ π) s hs
  exact Cech.StructureUnit.iso f π U hU

@[simp]
theorem iso_one : (iso f π s hs U hU).toLinearEquiv 1 = Cech.StructureUnit.unit f π U hU := by
  let : IsIso (f ≫ π).appTop :=
    AlgebraicGeometry.AbelianScheme.IsogenyQuotient.ArtinianGlobalFunctions.Construction.artinianLocal_globalFunctions_isIso (f ≫ π) s hs
  exact Cech.StructureUnit.iso_one f π U hU

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.ArtinianCechStructureUnit
