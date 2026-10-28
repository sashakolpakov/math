import OAI.NumberTheory.PadicHodge.IntegralComparison.OrderedCech.Functor
import OAI.AlgebraicGeometry.SheafCohomology.Projective.OrderedBaseCechFunctor

/-! # Cech Coordinates -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.IntrinsicOrdered.CechCoordinates.Intrinsic

noncomputable section

/-! The generic ordered tuple complex is the original base-linear
ordered Čech complex, with the identical intersection components. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

universe u
variable {X S : Scheme.{u}} (π : X ⟶ S)
  {ι : Type u} [LinearOrder ι] (U : ι → X.Opens)

open Scheme.Modules

def iso (M : X.Modules) :
    OrderedCech.Projection.complex U (AlgebraicGeometry.SheafCohomology.Cech.SchemeModuleBaseBasic.Scheme.Modules.baseModulePresheaf π M) ≅
      AlgebraicGeometry.SheafCohomology.Projective.OrderedBaseCech.Scheme.Modules.orderedBaseCechComplex π M U :=
  HomologicalComplex.Hom.isoOfComponents (fun _ => Iso.refl _) (by
    intro i j h
    obtain rfl : i + 1 = j := h
    simp only [Iso.refl_hom]
    rfl)

def functorIso : AlgebraicGeometry.SheafCohomology.Cech.SchemeModuleBaseBasic.Scheme.Modules.baseModulePresheafFunctor π ⋙ OrderedCech.Functor.Projection.functor U ≅
    AlgebraicGeometry.SheafCohomology.Projective.OrderedBaseCechFunctor.Scheme.Modules.orderedBaseCechComplexFunctor π U :=
  NatIso.ofComponents (iso π U) (by
    intro M N f
    apply HomologicalComplex.hom_ext
    intro n
    change _ ≫ 𝟙 _ = 𝟙 _ ≫ _
    simp only [Category.comp_id]
    rfl)

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.IntrinsicOrdered.CechCoordinates.Intrinsic
