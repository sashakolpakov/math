import OAI.NumberTheory.PadicHodge.IntegralComparison.Presentation.TupleProducts
import OAI.NumberTheory.PadicHodge.IntegralComparison.Free.PresentationSheafSections
import OAI.NumberTheory.PadicHodge.IntegralComparison.CoveringPresentationResolution

/-! # Resolution Terms -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Presentation.ResolutionTerms

noncomputable section

/-! Each actual presentation-resolution term is a free presentation sheaf on the frame products. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits

universe u v

variable {C : Type (max u v)} [Category.{v} C] [HasBinaryProducts C]
  {ι : Type v} (F : ι → C) (R : Type (max u v)) [CommRing R] (n : ℕ)

def presheafIso :
    (AlgebraicGeometry.Crystalline.Cohomology.Cech.PresentationResolution.CechPresentationResolution.complex R
      (CoveringPresentationPresheaf.presentations F)).X n ≅
        Free.PresentationSections.presheaf (TupleProducts.family F n) R :=
  Functor.isoWhiskerRight (TupleProducts.presheafIso F n) (ModuleCat.free R)

def sheafIso (J : GrothendieckTopology C) :
    (CoveringPresentationResolution.complex J R F).X n ≅
      Free.PresentationSheafSections.sheaf (TupleProducts.family F n) R J :=
  (presheafToSheaf J (ModuleCat.{max u v} R)).mapIso (presheafIso F R n)

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Presentation.ResolutionTerms
