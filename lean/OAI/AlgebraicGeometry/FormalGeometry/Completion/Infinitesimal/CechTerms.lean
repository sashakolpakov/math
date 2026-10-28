import OAI.AlgebraicGeometry.FormalGeometry.Completion.RelativeCechTerms
import OAI.AlgebraicGeometry.FormalGeometry.Completion.Infinitesimal.ModuleNaturality
import OAI.AlgebraicGeometry.FormalGeometry.Completion.AdicReduction
import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor

/-! # Cech Terms -/

namespace OAI.AlgebraicGeometry.FormalGeometry.Completion.Infinitesimal.CechTerms.Construction

noncomputable section

/-! Every reduced Cech term is identified with the actual term on the infinitesimal neighborhood. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry Opposite
open _root_.AlgebraicGeometry.Scheme.Modules

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

variable {R : Type u} [CommRing R] (I : Ideal R) {X : Scheme.{u}} [X.IsSeparated]
  (f : X ⟶ Spec (CommRingCat.of R))
  {ι : Type u} [LinearOrder ι] [Finite ι] (U : ι → X.Opens)
  (hU : ∀ i, IsAffineOpen (U i))

/-- The actual affine comparison on one intersection factor. -/
def infinitesimalCechFactorIso (n q : ℕ) (a : SheafCohomology.Projective.OrderedBaseCech.Scheme.Modules.OrderedCechIndex ι q) :
    (AdicReduction.Construction.adicReductionFunctor (I ^ (n + 1))).obj (RelativeCechTerms.Construction.relativeCechFactor f U q a) ≅
      RelativeCechTerms.Construction.relativeCechFactor (pullback.fst f (Neighborhoods.Construction.infinitesimalBaseToSpec I n) ≫ f)
        (fun i => pullback.fst f (Neighborhoods.Construction.infinitesimalBaseToSpec I n) ⁻¹ᵁ U i) q a := by
  let g := pullback.fst f (Neighborhoods.Construction.infinitesimalBaseToSpec I n)
  exact (ChartModules.Construction.affineInfinitesimalSectionsModuleEquiv I f n _
    (SheafCohomology.Cech.Cochains.IsAffineOpen.cechIntersection U hU q a.val)).toModuleIso ≪≫
      (RelativeStructureSections.Construction.relativeStructureSections (g ≫ f)).mapIso
        (eqToIso ((SheafCohomology.Cech.SchemeModuleBaseBasic.Scheme.Hom.preimage_cechIntersection g) U q a.val)).symm.op

/-- The term comparison for the actual quotient-power base change. -/
def infinitesimalCechTermIso (n q : ℕ) :
    (AdicReduction.Construction.adicReductionComplex (I ^ (n + 1)) (RelativeCechZeroCycles.Construction.relativeStructureCechComplex f U)).X q ≅
      (RelativeCechZeroCycles.Construction.relativeStructureCechComplex (pullback.fst f (Neighborhoods.Construction.infinitesimalBaseToSpec I n) ≫ f)
        (fun i => pullback.fst f (Neighborhoods.Construction.infinitesimalBaseToSpec I n) ⁻¹ᵁ U i)).X q := by
  have : Finite (SheafCohomology.Projective.OrderedBaseCech.Scheme.Modules.OrderedCechIndex ι q) := inferInstanceAs (Finite {i : Fin (q + 1) → ι // StrictMono i})
  let g := pullback.fst f (Neighborhoods.Construction.infinitesimalBaseToSpec I n)
  exact (AdicReduction.Construction.adicReductionFunctor (I ^ (n + 1))).mapIso (RelativeCechTerms.Construction.relativeStructureCechTermIso f U q) ≪≫
    PreservesProduct.iso (AdicReduction.Construction.adicReductionFunctor (I ^ (n + 1))) (RelativeCechTerms.Construction.relativeCechFactor f U q) ≪≫
      Pi.mapIso (infinitesimalCechFactorIso I f U hU n q) ≪≫
        (RelativeCechTerms.Construction.relativeStructureCechTermIso (g ≫ f) (fun i => g ⁻¹ᵁ U i) q).symm

end

end OAI.AlgebraicGeometry.FormalGeometry.Completion.Infinitesimal.CechTerms.Construction
