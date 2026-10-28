import OAI.NumberTheory.PadicHodge.IntegralComparison.Frobenius.PresheafRestriction
import OAI.NumberTheory.PadicHodge.IntegralComparison.Open.SectionAlgebraIso
import OAI.NumberTheory.PadicHodge.IntegralComparison.Module.SheafificationRestriction
import OAI.NumberTheory.PadicHodge.IntegralComparison.Frobenius.DeRhamGlobal
import OAI.NumberTheory.PadicHodge.IntegralComparison.SchemeModuleSheafification

/-! # Sheaf Open Restriction -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Frobenius.SheafOpenRestriction

noncomputable section

/-!
# IntegralComparison: the original Frobenius de Rham module terms commute with open restriction
-/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

variable (k : Type u) [Field k] [Fintype k] (X Y : Over (Spec (CommRingCat.of k)))
  (g : X.left ⟶ Y.left) [IsOpenImmersion g] (hg : g ≫ Y.hom = X.hom)

def ringMap : X.left.ringCatSheaf ⟶
    (g.opensFunctor.sheafPushforwardContinuous RingCat (Opens.grothendieckTopology X.left)
      (Opens.grothendieckTopology Y.left)).obj Y.left.ringCatSheaf :=
  ⟨PresheafRestriction.ringMap g.opensFunctor
    (AlgebraicGeometry.Crystalline.Cohomology.AlgebraicForms.AlgebraicDeRham.sectionAlgebras k Y) (AlgebraicGeometry.Crystalline.Cohomology.AlgebraicForms.AlgebraicDeRham.sectionAlgebras k X)
    (Open.SectionAlgebraIso.iso k X Y g hg)⟩

def presheafIso (n : ℕ) :
    (DeRhamGlobal.presheafComplex k X).X n ≅
      (PresheafOfModules.pushforward (ringMap k X Y g hg).hom).obj
        ((DeRhamGlobal.presheafComplex k Y).X n) :=
  PresheafRestriction.formsIso g.opensFunctor
    (AlgebraicGeometry.Crystalline.Cohomology.AlgebraicForms.AlgebraicDeRham.sectionAlgebras k Y) (AlgebraicGeometry.Crystalline.Cohomology.AlgebraicForms.AlgebraicDeRham.sectionAlgebras k X)
    (Open.SectionAlgebraIso.iso k X Y g hg) n

def iso (n : ℕ) : (DeRhamGlobal.complex k X).X n ≅
    (Scheme.Modules.restrictFunctor g).obj ((DeRhamGlobal.complex k Y).X n) :=
  (SchemeModuleSheafification.functor X.left).mapIso (presheafIso k X Y g hg n) ≪≫
    Module.SheafificationRestriction.iso (ringMap k X Y g hg)
      ((DeRhamGlobal.presheafComplex k Y).X n)

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Frobenius.SheafOpenRestriction
