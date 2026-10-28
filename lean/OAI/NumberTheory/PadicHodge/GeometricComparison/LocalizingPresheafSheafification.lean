import OAI.NumberTheory.PadicHodge.GeometricComparison.LocalizingPresheafSheaf
import OAI.NumberTheory.PadicHodge.GeometricComparison.BasisSheafificationComposition
import Mathlib.CategoryTheory.Sites.Abelian
import OAI.AlgebraicGeometry.Crystalline.Cohomology.MixedCech.Presheaf

/-! # Localizing Presheaf Sheafification -/

namespace OAI.NumberTheory.PadicHodge.GeometricComparison.LocalizingPresheafSheafification.LocalizingPresheafBasis

noncomputable section

/-! Sheafifying a localizing affine presheaf gives the actual associated module sheaf, also after a sheaf-preserving coefficient change. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u v w

variable (A : CommRingCat.{u})
  (P : (Spec A).Opensᵒᵖ ⥤ ModuleCat.{u} A)
  (hP : ∀ a : A, IsLocalizedModule (Submonoid.powers a)
    (P.map (PrimeSpectrum.basicOpen a).leTop.op).hom)

def sheafIso : (presheafToSheaf (Opens.grothendieckTopology (Spec A)) (ModuleCat.{u} A)).obj P ≅
    LocalizingPresheafSheaf.LocalizingPresheafBasis.associatedSheaf A P :=
  BasisSheafificationTo.BasisSheafification.iso (fun a : A => (PrimeSpectrum.basicOpen a : (Spec A).Opens))
    PrimeSpectrum.isBasis_basic_opens P (LocalizingPresheafSheaf.LocalizingPresheafBasis.associatedSheaf A P) (LocalizingPresheafSheaf.LocalizingPresheafBasis.iso A P hP)

variable {D : Type v} [Category.{w} D] (G : ModuleCat.{u} A ⥤ D)
  [(Opens.grothendieckTopology (Spec A)).HasSheafCompose G]
  [HasWeakSheafify (Opens.grothendieckTopology (Spec A)) D]

def sheafIsoComp : (presheafToSheaf (Opens.grothendieckTopology (Spec A)) D).obj (P ⋙ G) ≅
    (sheafCompose (Opens.grothendieckTopology (Spec A)) G).obj (LocalizingPresheafSheaf.LocalizingPresheafBasis.associatedSheaf A P) :=
  BasisSheafificationComposition.BasisSheafification.compIso (fun a : A => (PrimeSpectrum.basicOpen a : (Spec A).Opens))
    PrimeSpectrum.isBasis_basic_opens P (LocalizingPresheafSheaf.LocalizingPresheafBasis.associatedSheaf A P) (LocalizingPresheafSheaf.LocalizingPresheafBasis.iso A P hP) G

end

end OAI.NumberTheory.PadicHodge.GeometricComparison.LocalizingPresheafSheafification.LocalizingPresheafBasis
