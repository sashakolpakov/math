import OAI.NumberTheory.PadicHodge.GeometricComparison.LocalizingPresheafSheafification
import OAI.NumberTheory.PadicHodge.GeometricComparison.BasisSheafificationUnit

/-! # Localizing Presheaf Unit -/

namespace OAI.NumberTheory.PadicHodge.GeometricComparison.LocalizingPresheafUnit.LocalizingPresheafBasis

noncomputable section

/-! The canonical sheafification map of a localizing affine presheaf is invertible on principal opens after a sheaf-preserving coefficient change. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry Opposite

universe u v w

variable (A : CommRingCat.{u})
  (P : (Spec A).Opensᵒᵖ ⥤ ModuleCat.{u} A)
  (hP : ∀ a : A, IsLocalizedModule (Submonoid.powers a)
    (P.map (PrimeSpectrum.basicOpen a).leTop.op).hom)
  {D : Type v} [Category.{w} D] (G : ModuleCat.{u} A ⥤ D)
  [(Opens.grothendieckTopology (Spec A)).HasSheafCompose G]
  [HasWeakSheafify (Opens.grothendieckTopology (Spec A)) D]

include hP in
theorem unit_comp_basicOpen_isIso (a : A) :
    IsIso ((toSheafify (Opens.grothendieckTopology (Spec A)) (P ⋙ G)).app
      (op (PrimeSpectrum.basicOpen a))) :=
  BasisSheafificationUnit.BasisSheafification.unit_app_isIso
    (fun a : A => (PrimeSpectrum.basicOpen a : (Spec A).Opens))
    PrimeSpectrum.isBasis_basic_opens (P ⋙ G)
    ((sheafCompose (Opens.grothendieckTopology (Spec A)) G).obj (LocalizingPresheafSheaf.LocalizingPresheafBasis.associatedSheaf A P))
    (BasisSheafificationComposition.BasisSheafification.compBasisIso
      (fun a : A => (PrimeSpectrum.basicOpen a : (Spec A).Opens))
      P (LocalizingPresheafSheaf.LocalizingPresheafBasis.associatedSheaf A P) (LocalizingPresheafSheaf.LocalizingPresheafBasis.iso A P hP) G) a

end

end OAI.NumberTheory.PadicHodge.GeometricComparison.LocalizingPresheafUnit.LocalizingPresheafBasis
