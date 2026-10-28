import OAI.AlgebraicGeometry.AbelianScheme.TateComparison.PELIsogenies
import OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.PicardAdjoints
import OAI.AlgebraicGeometry.Picard.Homomorphisms.UnbundledDualPullback

/-! # PEL Picard Dual Maps -/

namespace OAI.AlgebraicGeometry.AbelianScheme.TateComparison

noncomputable section

/-! The original PEL Poincare equations identify the actual maps
used by native Weil naturality with canonical Picard dual pullback. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj

open OAI.AlgebraicGeometry.Picard.Homomorphisms.UnbundledDualPullback.Construction.UnbundledPicard

variable {R : Type} [CommRing R] {S : Scheme} {g N : ℕ}
  (P Q : PEL.PELFamilyData R g N S)
  (f : P.abelian.scheme ⟶ Q.abelian.scheme) [IsMonHom f]
  (d : Q.dual.abelian.scheme ⟶ P.dual.abelian.scheme) [IsMonHom d]

omit [IsMonHom d] in
theorem PELPicardDualMaps.pelPoincareDual_eq_picard
    (h : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackClass (𝟙 Q.dual.abelian.scheme ⊗ₘ f).left (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf Q.dual.poincare) =
      AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackClass (d ⊗ₘ 𝟙 P.abelian.scheme).left (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf P.dual.poincare)) :
    d = Picard.Homomorphisms.UnbundledDualPullback.Construction.UnbundledPicard.dualPicardPullback (Picard.Homomorphisms.UnbundledDualData.Construction.UnbundledPicard.DualData.ofBundled P.dual) (Picard.Homomorphisms.UnbundledDualData.Construction.UnbundledPicard.DualData.ofBundled Q.dual) f := by
  have hd : d = FrobeniusKernel.PicardPullback.Construction.IntrinsicPicardPullback.dualMap f P.dual Q.dual := FrobeniusKernel.PicardAdjoints.Construction.NativePicardPullback.dualMap_eq_of_poincare f P.dual Q.dual d h.symm
  rw [FrobeniusKernel.Polarization.Construction.NativePicardPullback.dualMap_eq_e57] at hd
  exact hd

section
variable {P Q}

theorem PELIsogenies.PELIsogeny.dualHom_eq_picard {m : ℕ} (e : PELIsogenies.PELIsogeny P Q m) :
    e.dualHom = Picard.Homomorphisms.UnbundledDualPullback.Construction.UnbundledPicard.dualPicardPullback (Picard.Homomorphisms.UnbundledDualData.Construction.UnbundledPicard.DualData.ofBundled P.dual) (Picard.Homomorphisms.UnbundledDualData.Construction.UnbundledPicard.DualData.ofBundled Q.dual) e.isogeny.hom :=
  PELPicardDualMaps.pelPoincareDual_eq_picard P Q e.isogeny.hom e.dualHom e.poincare

end

theorem PEL.PELFamilyData.poincareDual_eq_picard (a : End.IntegralEnd P.abelian.scheme) (b : End.IntegralEnd P.dual.abelian.scheme)
    (h : P.IsPoincareDual a b) :
    End.endSchemeMap P.dual.abelian.scheme b =
      Picard.Homomorphisms.UnbundledDualPullback.Construction.UnbundledPicard.dualPicardPullback (Picard.Homomorphisms.UnbundledDualData.Construction.UnbundledPicard.DualData.ofBundled P.dual) (Picard.Homomorphisms.UnbundledDualData.Construction.UnbundledPicard.DualData.ofBundled P.dual) (End.endSchemeMap P.abelian.scheme a) :=
  PELPicardDualMaps.pelPoincareDual_eq_picard P P (End.endSchemeMap P.abelian.scheme a) (End.endSchemeMap P.dual.abelian.scheme b) h

end

end OAI.AlgebraicGeometry.AbelianScheme.TateComparison
