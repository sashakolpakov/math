import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Picard.PELFamily
import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Picard.Rosati

/-! # Family Rosati -/

namespace OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Picard.FamilyRosati.Construction

noncomputable section

/-! The actual quotient family satisfies the full Rosati predicate,
including the original Poincare class equation for each integral adjoint.
The proof uses the source predicate and the constructed quotient equation. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory
open scoped _root_.CategoryTheory.MonObj

universe u

variable {R : Type u} [CommRing R] {g N : ℕ}
  {k : Type u} [Field k] [IsAlgClosed k]
  (P : TateComparison.PEL.PELFamilyData R g N (Spec (.of k)))
  (B : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme g (Spec (.of k))) (DB : AbelianModuli.HilbertConstruction.Dual.Data.DualAbelianData B)
  (m : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme.Isogeny B DB.abelian)
  (σ : AbelianModuli.ReferenceFamily.ActionData.IntegralAction R B) (level : B.FullLevel N)
  (f : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme.Isogeny P.abelian B) (n : ℕ)
  (hσ : ∀ a : R, (TateComparison.PELAdapters.actionFromEnd P.action).map a ≫ f.hom = f.hom ≫ σ.map a)
  (hp : f.hom ≫ m.hom ≫ FrobeniusKernel.PicardPullback.Construction.IntrinsicPicardPullback.dualMap f.hom P.dual DB = P.polarizationMap.hom ^ n)

include hσ hp in
set_option backward.isDefEq.respectTransparency false in
theorem picardQuotientFamily_rosati (c : R →+* R) (hR : P.IsRosatiCompatible c) :
    (PELFamily.Construction.picardQuotientFamily B DB m σ level).IsRosatiCompatible c := by
  intro a
  let bd := FrobeniusKernel.PicardPullback.Construction.IntrinsicPicardPullback.dualMap (σ.map a) DB DB
  have : IsMonHom bd := FrobeniusKernel.PicardGroupMap.Construction.IntrinsicPicardPullback.dualMap_isMonHom (σ.map a) DB DB
  refine ⟨TateComparison.End.endOfSchemeMap DB.abelian.scheme bd, ?_, ?_⟩
  · change AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackClass
        (𝟙 DB.abelian.scheme ⊗ₘ TateComparison.End.endSchemeMap B.scheme (TateComparison.PELAdapters.actionToEnd σ a)).left
        (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf DB.poincare) =
      AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackClass
        (TateComparison.End.endSchemeMap DB.abelian.scheme (TateComparison.End.endOfSchemeMap DB.abelian.scheme bd) ⊗ₘ 𝟙 B.scheme).left
        (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf DB.poincare)
    rw [TateComparison.PELAdapters.actionToEnd_schemeMap, TateComparison.End.endSchemeMap_ofSchemeMap]
    exact (FrobeniusKernel.IntrinsicPoincare.Construction.IntrinsicPicardPullback.dualMap_poincare DB DB (σ.map a)).symm
  · change m.hom ≫ TateComparison.End.endSchemeMap DB.abelian.scheme (TateComparison.End.endOfSchemeMap DB.abelian.scheme bd) =
      TateComparison.End.endSchemeMap B.scheme (TateComparison.PELAdapters.actionToEnd σ (c a)) ≫ m.hom
    rw [TateComparison.End.endSchemeMap_ofSchemeMap, TateComparison.PELAdapters.actionToEnd_schemeMap]
    obtain ⟨ad, hclass, hsource⟩ := hR a
    have ha := FrobeniusKernel.PicardAdjoints.Construction.NativePicardPullback.dualMap_eq_of_poincare
      (TateComparison.End.endSchemeMap P.abelian.scheme (P.action a)) P.dual P.dual
      (TateComparison.End.endSchemeMap P.dual.abelian.scheme ad) hclass.symm
    rw [ha] at hsource
    exact Rosati.Construction.picardQuotient_rosati_equation P.dual DB f P.polarizationMap.hom m.hom
      (TateComparison.PELAdapters.actionFromEnd P.action) σ hσ n hp a (c a) hsource

end

end OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Picard.FamilyRosati.Construction
