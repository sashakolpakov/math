import OAI.AlgebraicGeometry.Divisors.LineBundles.Conormal.InfinityGluing
import OAI.AlgebraicGeometry.Divisors.LineBundles.Conormal.ProjectiveGluing
import OAI.AlgebraicGeometry.Divisors.LineBundles.SymmetricInfinity.Naturality
import OAI.AlgebraicGeometry.Divisors.LineBundles.SymmetricProjective.Base

/-! # Infinity Inclusion Diagram -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles.Conormal.InfinityInclusionDiagram.BundleCycles

noncomputable section

/-! The genuine closed infinity inclusions are a natural transformation
over the ambient scheme. -/

open _root_.AlgebraicGeometry _root_.CategoryTheory
open _root_.AlgebraicGeometry.Scheme.AffineZariskiSite

variable {X : Scheme.{0}} (I : X.IdealSheafData)

def conormalInfinityInclusionDiagram :
    (InfinityGluing.BundleCycles.conormalInfinityGlueData I).functor ⟶ (ProjectiveGluing.BundleCycles.conormalProjectiveGlueData I).functor where
  app U := SymmetricInfinity.Inclusion.BundleCycles.symmetricInfinityInclusion (Γ(X, U.1) ⧸ I.ideal U) (I.ideal U).Cotangent
  naturality {_U _V} i := (SymmetricInfinity.Naturality.BundleCycles.symmetricInfinityInclusion_naturality _ _ (RestrictionSpan.BundleCycles.conormalRestriction_span I i)).symm

theorem conormalInfinityInclusionDiagram_over :
    conormalInfinityInclusionDiagram I ≫ (ProjectiveGluing.BundleCycles.conormalProjectiveGlueData I).natTrans =
      (InfinityGluing.BundleCycles.conormalInfinityGlueData I).natTrans := by
  apply NatTrans.ext
  funext U
  let R := Γ(X, U.1) ⧸ I.ideal U
  let M := (I.ideal U).Cotangent
  let q := CommRingCat.ofHom (Ideal.Quotient.mk (I.ideal U))
  change SymmetricInfinity.Inclusion.BundleCycles.symmetricInfinityInclusion R M ≫
    (SymmetricProjective.Scheme.BundleCycles.symmetricProjectiveToBase R (R × M) ≫ (Spec.map q ≫ U.2.isoSpec.inv)) =
    SymmetricProjective.Scheme.BundleCycles.symmetricProjectiveToBase R M ≫ (Spec.map q ≫ U.2.isoSpec.inv)
  rw [← Category.assoc]
  exact congrArg (fun k => k ≫ (Spec.map q ≫ U.2.isoSpec.inv))
    (SymmetricProjective.Base.BundleCycles.symmetricProjectiveMap_over (LinearMap.snd R R M) (fun m => ⟨(0, m), rfl⟩))

end

end OAI.AlgebraicGeometry.Divisors.LineBundles.Conormal.InfinityInclusionDiagram.BundleCycles
