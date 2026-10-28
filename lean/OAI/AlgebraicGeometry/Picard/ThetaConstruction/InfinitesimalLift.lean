import OAI.AlgebraicGeometry.Picard.ThetaConstruction.DualPointLifts
import OAI.RepresentationTheory.Theta.Geometric.DescendedInfinitesimalComparison

/-! # Infinitesimal Lift -/

namespace OAI.AlgebraicGeometry.Picard.ThetaConstruction

noncomputable section

/-! A native dual-number point in the descended Picard kernel lifts to
an actual origin translation preserving the original line bundle family. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory
open scoped _root_.CategoryTheory.MonObj

variable {dim : ℕ} {matrix : DefinitionsIntegral.IntegralMatrix dim}
    {F : DefinitionsIntegral.MarkedPolarizedTorus dim matrix}
    {M : PeriodModel.Geometric.AlgebraicPeriodModel F} {N : IntegralDualModel.Geometric.IntegralDualAlgebraicModel F}

open OAI.RepresentationTheory.Theta.Geometric.DescendedInfinitesimalComparison

theorem IntegralDualIsogenyKernel.Geometric.IntegralDualLatticeIsogeny.exists_infinitesimal_translation_comparison (p : IntegralDualIsogenyKernel.Geometric.IntegralDualLatticeIsogeny M N)
    (L : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle M.abelianScheme.scheme.left)
    (Q : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle (N.abelianScheme.scheme ⊗ M.abelianScheme.scheme).left)
    (recover : (Q.pullback (p.isogeny.hom ⊗ₘ 𝟙 M.abelianScheme.scheme).left).sheaf ≅
      (RepresentationTheory.Theta.Geometric.AbelianDifferenceBundle.abelianDifferenceBundle M.abelianScheme L).sheaf)
    (eA : (Q.pullback (lift (𝟙 N.abelianScheme.scheme)
      (1 : N.abelianScheme.scheme ⟶ M.abelianScheme.scheme)).left).sheaf ≅ AbelianModuli.HilbertConstruction.Line.Bundles.structureModule N.abelianScheme.scheme.left)
    (eB : (Q.pullback (lift (1 : M.abelianScheme.scheme ⟶ N.abelianScheme.scheme)
      (𝟙 M.abelianScheme.scheme)).left).sheaf ≅ AbelianModuli.HilbertConstruction.Line.Bundles.structureModule M.abelianScheme.scheme.left)
    (v : AbelianModuli.ReferenceFamily.DualOpen.Lifts.DualSchemePoints N.abelian.toOver 1)
    (hv : RepresentationTheory.Theta.Geometric.ParameterizedPicardClass.parameterPicardClass Q v.val = RepresentationTheory.Theta.Geometric.ParameterizedPicardClass.parameterPicardClass Q
      (1 : AbelianModuli.ReferenceFamily.LieRanks.dualNumberTest ℂ ⟶ N.abelianScheme.scheme)) :
    ∃ r : AbelianModuli.ReferenceFamily.DualOpen.Lifts.DualSchemePoints M.abelian.toOver 1, r.val ≫ p.nativeMap = v.val ∧
      Nonempty (((L.pullback (snd (AbelianModuli.ReferenceFamily.LieRanks.dualNumberTest ℂ) M.abelianScheme.scheme).left).pullback
        (M.abelianScheme.translation r.val).left).sheaf ≅
          (L.pullback (snd (AbelianModuli.ReferenceFamily.LieRanks.dualNumberTest ℂ) M.abelianScheme.scheme).left).sheaf) := by
  let : Subsingleton (AbelianModuli.ReferenceFamily.LieRanks.dualNumberTest ℂ).left := AbelianModuli.ReferenceFamily.Dual.NumberSpectrum.dualNumber_primeSpectrum_subsingleton
  let : Nonempty (AbelianModuli.ReferenceFamily.LieRanks.dualNumberTest ℂ).left :=
    ⟨(AbelianModuli.ReferenceFamily.LieRanks.dualNumberOrigin ℂ).left (default : Foundations.Scheme.ProjectiveSpace.complexBase)⟩
  let : CompactSpace (AbelianModuli.ReferenceFamily.LieRanks.dualNumberTest ℂ).left :=
    inferInstanceAs (CompactSpace (Spec (.of (DualNumber ℂ))))
  let : QuasiSeparatedSpace (AbelianModuli.ReferenceFamily.LieRanks.dualNumberTest ℂ).left :=
    inferInstanceAs (QuasiSeparatedSpace (Spec (.of (DualNumber ℂ))))
  obtain ⟨r, hr⟩ := p.exists_dualPoint_at_origin_lift v
  refine ⟨r, hr, ?_⟩
  apply RepresentationTheory.Theta.Geometric.DescendedInfinitesimalComparison.descendedParameter_trivial_translation_iso M.abelianScheme N.abelianScheme
    p.isogeny.hom L Q recover eA eB r.val
  exact (congrArg (fun t : AbelianModuli.ReferenceFamily.LieRanks.dualNumberTest ℂ ⟶ N.abelianScheme.scheme => RepresentationTheory.Theta.Geometric.ParameterizedPicardClass.parameterPicardClass Q t) hr).trans hv

end

end OAI.AlgebraicGeometry.Picard.ThetaConstruction
