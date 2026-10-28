import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Reference.DualPointLifts
import OAI.RepresentationTheory.Theta.Geometric.DescendedInfinitesimalComparison

/-! # Infinitesimal Picard Lift -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Reference

noncomputable section

/-! A native dual-number point in the descended Picard kernel lifts to
an actual origin translation preserving the original line bundle family. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory
open scoped _root_.CategoryTheory.MonObj

variable {E : Type} [Field E] [NumberField E] [Algebra ℚ E]
    [NumberField.IsCMField E] {s : ℕ} {P : Datum.RankThreePELDatum E s}
    {z : P.domain} {F : Fiber.ReferenceAnalyticFiber P z} {hP : P.IsAdmissible}
    {M : AlgebraicModel.ReferenceAlgebraicModel F hP} {N : DualModel.ReferenceDualModel F hP}

open OAI.RepresentationTheory.Theta.Geometric.DescendedInfinitesimalComparison

theorem IsogenyKernel.ReferenceLatticeIsogeny.exists_infinitesimal_translation_comparison (p : IsogenyKernel.ReferenceLatticeIsogeny M N)
    (L : HilbertConstruction.Line.Bundles.LineBundle M.abelianScheme.scheme.left)
    (Q : HilbertConstruction.Line.Bundles.LineBundle (N.abelianScheme.scheme ⊗ M.abelianScheme.scheme).left)
    (recover : (Q.pullback (p.isogeny.hom ⊗ₘ 𝟙 M.abelianScheme.scheme).left).sheaf ≅
      (RepresentationTheory.Theta.Geometric.AbelianDifferenceBundle.abelianDifferenceBundle M.abelianScheme L).sheaf)
    (eA : (Q.pullback (lift (𝟙 N.abelianScheme.scheme)
      (1 : N.abelianScheme.scheme ⟶ M.abelianScheme.scheme)).left).sheaf ≅ HilbertConstruction.Line.Bundles.structureModule N.abelianScheme.scheme.left)
    (eB : (Q.pullback (lift (1 : M.abelianScheme.scheme ⟶ N.abelianScheme.scheme)
      (𝟙 M.abelianScheme.scheme)).left).sheaf ≅ HilbertConstruction.Line.Bundles.structureModule M.abelianScheme.scheme.left)
    (v : DualOpen.Lifts.DualSchemePoints N.abelian.toOver 1)
    (hv : RepresentationTheory.Theta.Geometric.ParameterizedPicardClass.parameterPicardClass Q v.val = RepresentationTheory.Theta.Geometric.ParameterizedPicardClass.parameterPicardClass Q
      (1 : LieRanks.dualNumberTest ℂ ⟶ N.abelianScheme.scheme)) :
    ∃ r : DualOpen.Lifts.DualSchemePoints M.abelian.toOver 1, r.val ≫ p.nativeMap = v.val ∧
      Nonempty (((L.pullback (snd (LieRanks.dualNumberTest ℂ) M.abelianScheme.scheme).left).pullback
        (M.abelianScheme.translation r.val).left).sheaf ≅
          (L.pullback (snd (LieRanks.dualNumberTest ℂ) M.abelianScheme.scheme).left).sheaf) := by
  let : Subsingleton (LieRanks.dualNumberTest ℂ).left := Dual.NumberSpectrum.dualNumber_primeSpectrum_subsingleton
  let : Nonempty (LieRanks.dualNumberTest ℂ).left :=
    ⟨(LieRanks.dualNumberOrigin ℂ).left (default : Foundations.Scheme.ProjectiveSpace.complexBase)⟩
  let : CompactSpace (LieRanks.dualNumberTest ℂ).left :=
    inferInstanceAs (CompactSpace (Spec (.of (DualNumber ℂ))))
  let : QuasiSeparatedSpace (LieRanks.dualNumberTest ℂ).left :=
    inferInstanceAs (QuasiSeparatedSpace (Spec (.of (DualNumber ℂ))))
  obtain ⟨r, hr⟩ := p.exists_dualPoint_at_origin_lift v
  refine ⟨r, hr, ?_⟩
  apply RepresentationTheory.Theta.Geometric.DescendedInfinitesimalComparison.descendedParameter_trivial_translation_iso M.abelianScheme N.abelianScheme
    p.isogeny.hom L Q recover eA eB r.val
  exact (congrArg (fun t : LieRanks.dualNumberTest ℂ ⟶ N.abelianScheme.scheme => RepresentationTheory.Theta.Geometric.ParameterizedPicardClass.parameterPicardClass Q t) hr).trans hv

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Reference
