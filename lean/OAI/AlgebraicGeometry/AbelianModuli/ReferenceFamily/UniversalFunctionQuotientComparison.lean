import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.UniversalFunctionDualIso
import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.UniversalFunction.PolarizationCancellation
import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Specialization
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.PEL.Classifying

/-! # Universal Function Quotient Comparison -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.UniversalFunctionQuotientComparison

noncomputable section

/-! Equal original full kernels determine the entire PEL quotient
on every test base when the source has universal global functions.
The dual and Poincare comparisons are constructed from Picard pullback. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj

open OAI.AlgebraicGeometry.Isogenies.NeighborCounting.QuotientComparison

theorem universalFunction_quotientComparison_polarization
    {S : Scheme.{0}} {g h : ℕ}
    {A : HilbertConstruction.Abelian.Schemes.AbelianScheme g S} {B C : HilbertConstruction.Abelian.Schemes.AbelianScheme h S}
    (f : HilbertConstruction.Abelian.Schemes.AbelianScheme.Isogeny A B) (r : HilbertConstruction.Abelian.Schemes.AbelianScheme.Isogeny A C)
    (DA : HilbertConstruction.Dual.Data.DualAbelianData A) (DB : HilbertConstruction.Dual.Data.DualAbelianData B) (DC : HilbertConstruction.Dual.Data.DualAbelianData C)
    (hB : AbelianScheme.IsogenyQuotient.GlobalFunctions.Construction.HasUniversalGlobalFunctions B.scheme)
    (hDC : AbelianScheme.IsogenyQuotient.GlobalFunctions.Construction.HasUniversalGlobalFunctions DC.abelian.scheme)
    (e : B.scheme ≅ C.scheme) [IsMonHom e.hom] (he : f.hom ≫ e.hom = r.hom)
    {δ ε : Fin h → ℕ} (polB : HilbertConstruction.PolarizationData.Polarization DB δ) (polC : HilbertConstruction.PolarizationData.Polarization DC ε)
    (hp : AbelianScheme.FrobeniusKernel.PolarizationComparison.Construction.polarizationPullbackHom f.hom DA DB polB = AbelianScheme.FrobeniusKernel.PolarizationComparison.Construction.polarizationPullbackHom r.hom DA DC polC) :
    polB.isogeny.hom = e.hom ≫ polC.isogeny.hom ≫ AbelianScheme.FrobeniusKernel.PicardPullback.Construction.IntrinsicPicardPullback.dualMap e.hom DB DC := by
  have : IsMonHom (AbelianScheme.FrobeniusKernel.PicardPullback.Construction.IntrinsicPicardPullback.dualMap e.hom DB DC) :=
    AbelianScheme.IsogenyQuotient.UniversalFunction.DualMaps.Construction.universalFunction_nativeDualMap_isMonHom e.hom DB DC hDC
  apply AbelianScheme.IsogenyQuotient.UniversalFunction.PolarizationCancellation.Construction.universalFunction_polarizationPullback_injective f DA DB hB
  have hd : AbelianScheme.FrobeniusKernel.PicardPullback.Construction.IntrinsicPicardPullback.dualMap e.hom DB DC ≫ AbelianScheme.FrobeniusKernel.PicardPullback.Construction.IntrinsicPicardPullback.dualMap f.hom DA DB =
      AbelianScheme.FrobeniusKernel.PicardPullback.Construction.IntrinsicPicardPullback.dualMap r.hom DA DC :=
    (AbelianScheme.FrobeniusKernel.PicardPullback.Construction.IntrinsicPicardPullback.dualMap_comp f.hom DA DB DC e.hom).symm.trans
      (AbelianScheme.IsogenyQuotient.Noetherian.DualMaps.Construction.nativeDualMap_congr DA DC _ _ he)
  simp only [Category.assoc]
  rw [hd, ← Category.assoc f.hom e.hom, he]
  exact hp

variable {E K : Type} [Field E] [NumberField E] [Algebra ℚ E]
    [NumberField.IsCMField E] [Field K]
    {s N : ℕ} {P : Datum.RankThreePELDatum E s} {iota : E →+* K}
    {T : Over (Spec (.of K))}
    (A B C : PEL.Objects.PELObject P iota N T)
    (hA : AbelianScheme.IsogenyQuotient.GlobalFunctions.Construction.HasUniversalGlobalFunctions A.polarized.abelian.scheme)
    (f : HilbertConstruction.Abelian.Schemes.AbelianScheme.Isogeny A.polarized.abelian B.polarized.abelian)
    (r : HilbertConstruction.Abelian.Schemes.AbelianScheme.Isogeny A.polarized.abelian C.polarized.abelian)
    (hk : Isogenies.NeighborCounting.QuotientComparison.SameKernel f r)
    (hp : AbelianScheme.FrobeniusKernel.PolarizationComparison.Construction.polarizationPullbackHom f.hom A.polarized.dual B.polarized.dual B.polarized.polarization =
      AbelianScheme.FrobeniusKernel.PolarizationComparison.Construction.polarizationPullbackHom r.hom A.polarized.dual C.polarized.dual C.polarized.polarization)
    (hf : ∀ a, f.hom ≫ B.action.map a = A.action.map a ≫ f.hom)
    (hr : ∀ a, r.hom ≫ C.action.map a = A.action.map a ≫ r.hom)
    (hfl : ∀ (U : Over T.left)
      (c : LocallyConstant U.left (Multiplicative (Fin (2 * (3 * s)) → ZMod N))),
      (A.polarized.level.hom.app (.op U) c).val ≫ f.hom = (B.polarized.level.hom.app (.op U) c).val)
    (hrl : ∀ (U : Over T.left)
      (c : LocallyConstant U.left (Multiplicative (Fin (2 * (3 * s)) → ZMod N))),
      (A.polarized.level.hom.app (.op U) c).val ≫ r.hom = (C.polarized.level.hom.app (.op U) c).val)

def universalFunctionQuotientPELIso : PEL.Objects.PELIso B C := by
  let hB := AbelianScheme.IsogenyQuotient.GlobalFunctions.Construction.universalGlobalFunctions_of_finiteFlat_source f.hom hA
  let hC := AbelianScheme.IsogenyQuotient.GlobalFunctions.Construction.universalGlobalFunctions_of_finiteFlat_source r.hom hA
  let hDB := AbelianScheme.IsogenyQuotient.GlobalFunctions.Construction.universalGlobalFunctions_of_finiteFlat_source B.polarized.polarization.isogeny.hom hB
  let hDC := AbelianScheme.IsogenyQuotient.GlobalFunctions.Construction.universalGlobalFunctions_of_finiteFlat_source C.polarized.polarization.isogeny.hom hC
  exact {
    polarized := {
      abelian := Isogenies.NeighborCounting.QuotientComparison.quotientIso f r hk
      dual := (UniversalFunctionDualIso.originalNativeDualIso B.polarized.dual C.polarized.dual (Isogenies.NeighborCounting.QuotientComparison.quotientIso f r hk)).symm
      abelianGroup := inferInstance
      dualGroup := UniversalFunctionDualIso.originalNativeDualIso_inv_isMonHom B.polarized.dual C.polarized.dual
        (Isogenies.NeighborCounting.QuotientComparison.quotientIso f r hk) hDB
      polarization := by
        let e := Isogenies.NeighborCounting.QuotientComparison.quotientIso f r hk
        let d := UniversalFunctionDualIso.originalNativeDualIso B.polarized.dual C.polarized.dual e
        have h : B.polarized.polarization.isogeny.hom =
            e.hom ≫ C.polarized.polarization.isogeny.hom ≫ d.hom :=
          universalFunction_quotientComparison_polarization f r A.polarized.dual
            B.polarized.dual C.polarized.dual hB hDC e (Isogenies.NeighborCounting.QuotientComparison.quotientIso_projection f r hk) _ _ hp
        change B.polarized.polarization.isogeny.hom ≫ d.inv = e.hom ≫ C.polarized.polarization.isogeny.hom
        rw [h, Category.assoc, Category.assoc, d.hom_inv_id, Category.comp_id]
      poincare := UniversalFunctionDualIso.originalNativeDualIso_poincare B.polarized.dual C.polarized.dual
        (Isogenies.NeighborCounting.QuotientComparison.quotientIso f r hk) hC
      level U c := by
        rw [← hfl U c, Category.assoc, Isogenies.NeighborCounting.QuotientComparison.quotientIso_projection, hrl U c] }
    action a := by
      have : EffectiveEpi f.hom := Picard.Homomorphisms.GroupDescent.Construction.effectiveEpi_over_of_fpqc f.hom
      change B.action.map a ≫ (Isogenies.NeighborCounting.QuotientComparison.quotientIso f r hk).hom = (Isogenies.NeighborCounting.QuotientComparison.quotientIso f r hk).hom ≫ C.action.map a
      apply (cancel_epi f.hom).mp
      rw [← Category.assoc, hf, Category.assoc, Isogenies.NeighborCounting.QuotientComparison.quotientIso_projection,
        ← Category.assoc, Isogenies.NeighborCounting.QuotientComparison.quotientIso_projection, hr] }

theorem universalFunctionQuotientPELIso_projection :
    f.hom ≫ (universalFunctionQuotientPELIso A B C hA f r hk hp hf hr hfl hrl).polarized.abelian.hom =
      r.hom := Isogenies.NeighborCounting.QuotientComparison.quotientIso_projection f r hk

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.UniversalFunctionQuotientComparison
