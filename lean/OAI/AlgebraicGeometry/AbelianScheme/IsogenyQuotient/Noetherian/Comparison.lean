import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Noetherian.DualIso
import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Noetherian.PolarizationCancellation
import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Specialization
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.PEL.Classifying

/-! # Comparison -/

namespace OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Noetherian.Comparison.Construction

noncomputable section

/-! Equal full kernels determine the entire PEL quotient over a
Noetherian base, including the original normalized Poincare bundle. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj

open OAI.AlgebraicGeometry.Isogenies.NeighborCounting.QuotientComparison

theorem noetherian_quotientComparison_polarization
    {S : Scheme.{0}} [IsLocallyNoetherian S] {g h : ℕ}
    {A : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme g S} {B C : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme h S}
    (f : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme.Isogeny A B) (r : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme.Isogeny A C)
    (DA : AbelianModuli.HilbertConstruction.Dual.Data.DualAbelianData A) (DB : AbelianModuli.HilbertConstruction.Dual.Data.DualAbelianData B) (DC : AbelianModuli.HilbertConstruction.Dual.Data.DualAbelianData C)
    (e : B.scheme ≅ C.scheme) [IsMonHom e.hom] (he : f.hom ≫ e.hom = r.hom)
    {δ ε : Fin h → ℕ} (polB : AbelianModuli.HilbertConstruction.PolarizationData.Polarization DB δ) (polC : AbelianModuli.HilbertConstruction.PolarizationData.Polarization DC ε)
    (hp : FrobeniusKernel.PolarizationComparison.Construction.polarizationPullbackHom f.hom DA DB polB = FrobeniusKernel.PolarizationComparison.Construction.polarizationPullbackHom r.hom DA DC polC) :
    polB.isogeny.hom = e.hom ≫ polC.isogeny.hom ≫ FrobeniusKernel.PicardPullback.Construction.IntrinsicPicardPullback.dualMap e.hom DB DC := by
  have : IsMonHom (FrobeniusKernel.PicardPullback.Construction.IntrinsicPicardPullback.dualMap e.hom DB DC) :=
    DualMaps.Construction.noetherian_nativeDualMap_isMonHom e.hom DB DC
  apply PolarizationCancellation.Construction.noetherian_polarizationPullback_injective f DA DB
  have hd : FrobeniusKernel.PicardPullback.Construction.IntrinsicPicardPullback.dualMap e.hom DB DC ≫ FrobeniusKernel.PicardPullback.Construction.IntrinsicPicardPullback.dualMap f.hom DA DB =
      FrobeniusKernel.PicardPullback.Construction.IntrinsicPicardPullback.dualMap r.hom DA DC :=
    (FrobeniusKernel.PicardPullback.Construction.IntrinsicPicardPullback.dualMap_comp f.hom DA DB DC e.hom).symm.trans
      (DualMaps.Construction.nativeDualMap_congr DA DC _ _ he)
  simp only [Category.assoc]
  rw [hd, ← Category.assoc f.hom e.hom, he]
  exact hp

variable {E K : Type} [Field E] [NumberField E] [Algebra ℚ E]
  [NumberField.IsCMField E] [Field K]
  {d N : ℕ} {P : AbelianModuli.ReferenceFamily.Datum.RankThreePELDatum E d} {iota : E →+* K}
  {T : Over (Spec (.of K))} [IsLocallyNoetherian T.left]
  (A B C : AbelianModuli.ReferenceFamily.PEL.Objects.PELObject P iota N T)
  (f : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme.Isogeny A.polarized.abelian B.polarized.abelian)
  (r : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme.Isogeny A.polarized.abelian C.polarized.abelian)
  (hk : Isogenies.NeighborCounting.QuotientComparison.SameKernel f r)
  (hp : FrobeniusKernel.PolarizationComparison.Construction.polarizationPullbackHom f.hom A.polarized.dual B.polarized.dual B.polarized.polarization =
    FrobeniusKernel.PolarizationComparison.Construction.polarizationPullbackHom r.hom A.polarized.dual C.polarized.dual C.polarized.polarization)
  (hf : ∀ a, f.hom ≫ B.action.map a = A.action.map a ≫ f.hom)
  (hr : ∀ a, r.hom ≫ C.action.map a = A.action.map a ≫ r.hom)
  (hfl : ∀ (U : Over T.left)
    (c : LocallyConstant U.left (Multiplicative (Fin (2 * (3 * d)) → ZMod N))),
    (A.polarized.level.hom.app (.op U) c).val ≫ f.hom = (B.polarized.level.hom.app (.op U) c).val)
  (hrl : ∀ (U : Over T.left)
    (c : LocallyConstant U.left (Multiplicative (Fin (2 * (3 * d)) → ZMod N))),
    (A.polarized.level.hom.app (.op U) c).val ≫ r.hom = (C.polarized.level.hom.app (.op U) c).val)

def noetherianQuotientPELIso : AbelianModuli.ReferenceFamily.PEL.Objects.PELIso B C where
  polarized := {
    abelian := Isogenies.NeighborCounting.QuotientComparison.quotientIso f r hk
    dual := (DualIso.Construction.noetherianNativeDualIso B.polarized.dual C.polarized.dual (Isogenies.NeighborCounting.QuotientComparison.quotientIso f r hk)).symm
    abelianGroup := inferInstance
    dualGroup := DualIso.Construction.noetherianNativeDualIso_inv_isMonHom B.polarized.dual C.polarized.dual (Isogenies.NeighborCounting.QuotientComparison.quotientIso f r hk)
    polarization := by
      let e := Isogenies.NeighborCounting.QuotientComparison.quotientIso f r hk
      let d := DualIso.Construction.noetherianNativeDualIso B.polarized.dual C.polarized.dual e
      have h : B.polarized.polarization.isogeny.hom =
          e.hom ≫ C.polarized.polarization.isogeny.hom ≫ d.hom :=
        noetherian_quotientComparison_polarization f r A.polarized.dual B.polarized.dual
          C.polarized.dual e (Isogenies.NeighborCounting.QuotientComparison.quotientIso_projection f r hk) _ _ hp
      change B.polarized.polarization.isogeny.hom ≫ d.inv = e.hom ≫ C.polarized.polarization.isogeny.hom
      rw [h, Category.assoc, Category.assoc, d.hom_inv_id, Category.comp_id]
    poincare := DualIso.Construction.noetherianNativeDualIso_poincare B.polarized.dual C.polarized.dual (Isogenies.NeighborCounting.QuotientComparison.quotientIso f r hk)
    level U c := by
      rw [← hfl U c, Category.assoc, Isogenies.NeighborCounting.QuotientComparison.quotientIso_projection, hrl U c] }
  action a := by
    have : EffectiveEpi f.hom := Picard.Homomorphisms.GroupDescent.Construction.effectiveEpi_over_of_fpqc f.hom
    change B.action.map a ≫ (Isogenies.NeighborCounting.QuotientComparison.quotientIso f r hk).hom = (Isogenies.NeighborCounting.QuotientComparison.quotientIso f r hk).hom ≫ C.action.map a
    apply (cancel_epi f.hom).mp
    rw [← Category.assoc, hf, Category.assoc, Isogenies.NeighborCounting.QuotientComparison.quotientIso_projection,
      ← Category.assoc, Isogenies.NeighborCounting.QuotientComparison.quotientIso_projection, hr]

include A f r hk hp hf hr hfl hrl in
theorem noetherianQuotientPELClass_eq : B.classOf = C.classOf :=
  Quotient.sound ⟨noetherianQuotientPELIso A B C f r hk hp hf hr hfl hrl⟩

end

end OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Noetherian.Comparison.Construction
