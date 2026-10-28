import OAI.AlgebraicGeometry.AbelianScheme.TateComparison.PELModuli
import OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.IntrinsicPoincare

/-! # Canonical PEL -/

namespace OAI.AlgebraicGeometry.AbelianScheme.TateComparison

noncomputable section

/-! Construct a complete PEL comparison from an abelian isomorphism.
The dual and its raw Poincare identity are supplied by the actual Picard
pullback construction, leaving only the geometric action, level and
polarization equations to verify. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory
open scoped _root_.CategoryTheory.MonObj

open OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.IntrinsicPoincare.Construction.IntrinsicPicardPullback
variable {R k : Type} [CommRing R] [Field k] [IsAlgClosed k] {g N : ℕ}
  {P Q : PEL.PELFamilyData R g N (Spec (.of k))}

def PELModuli.PELFamilyIso.ofAbelianIso (e : P.abelian.scheme ≅ Q.abelian.scheme) [IsMonHom e.hom]
    (hp : e.hom ≫ Q.polarizationMap.hom ≫ FrobeniusKernel.PicardPullback.Construction.IntrinsicPicardPullback.dualMap e.hom P.dual Q.dual =
      P.polarizationMap.hom)
    (ha : ∀ r : R, End.endSchemeMap P.abelian.scheme (P.action r) ≫ e.hom =
      e.hom ≫ End.endSchemeMap Q.abelian.scheme (Q.action r))
    (hl : ∀ (T : Over (Spec (.of k)))
      (c : LocallyConstant T.left (Multiplicative (Fin (2 * g) → ZMod N))),
      (P.marking.hom.app (.op T) c).val ≫ e.hom = (Q.marking.hom.app (.op T) c).val) :
    PELModuli.PELFamilyIso P Q where
  abelian := e
  dual := (FrobeniusKernel.IntrinsicPoincare.Construction.IntrinsicPicardPullback.dualIso P.dual Q.dual e).symm
  abelianGroup := inferInstance
  dualGroup := inferInstanceAs (IsMonHom (FrobeniusKernel.IntrinsicPoincare.Construction.IntrinsicPicardPullback.dualIso P.dual Q.dual e).inv)
  polarization := by
    let d := FrobeniusKernel.IntrinsicPoincare.Construction.IntrinsicPicardPullback.dualIso P.dual Q.dual e
    have hd : d.hom = FrobeniusKernel.PicardPullback.Construction.IntrinsicPicardPullback.dualMap e.hom P.dual Q.dual := FrobeniusKernel.IntrinsicPoincare.Construction.IntrinsicPicardPullback.dualIso_hom P.dual Q.dual e
    have hpd : e.hom ≫ Q.polarizationMap.hom ≫ d.hom = P.polarizationMap.hom :=
      (congrArg (fun z => e.hom ≫ Q.polarizationMap.hom ≫ z) hd).trans hp
    have ht := congrArg (fun z => z ≫ d.inv) hpd
    change P.polarizationMap.hom ≫ d.inv = e.hom ≫ Q.polarizationMap.hom
    simpa only [Category.assoc, Iso.hom_inv_id, Category.comp_id] using ht.symm
  poincare := FrobeniusKernel.IntrinsicPoincare.Construction.IntrinsicPicardPullback.dualIso_poincare P.dual Q.dual e
  equivariant := ha
  marking := hl

end

end OAI.AlgebraicGeometry.AbelianScheme.TateComparison
