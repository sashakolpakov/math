import OAI.AlgebraicGeometry.AbelianScheme.TateComparison.PELAdapters
import OAI.AlgebraicGeometry.AbelianScheme.TateComparison.PELIsogenies
import OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.IntrinsicPoincare
import OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.PicardGroupMap

/-! # PEL Family -/

namespace OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Picard.PELFamily.Construction

noncomputable section

/-! The constructed quotient map, action and marking form actual PEL
isogeny data once the quotient Picard isogeny is available. Geometric
positivity and the PEL predicates remain separate from this data. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj

universe u

variable {R : Type u} [CommRing R] {g N : ℕ} {S : Scheme.{u}}
  (B : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme g S) (DB : AbelianModuli.HilbertConstruction.Dual.Data.DualAbelianData B)
  (m : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme.Isogeny B DB.abelian)
  (σ : AbelianModuli.ReferenceFamily.ActionData.IntegralAction R B) (level : B.FullLevel N)

def picardQuotientFamily : TateComparison.PEL.PELFamilyData R g N S where
  abelian := B
  dual := DB
  polarizationMap := m
  marking := level
  action := TateComparison.PELAdapters.actionToEnd σ

variable {k : Type u} [Field k] [IsAlgClosed k]
  (P : TateComparison.PEL.PELFamilyData R g N (Spec (.of k)))
  (B : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme g (Spec (.of k))) (DB : AbelianModuli.HilbertConstruction.Dual.Data.DualAbelianData B)
  (m : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme.Isogeny B DB.abelian)
  (σ : AbelianModuli.ReferenceFamily.ActionData.IntegralAction R B) (level : B.FullLevel N)
  (f : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme.Isogeny P.abelian B) (n : ℕ)
  (hσ : ∀ a : R, (TateComparison.PELAdapters.actionFromEnd P.action).map a ≫ f.hom = f.hom ≫ σ.map a)
  (hp : f.hom ≫ m.hom ≫ FrobeniusKernel.PicardPullback.Construction.IntrinsicPicardPullback.dualMap f.hom P.dual DB = P.polarizationMap.hom ^ n)
  (hlevel : ∀ (T : Over (Spec (.of k)))
    (c : LocallyConstant T.left (Multiplicative (Fin (2 * g) → ZMod N))),
    (level.hom.app (.op T) c).val = (P.marking.hom.app (.op T) c).val ≫ f.hom)

def picardQuotientPELIsogeny : TateComparison.PELIsogenies.PELIsogeny P (picardQuotientFamily B DB m σ level) n where
  isogeny := f
  dualHom := FrobeniusKernel.PicardPullback.Construction.IntrinsicPicardPullback.dualMap f.hom P.dual DB
  dualGroup := FrobeniusKernel.PicardGroupMap.Construction.IntrinsicPicardPullback.dualMap_isMonHom f.hom P.dual DB
  poincare := (FrobeniusKernel.IntrinsicPoincare.Construction.IntrinsicPicardPullback.dualMap_poincare P.dual DB f.hom).symm
  equivariant a := by
    change TateComparison.End.endSchemeMap P.abelian.scheme (P.action a) ≫ f.hom =
      f.hom ≫ TateComparison.End.endSchemeMap B.scheme (TateComparison.PELAdapters.actionToEnd σ a)
    rw [TateComparison.PELAdapters.actionToEnd_schemeMap]
    exact hσ a
  polarization := hp
  marking T c := (hlevel T c).symm

end

end OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Picard.PELFamily.Construction
