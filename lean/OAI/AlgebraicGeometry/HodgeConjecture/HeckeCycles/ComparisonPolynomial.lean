import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.AlbaneseModel
import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.EndTransport
import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.GroupBaseChange

/-! # Comparison Polynomial -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.ComparisonPolynomial.CM

noncomputable section

/-! The ordinary Frobenius polynomial transports to GeometricComparison's actual
special fiber through the proved completion/reduction comparison. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj
open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.AlbaneseModel.CM OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.AlbaneseModel.CM.SpecialFiber

variable {E K : Type} [Field E] [NumberField E] [NumberField.IsCMField E]
  [Field K] [NumberField K] {s q : ℕ} [Fact q.Prime]
  (D : AbelianScheme.TateComparison.Data.SphericalPELAlbaneseData E K s q) (hg : D.HasIntegralModelGeometry)
  (j : PELModuli.CMPoints.Arithmetic.QadicChoice K D.complexEmbedding q)
  (hcop : Nat.Coprime q D.denominator)
  (res : AbelianScheme.TateComparison.Data.modelRing K D.denominator →+* ZMod q)
  (hres : res.comp (algebraMap (NumberField.RingOfIntegers K)
    (AbelianScheme.TateComparison.Data.modelRing K D.denominator)) = j.residue)

def sourceGroup : CommGrp (Over (Spec (.of (ZMod q)))) :=
  GroupBaseChange.CM.changedGroup (AbelianScheme.TateComparison.Products.componentProduct D.components.A) (Spec.map (CommRingCat.ofHom res))

def targetGroup : CommGrp (Over (Spec (.of (ZMod q)))) :=
  PELModuli.IntegralModel.Components.commutativeGroupOfAbelianScheme (AlbaneseModel.CM.comparisonModel D hg j hcop).specialFiber

def comparisonIso : (targetGroup D hg j hcop).X ≅ (sourceGroup D res).X :=
  AlbaneseModel.CM.SpecialFiber.albaneseSpecialFiberIso D hg j hcop res hres

local instance : GrpObj (targetGroup D hg j hcop).X := (targetGroup D hg j hcop).grp
local instance : IsCommMonObj (targetGroup D hg j hcop).X := (targetGroup D hg j hcop).comm
local instance : GrpObj (sourceGroup D res).X := (sourceGroup D res).grp
local instance : IsCommMonObj (sourceGroup D res).X := (sourceGroup D res).comm

theorem comparisonIso_group : IsMonHom (comparisonIso D hg j hcop res hres).hom :=
  AlbaneseModel.CM.SpecialFiber.albaneseSpecialFiberIso_group D hg j hcop res hres

local instance : IsMonHom (comparisonIso D hg j hcop res hres).hom :=
  comparisonIso_group D hg j hcop res hres

theorem comparisonIso_inv_group : IsMonHom (comparisonIso D hg j hcop res hres).inv := by
  infer_instance

local instance : IsMonHom (comparisonIso D hg j hcop res hres).symm.hom :=
  comparisonIso_inv_group D hg j hcop res hres

def specialEndTransport : FormalGeometry.Completion.Endomorphisms.Construction.AlgebraicEnd (sourceGroup D res).X ≃+*
    FormalGeometry.Completion.Endomorphisms.Construction.AlgebraicEnd (targetGroup D hg j hcop).X :=
  EndTransport.CM.schemeTransport (sourceGroup D res) (targetGroup D hg j hcop)
    (comparisonIso D hg j hcop res hres).symm

theorem specialFiber_polynomial (T : Fin 3 → FormalGeometry.Completion.Endomorphisms.Construction.AlgebraicEnd (sourceGroup D res).X)
    (h : Ordinary.Polynomial.CM.heckePolynomialValue q
      (FormalGeometry.Completion.Endomorphisms.Construction.algebraicFrobenius (ZMod q) (sourceGroup D res).X) T = 0) :
    Ordinary.Polynomial.CM.heckePolynomialValue q
      (FormalGeometry.Completion.Endomorphisms.Construction.algebraicFrobenius (ZMod q) (targetGroup D hg j hcop).X)
      (fun i => specialEndTransport D hg j hcop res hres (T i)) = 0 :=
  EndTransport.CM.schemeTransport_frobenius_polynomial
    (sourceGroup D res) (targetGroup D hg j hcop) (comparisonIso D hg j hcop res hres).symm q T h

end

end OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.ComparisonPolynomial.CM
