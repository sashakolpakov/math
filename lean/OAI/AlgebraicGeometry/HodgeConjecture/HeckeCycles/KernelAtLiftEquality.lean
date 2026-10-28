import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.PELRestrictionNaturality
import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.PointSubgroupCoherence

/-! # Kernel At Lift Equality -/

namespace OAI

noncomputable section

namespace AlgebraicGeometry.HodgeConjecture.HeckeCycles.KernelAtLiftEquality.CM.Restricted

/-! The kernel at a branch of a restricted correspondence is the inverse
image of the original branch's kernel under the actual PEL comparison. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj
open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.PointSubgroupCoherence.CM

variable {R : Type} [CommRing R] {g N : ℕ} {X Y Q Q' Z : Scheme}
  (A : AbelianScheme.TateComparison.PEL.PELFamilyData R g N X) (U : AbelianScheme.TateComparison.PEL.PELFamilyData R g N Y)
  (i : X ⟶ Y) (e : AbelianScheme.TateComparison.PELModuli.PELFamilyIso A (U.pullback i))
  (r : Q' ⟶ Q) (s : Q ⟶ Y) (s' : Q' ⟶ X) (hs : r ≫ s = s' ≫ i)

def atLift (F : AbelianScheme.TateComparison.PEL.PELFamilyData R g N Y) (p : Q ⟶ Y)
    (H : AbelianScheme.TateComparison.Subgroups.PointSubgroup (F.pullback p).abelian)
    (x : Z ⟶ Y) (c : Z ⟶ Q) (w : c ≫ p = x) :
    AbelianScheme.TateComparison.Subgroups.PointSubgroup (F.pullback x).abelian :=
  (H.pullback c).comapHom (AbelianScheme.TateComparison.BaseChangeCoherence.baseChangeFactorIso F.abelian c p x w).hom

theorem restrict_atLift (H : AbelianScheme.TateComparison.Subgroups.PointSubgroup (U.pullback s).abelian)
    (c : Z ⟶ Q') (x : Z ⟶ X) (wc : c ≫ s' = x)
    (hc : (c ≫ r) ≫ s = x ≫ i) :
    atLift A s' ((H.pullback r).comapHom
      (CMExtraction.PEL.PELRestriction.IsogenyQuotient.restrictionFamilyIso A U i e r s s' hs).abelian.hom) x c wc =
    (atLift U s H (x ≫ i) (c ≫ r) hc).comapHom
      (PELRestrictionNaturality.CM.atPoint A U i e x).abelian.hom := by
  let ea := (AbelianScheme.TateComparison.BaseChangeCoherence.baseChangeFactorIso A.abelian c s' x wc).hom
  let eu := (AbelianScheme.TateComparison.BaseChangeCoherence.baseChangeFactorIso U.abelian (c ≫ r) s (x ≫ i) hc).hom
  let er := (AbelianScheme.TateComparison.BaseChangeCoherence.baseChangeFactorIso (U.abelian.pullback s) c r (c ≫ r) rfl).hom
  let ex := (PELRestrictionNaturality.CM.atPoint A U i e x).abelian.hom
  let es := (CMExtraction.PEL.PELRestriction.IsogenyQuotient.restrictionFamilyIso A U i e r s s' hs).abelian.hom
  let es' := ((CMExtraction.PEL.PELRestriction.IsogenyQuotient.restrictionFamilyIso A U i e r s s' hs).pullback c).abelian.hom
  have hn : ea ≫ es' = (ex ≫ eu) ≫ er :=
    (PELRestrictionNaturality.CM.at_branch A U i e r s s' hs c x wc hc).trans
      (Category.assoc ex eu er).symm
  have hm := PointSubgroupCoherence.CM.pullback_comap (H.pullback r) es c
  have hf := PointSubgroupCoherence.CM.pullback_factor H c r (c ≫ r) rfl
  change (((H.pullback r).comapHom es).pullback c).comapHom ea =
    ((H.pullback (c ≫ r)).comapHom eu).comapHom ex
  calc
    _ = (((H.pullback r).pullback c).comapHom es').comapHom ea :=
      congrArg (fun J => J.comapHom ea) hm
    _ = ((H.pullback r).pullback c).comapHom (ea ≫ es') :=
      PointSubgroupCoherence.CM.comap_comp _ ea _
    _ = ((H.pullback r).pullback c).comapHom ((ex ≫ eu) ≫ er) :=
      AbelianScheme.TateComparison.Subgroups.PointSubgroup.comapHom_congr _ _ _ hn
    _ = (((H.pullback r).pullback c).comapHom er).comapHom (ex ≫ eu) :=
      (PointSubgroupCoherence.CM.comap_comp _ (ex ≫ eu) er).symm
    _ = (H.pullback (c ≫ r)).comapHom (ex ≫ eu) :=
      congrArg (fun J => J.comapHom (ex ≫ eu)) hf
    _ = _ := (PointSubgroupCoherence.CM.comap_comp _ ex eu).symm

end AlgebraicGeometry.HodgeConjecture.HeckeCycles.KernelAtLiftEquality.CM.Restricted

namespace AlgebraicGeometry.HodgeConjecture.HeckeCycles.KernelAtLiftEquality.CM

/-! Equality of actual branch maps and faithful transport through a
group-scheme isomorphism detect the corresponding kernel subgroups. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj

variable {R : Type} [CommRing R] {g N : ℕ} {Y Q Z : Scheme}
  (F : AbelianScheme.TateComparison.PEL.PELFamilyData R g N Y) (p : Q ⟶ Y)
  (H : AbelianScheme.TateComparison.Subgroups.PointSubgroup (F.pullback p).abelian) (x : Z ⟶ Y)

theorem branch_congr (c d : Z ⟶ Q) (hc : c ≫ p = x) (hd : d ≫ p = x) (h : c = d) :
    Restricted.atLift F p H x c hc =
      Restricted.atLift F p H x d hd := by
  subst d
  rfl

variable {S : Scheme} {A B : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme g S}
  (e : A.scheme ≅ B.scheme) [IsMonHom e.hom]

theorem comap_inverse (J : AbelianScheme.TateComparison.Subgroups.PointSubgroup B) :
    (J.comapHom e.hom).comapHom e.inv = J := by
  apply AbelianScheme.TateComparison.Subgroups.PointSubgroup.ext
  intro T
  ext z
  change (z ≫ e.inv) ≫ e.hom ∈ J.atTest T ↔ z ∈ J.atTest T
  simp only [Category.assoc, e.inv_hom_id, Category.comp_id]

theorem comap_injective : Function.Injective (fun J : AbelianScheme.TateComparison.Subgroups.PointSubgroup B => J.comapHom e.hom) := by
  intro J K h
  have he := congrArg (fun L => L.comapHom e.inv) h
  exact (comap_inverse e J).symm.trans (he.trans (comap_inverse e K))

end AlgebraicGeometry.HodgeConjecture.HeckeCycles.KernelAtLiftEquality.CM

end

end OAI
