import OAI.AlgebraicGeometry.Divisors.LineBundles.StalkSupportDivisor
import OAI.AlgebraicGeometry.Divisors.LineBundles.Finite.FamilyMap

/-! # Stalk Residue Family -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles.StalkResidueFamily.BundleCycles

noncomputable section

section

/-!
# LineBundleCycles: the actual residue family restricted to a stalk spectrum

The finite family is mapped by coefficient restriction. Its terms at
points in the stalk spectrum are the proved local residue contributions;
terms outside that spectrum restrict to zero by specialization.
-/

open _root_.AlgebraicGeometry _root_.CategoryTheory _root_.TopologicalSpace _root_.Order

variable (X : Scheme.{0}) [IsIntegral X] [AlgebraicGeometry.IsNoetherian X]
    (hNormal : ∀ y : X, IsIntegrallyClosed (X.presheaf.stalk y)) (x : X)

abbrev stalkNormalStructure : ∀ p : Spec (X.presheaf.stalk x),
    IsIntegrallyClosed ((Spec (X.presheaf.stalk x)).presheaf.stalk p) :=
  @Affine.ProperReciprocity.BundleCycles.affineNormal_stalk_integrallyClosed (X.presheaf.stalk x) inferInstance inferInstance (hNormal x)

def stalkRationalUnit (g : X.functionFieldˣ) : (Spec (X.presheaf.stalk x)).functionFieldˣ :=
  Units.map (StalkRationalOrder.BundleCycles.stalkFunctionFieldMap X x).hom.toMonoidHom g

def stalkPointCycleRestriction : (X →₀ ℚ) →+ (Spec (X.presheaf.stalk x) →₀ ℚ) :=
  Finsupp.comapDomain.addMonoidHom (X.fromSpecStalk x).isEmbedding.injective

def stalkRestrictedResidueFamily (g h : X.functionFieldˣ) :
    {y : X // coheight y = 1} →₀ (Spec (X.presheaf.stalk x) →₀ ℚ) :=
  (ResidueCycleFamily.BundleCycles.normalResidueCycleFamily X hNormal g h).mapRange (stalkPointCycleRestriction X x)
    (stalkPointCycleRestriction X x).map_zero

def stalkResidueDivisorEmbedding (g h : X.functionFieldˣ) :
    Normal.PointResidue.BundleCycles.residueDivisorSupport (Spec (X.presheaf.stalk x)) (stalkRationalUnit X x g) (stalkRationalUnit X x h) ↪
      {y : X // coheight y = 1} where
  toFun p := ⟨X.fromSpecStalk x p,
    (StalkLocalization.BundleCycles.fromSpecStalk_coheight X x p).trans (Normal.PointResidue.BundleCycles.residueDivisorSupport_coheight (Spec (X.presheaf.stalk x))
      (stalkRationalUnit X x g) (stalkRationalUnit X x h) p)⟩
  inj' _ _ he := Subtype.ext ((X.fromSpecStalk x).isEmbedding.injective
    (congrArg (fun q : {y : X // coheight y = 1} => (q : X)) he))

theorem stalkRestrictedResidueFamily_at_source (g h : X.functionFieldˣ)
    (p : Spec (X.presheaf.stalk x)) (hp : coheight p = 1) :
    stalkRestrictedResidueFamily X hNormal x g h
      ⟨X.fromSpecStalk x p, (StalkLocalization.BundleCycles.fromSpecStalk_coheight X x p).trans hp⟩ =
      ResidueCycleFamily.BundleCycles.normalResidueContribution (Spec (X.presheaf.stalk x)) (stalkNormalStructure X hNormal x)
        (stalkRationalUnit X x g) (stalkRationalUnit X x h) ⟨p, hp⟩ :=
  StalkSupportDivisor.BundleCycles.normalResidueContribution_fromSpecStalk X x p hNormal hp g h

theorem stalkRestrictedResidueFamily_off_image (g h : X.functionFieldˣ)
    (y : {y : X // coheight y = 1}) (hy : (y : X) ∉ Set.range (X.fromSpecStalk x)) :
    stalkRestrictedResidueFamily X hNormal x g h y = 0 := by
  let := hNormal y
  ext p
  change Graded.GlobalSpecialization.BundleCycles.schemePrincipalPointDivisor (irreducibleSetEquivPoints.symm (y : X))
    (Normal.PointResidue.BundleCycles.normalPointResidueFunction X y y.2 g h) (X.fromSpecStalk x p) = 0
  apply Open.PrincipalRestriction.BundleCycles.schemePrincipalPointDivisor_off_support
  intro hm
  have hs : (y : X) ⤳ X.fromSpecStalk x p := specializes_iff_mem_closure.mpr hm
  have hp : X.fromSpecStalk x p ⤳ x := by
    have hm : X.fromSpecStalk x p ∈ Set.range (X.fromSpecStalk x) := ⟨p, rfl⟩
    rw [Scheme.range_fromSpecStalk] at hm
    exact hm
  apply hy
  rw [Scheme.range_fromSpecStalk]
  exact hs.trans hp

end

section

/-!
# LineBundleCycles: the local divisor support covers the entire restricted residue family
-/

open _root_.AlgebraicGeometry _root_.CategoryTheory _root_.TopologicalSpace _root_.Order

variable (X : Scheme.{0}) [IsIntegral X] [AlgebraicGeometry.IsNoetherian X]
    (hNormal : ∀ y : X, IsIntegrallyClosed (X.presheaf.stalk y)) (x : X)

theorem stalkRestrictedResidueFamily_support_subset (g h : X.functionFieldˣ) :
    ((stalkRestrictedResidueFamily X hNormal x g h).support : Set {y : X // coheight y = 1}) ⊆
      Set.range (stalkResidueDivisorEmbedding X x g h) := by
  intro y hy
  have hyr : (y : X) ∈ Set.range (X.fromSpecStalk x) := by
    by_contra hn
    exact (Finsupp.mem_support_iff.mp hy) (stalkRestrictedResidueFamily_off_image X hNormal x g h y hn)
  obtain ⟨p, hp⟩ := hyr
  have hc : coheight p = 1 := (StalkLocalization.BundleCycles.fromSpecStalk_coheight X x p).symm.trans
    ((congrArg coheight hp).trans y.2)
  have he := stalkRestrictedResidueFamily_at_source X hNormal x g h p hc
  have hey : (⟨X.fromSpecStalk x p, (StalkLocalization.BundleCycles.fromSpecStalk_coheight X x p).trans hc⟩ : {y : X // coheight y = 1}) = y :=
    Subtype.ext hp
  rw [hey] at he
  have hm : p ∈ Normal.PointResidue.BundleCycles.residueDivisorSupport (Spec (X.presheaf.stalk x))
      (stalkRationalUnit X x g) (stalkRationalUnit X x h) := by
    by_contra hn
    exact (Finsupp.mem_support_iff.mp hy) (he.trans
      (ResidueCycleFamily.BundleCycles.normalResidueContribution_eq_zero (Spec (X.presheaf.stalk x)) (stalkNormalStructure X hNormal x)
        (stalkRationalUnit X x g) (stalkRationalUnit X x h) ⟨p, hc⟩ hn))
  exact ⟨⟨p, hm⟩, Subtype.ext hp⟩

end

/-!
# LineBundleCycles: restriction of the complete geometric residue boundary to an actual stalk

The restricted finite family is supported on the actual local divisor
support. Summation and restriction commute, and every term agrees with
the local geometric residue divisor.
-/

open _root_.AlgebraicGeometry _root_.CategoryTheory _root_.TopologicalSpace _root_.Order
open scoped Classical

variable (X : Scheme.{0}) [IsIntegral X] [AlgebraicGeometry.IsNoetherian X]
    (hNormal : ∀ y : X, IsIntegrallyClosed (X.presheaf.stalk y)) (x : X)

theorem normalResidueBoundary_fromSpecStalk (g h : X.functionFieldˣ) :
    Finsupp.comapDomain (X.fromSpecStalk x) (Normal.PointResidue.BundleCycles.normalResidueBoundaryCycle X hNormal g h)
      (X.fromSpecStalk x).isEmbedding.injective.injOn =
      Normal.PointResidue.BundleCycles.normalResidueBoundaryCycle (Spec (X.presheaf.stalk x)) (stalkNormalStructure X hNormal x)
        (stalkRationalUnit X x g) (stalkRationalUnit X x h) := by
  let F := ResidueCycleFamily.BundleCycles.normalResidueCycleFamily X hNormal g h
  let C := stalkPointCycleRestriction X x
  let G := stalkRestrictedResidueFamily X hNormal x g h
  let i := stalkResidueDivisorEmbedding X x g h
  have he := Finite.FamilyReindex.BundleCycles.finiteFamily_sum_embedding i G (stalkRestrictedResidueFamily_support_subset X hNormal x g h)
  have hm := Finite.FamilyMap.BundleCycles.finiteFamily_sum_map F C
  have hb := ResidueBoundaryAddition.BundleCycles.residueFamilySum_eq_boundary X hNormal g h
  change F.sum (fun _ m => m) = Normal.PointResidue.BundleCycles.normalResidueBoundaryCycle X hNormal g h at hb
  change G.sum (fun _ m => m) = C (F.sum (fun _ m => m)) at hm
  change C (Normal.PointResidue.BundleCycles.normalResidueBoundaryCycle X hNormal g h) = _
  rw [← hb, ← hm, he]
  unfold Normal.PointResidue.BundleCycles.normalResidueBoundaryCycle
  apply Finset.sum_congr rfl
  intro p _
  exact stalkRestrictedResidueFamily_at_source X hNormal x g h p
    (Normal.PointResidue.BundleCycles.residueDivisorSupport_coheight (Spec (X.presheaf.stalk x)) (stalkRationalUnit X x g) (stalkRationalUnit X x h) p)

theorem normalResidueBoundary_coefficient_zero_of_coheight_two (g h : X.functionFieldˣ)
    (hx : coheight x = 2) : Normal.PointResidue.BundleCycles.normalResidueBoundaryCycle X hNormal g h x = 0 := by
  let := hNormal x
  have he := normalResidueBoundary_fromSpecStalk X hNormal x g h
  have he := he.trans (StalkNormalReciprocity.BundleCycles.normalStalkResidueBoundary_zero X x hx g h)
  have hc := congrArg (fun z : Spec (X.presheaf.stalk x) →₀ ℚ => z (IsLocalRing.closedPoint (X.presheaf.stalk x))) he
  change Normal.PointResidue.BundleCycles.normalResidueBoundaryCycle X hNormal g h
    (X.fromSpecStalk x (IsLocalRing.closedPoint (X.presheaf.stalk x))) = 0 at hc
  rw [Scheme.fromSpecStalk_closedPoint] at hc
  exact hc

end

end OAI.AlgebraicGeometry.Divisors.LineBundles.StalkResidueFamily.BundleCycles
