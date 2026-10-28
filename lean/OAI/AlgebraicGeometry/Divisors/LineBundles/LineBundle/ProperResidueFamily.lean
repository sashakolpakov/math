import OAI.AlgebraicGeometry.Divisors.LineBundles.LineBundle.ProperResidueContribution
import OAI.AlgebraicGeometry.Divisors.LineBundles.ResidueBoundaryAddition
import OAI.AlgebraicGeometry.Divisors.LineBundles.Global.NormalReciprocity

/-! # Proper Residue Family -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles.LineBundle.ProperResidueFamily.Cycles

noncomputable section

section

/-! # LineBundleCycles: the actual finite proper-intersection difference and its reciprocity in a global frame -/

open _root_.AlgebraicGeometry _root_.CategoryTheory _root_.TopologicalSpace _root_.Order

variable {X : Scheme.{0}} [IsIntegral X] [AlgebraicGeometry.IsNoetherian X]
    (L : LineBundles.Scheme.SchemeIdealModule.BundleCycles.SchemeLineBundle X) (a g : X.functionFieldˣ)
    (hproper : Disjoint (L.rationalSectionPointDivisorWithCoefficient a).support (Ord.BundleCycles.principalDivisor X g.val).support)
    (hNormal : ∀ x : X, IsIntegrallyClosed (X.presheaf.stalk x))

def properLineBundleResidueSupport : Finset X := by
  classical
  exact (L.rationalSectionPointDivisorWithCoefficient a).support ∪ (Ord.BundleCycles.principalDivisor X g.val).support

theorem properLineBundleResidueContribution_off_support (x : {x : X // coheight x = 1})
    (hx : x.val ∉ properLineBundleResidueSupport L a g) :
    ProperResidueContribution.Cycles.properLineBundleResidueContribution L a g hproper hNormal x = 0 := by
  classical
  have ha : L.rationalSectionPointDivisorWithCoefficient a x = 0 :=
    Finsupp.notMem_support_iff.mp (fun h => hx (Finset.mem_union_left _ h))
  have hg : X.ord g.val x = 0 :=
    Finsupp.notMem_support_iff.mp (fun h => hx (Finset.mem_union_right _ h))
  rw [ProperResidueContribution.Cycles.properLineBundleResidueContribution_zero_section L a g hproper hNormal x ha, hg, zero_smul]

theorem properLineBundleResidueContribution_finite :
    {x : {x : X // coheight x = 1} | ProperResidueContribution.Cycles.properLineBundleResidueContribution L a g hproper hNormal x ≠ 0}.Finite := by
  have hs : {x : {x : X // coheight x = 1} | x.val ∈ properLineBundleResidueSupport L a g}.Finite :=
    (properLineBundleResidueSupport L a g).finite_toSet.preimage Subtype.val_injective.injOn
  apply hs.subset
  intro x hx
  by_contra hn
  exact hx (properLineBundleResidueContribution_off_support L a g hproper hNormal x hn)

def properLineBundleResidueFamily : {x : X // coheight x = 1} →₀ (X →₀ ℚ) :=
  Finsupp.ofSupportFinite (ProperResidueContribution.Cycles.properLineBundleResidueContribution L a g hproper hNormal)
    (properLineBundleResidueContribution_finite L a g hproper hNormal)

def properLineBundleResidueCycle : X →₀ ℚ :=
  ResidueBoundaryAddition.BundleCycles.residueFamilySum X (properLineBundleResidueFamily L a g hproper hNormal)

theorem properLineBundleResidueFamily_globalFrame (e : L.sheaf ≅ DivisorClass.Chern.Line.Bundles.Construction.structureModule X) :
    properLineBundleResidueFamily L a g hproper hNormal =
      ResidueCycleFamily.BundleCycles.normalResidueCycleFamily X hNormal (a * GlobalCoordinate.Cycles.lineBundleGlobalRationalCoefficient e) g := by
  ext x
  exact congrArg (fun z : X →₀ ℚ => z _) (ProperResidueContribution.Cycles.properLineBundleResidueContribution_globalFrame L a g hproper hNormal e x)

theorem properLineBundleResidueCycle_globalFrame (e : L.sheaf ≅ DivisorClass.Chern.Line.Bundles.Construction.structureModule X)
    (f : X ⟶ Foundations.Scheme.ProjectiveSpace.complexBase) [LocallyOfFiniteType f] :
    properLineBundleResidueCycle L a g hproper hNormal = 0 := by
  unfold properLineBundleResidueCycle
  rw [properLineBundleResidueFamily_globalFrame L a g hproper hNormal e,
    ResidueBoundaryAddition.BundleCycles.residueFamilySum_eq_boundary,
    Global.NormalReciprocity.BundleCycles.normalResidueBoundaryCycle_zero X hNormal f (a * GlobalCoordinate.Cycles.lineBundleGlobalRationalCoefficient e) g]

end

/-! # LineBundleCycles: the actual finite divisor supports compute the complete proper-intersection difference -/

open _root_.AlgebraicGeometry _root_.CategoryTheory _root_.TopologicalSpace _root_.Order

variable {X : Scheme.{0}} [IsIntegral X] [AlgebraicGeometry.IsNoetherian X]
    (L : LineBundles.Scheme.SchemeIdealModule.BundleCycles.SchemeLineBundle X) (a g : X.functionFieldˣ)

theorem rationalSectionWithCoefficient_support_coheight (x : X)
    (hx : x ∈ (L.rationalSectionPointDivisorWithCoefficient a).support) : coheight x = 1 := by
  by_contra hc
  apply Finsupp.mem_support_iff.mp hx
  rw [L.rationalSectionPointDivisorWithCoefficient_apply]
  exact Scheme.ord_eq_zero_of_coheight_neq_one hc _

theorem properLineBundleResidueSupport_coheight (x : properLineBundleResidueSupport L a g) :
    coheight x.val = 1 := by
  classical
  rcases Finset.mem_union.mp x.property with hx | hx
  · exact rationalSectionWithCoefficient_support_coheight L a x hx
  · exact Normal.PointResidue.BundleCycles.principalDivisor_support_coheight X g.val x hx

variable (hproper : Disjoint (L.rationalSectionPointDivisorWithCoefficient a).support (Ord.BundleCycles.principalDivisor X g.val).support)
    (hNormal : ∀ x : X, IsIntegrallyClosed (X.presheaf.stalk x))

theorem properLineBundleResidueCycle_sum :
    properLineBundleResidueCycle L a g hproper hNormal =
      ∑ x : properLineBundleResidueSupport L a g,
        ProperResidueContribution.Cycles.properLineBundleResidueContribution L a g hproper hNormal
          ⟨x, properLineBundleResidueSupport_coheight L a g x⟩ := by
  let e : properLineBundleResidueSupport L a g ↪ {x : X // coheight x = 1} :=
    ⟨fun x => ⟨x, properLineBundleResidueSupport_coheight L a g x⟩,
      fun _ _ h => Subtype.ext (congrArg (fun z : {x : X // coheight x = 1} => z.val) h)⟩
  have hs : ((properLineBundleResidueFamily L a g hproper hNormal).support : Set {x : X // coheight x = 1}) ⊆
      Set.range e := by
    intro x hx
    have hm : x.val ∈ properLineBundleResidueSupport L a g := by
      by_contra hn
      exact (Finsupp.mem_support_iff.mp hx)
        (properLineBundleResidueContribution_off_support L a g hproper hNormal x hn)
    exact ⟨⟨x, hm⟩, Subtype.ext rfl⟩
  exact LineBundles.Finite.FamilyReindex.BundleCycles.finiteFamily_sum_embedding e (properLineBundleResidueFamily L a g hproper hNormal) hs

end

end OAI.AlgebraicGeometry.Divisors.LineBundles.LineBundle.ProperResidueFamily.Cycles
