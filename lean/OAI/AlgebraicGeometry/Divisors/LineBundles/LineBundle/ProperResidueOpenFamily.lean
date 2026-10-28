import OAI.AlgebraicGeometry.Divisors.LineBundles.LineBundle.ProperResidueOpen
import OAI.AlgebraicGeometry.Divisors.LineBundles.LineBundle.ProperResidueSupport
import OAI.AlgebraicGeometry.Divisors.LineBundles.Finite.FamilyReindex
import OAI.AlgebraicGeometry.Divisors.LineBundles.Finite.FamilyMap

/-! # Proper Residue Open Family -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles.LineBundle.ProperResidueOpenFamily.Cycles

noncomputable section

/-! # LineBundleCycles: the entire actual finite proper-intersection difference commutes with open restriction -/

open _root_.AlgebraicGeometry _root_.CategoryTheory _root_.TopologicalSpace _root_.Order

variable {X Y : Scheme.{0}} (i : Y ⟶ X) [IsOpenImmersion i]

def openCodimensionOneEmbedding : {y : Y // coheight y = 1} ↪ {x : X // coheight x = 1} where
  toFun y := ⟨i y, (coheight_eq_of_isOpenImmersion i).trans y.property⟩
  inj' _ _ h := Subtype.ext (i.isOpenEmbedding.injective (congrArg Subtype.val h))

def openPointCycleRestriction : (X →₀ ℚ) →+ (Y →₀ ℚ) :=
  Finsupp.comapDomain.addMonoidHom i.isOpenEmbedding.injective

variable [IsIntegral X] [IsIntegral Y]
    [AlgebraicGeometry.IsNoetherian X] [AlgebraicGeometry.IsNoetherian Y]
    (L : LineBundles.Scheme.SchemeIdealModule.BundleCycles.SchemeLineBundle X) (a g : X.functionFieldˣ)
    (hproper : Disjoint (L.rationalSectionPointDivisorWithCoefficient a).support (Ord.BundleCycles.principalDivisor X g.val).support)
    (hNormal : ∀ x : X, IsIntegrallyClosed (X.presheaf.stalk x))
    (hNormalY : ∀ y : Y, IsIntegrallyClosed (Y.presheaf.stalk y))

def openRestrictedProperResidueFamily : {x : X // coheight x = 1} →₀ (Y →₀ ℚ) :=
  (ProperResidueFamily.Cycles.properLineBundleResidueFamily L a g hproper hNormal).mapRange
    (openPointCycleRestriction i) (openPointCycleRestriction i).map_zero

theorem openRestrictedProperResidueFamily_comap :
    Finsupp.comapDomain (openCodimensionOneEmbedding i)
        (openRestrictedProperResidueFamily i L a g hproper hNormal)
        (openCodimensionOneEmbedding i).injective.injOn =
      ProperResidueFamily.Cycles.properLineBundleResidueFamily (L.pullback i) (L.openPullbackSectionCoefficient i a)
        (Open.FunctionFieldUnits.BundleCycles.openFunctionFieldUnits i g) (ProperResidueOpen.Cycles.openProperSection L i a g hproper) hNormalY := by
  ext y z
  exact congrArg (fun c : Y →₀ ℚ => c z)
    (ProperResidueOpen.Cycles.properLineBundleResidueContribution_open L i a g hproper hNormal hNormalY y)

omit hNormalY [IsIntegral Y] [AlgebraicGeometry.IsNoetherian Y] in
theorem openRestrictedProperResidueFamily_support :
    ((openRestrictedProperResidueFamily i L a g hproper hNormal).support : Set {x : X // coheight x = 1}) ⊆
      Set.range (openCodimensionOneEmbedding i) := by
  intro x hx
  have him : x.val ∈ Set.range i := by
    by_contra hn
    exact (Finsupp.mem_support_iff.mp hx)
      (ProperResidueSupport.Cycles.properLineBundleResidueContribution_open_off_image i L a g hproper hNormal x hn)
  obtain ⟨y, hy⟩ := him
  have hc : coheight y = 1 := (coheight_eq_of_isOpenImmersion i).symm.trans
    ((congrArg coheight hy).trans x.property)
  exact ⟨⟨y, hc⟩, Subtype.ext hy⟩

theorem properLineBundleResidueCycle_open :
    Finsupp.comapDomain i (ProperResidueFamily.Cycles.properLineBundleResidueCycle L a g hproper hNormal) i.isOpenEmbedding.injective.injOn =
      ProperResidueFamily.Cycles.properLineBundleResidueCycle (L.pullback i) (L.openPullbackSectionCoefficient i a)
        (Open.FunctionFieldUnits.BundleCycles.openFunctionFieldUnits i g) (ProperResidueOpen.Cycles.openProperSection L i a g hproper) hNormalY := by
  let F := ProperResidueFamily.Cycles.properLineBundleResidueFamily L a g hproper hNormal
  let C := openPointCycleRestriction i
  let G := openRestrictedProperResidueFamily i L a g hproper hNormal
  have hm := Finite.FamilyMap.BundleCycles.finiteFamily_sum_map F C
  have hs := Finite.FamilyReindex.BundleCycles.finiteFamily_sum_comap (openCodimensionOneEmbedding i) G
    (openRestrictedProperResidueFamily_support i L a g hproper hNormal)
  have he := openRestrictedProperResidueFamily_comap i L a g hproper hNormal hNormalY
  change C (F.sum (fun _ m => m)) = _
  exact hm.symm.trans (hs.trans (congrArg (fun f => f.sum (fun _ m => m)) he))

end

end OAI.AlgebraicGeometry.Divisors.LineBundles.LineBundle.ProperResidueOpenFamily.Cycles
