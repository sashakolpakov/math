import OAI.AlgebraicGeometry.Divisors.LineBundles.LineBundle.ProperResidueOpenFamily
import OAI.AlgebraicGeometry.Divisors.LineBundles.Open.ImmersionNoetherian

/-! # Proper Reciprocity -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles.LineBundle.ProperReciprocity.Cycles

noncomputable section

/-! # LineBundleCycles: reciprocity for actual proper intersection with an arbitrary algebraic line bundle -/

open _root_.AlgebraicGeometry _root_.CategoryTheory _root_.TopologicalSpace

variable {X : Scheme.{0}} [IsIntegral X] [AlgebraicGeometry.IsNoetherian X]
    (L : LineBundles.Scheme.SchemeIdealModule.BundleCycles.SchemeLineBundle X) (a g : X.functionFieldˣ)
    (hproper : Disjoint (L.rationalSectionPointDivisorWithCoefficient a).support (Ord.BundleCycles.principalDivisor X g.val).support)
    (hNormal : ∀ x : X, IsIntegrallyClosed (X.presheaf.stalk x))
    (f : X ⟶ Foundations.Scheme.ProjectiveSpace.complexBase) [LocallyOfFiniteType f]

include f in
theorem properLineBundleResidueCycle_zero : ProperResidueFamily.Cycles.properLineBundleResidueCycle L a g hproper hNormal = 0 := by
  ext x
  let U := L.trivializingOpen x
  let : Nonempty U := ⟨⟨x, L.mem_trivializingOpen x⟩⟩
  let : IsIntegral U.toScheme := isIntegral_of_isOpenImmersion U.ι
  let : AlgebraicGeometry.IsNoetherian U.toScheme := Open.ImmersionNoetherian.BundleCycles.openImmersion_isNoetherian U.ι
  let e : (L.pullback U.ι).sheaf ≅ DivisorClass.Chern.Line.Bundles.Construction.structureModule U.toScheme :=
    (L.restrictToOpenPullbackIso U.ι).symm ≪≫ L.trivialization x
  let hN := Normal.RestrictionOpenDivisor.BundleCycles.openNormalStructure U.ι hNormal
  let hp := ProperResidueOpen.Cycles.openProperSection L U.ι a g hproper
  have ho := ProperResidueOpenFamily.Cycles.properLineBundleResidueCycle_open U.ι L a g hproper hNormal hN
  have hz := ProperResidueFamily.Cycles.properLineBundleResidueCycle_globalFrame (L.pullback U.ι)
    (L.openPullbackSectionCoefficient U.ι a) (Open.FunctionFieldUnits.BundleCycles.openFunctionFieldUnits U.ι g) hp hN e (U.ι ≫ f)
  exact congrArg (fun c : U.toScheme →₀ ℚ => c ⟨x, L.mem_trivializingOpen x⟩) (ho.trans hz)

end

end OAI.AlgebraicGeometry.Divisors.LineBundles.LineBundle.ProperReciprocity.Cycles
