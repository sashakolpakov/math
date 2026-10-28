import OAI.AlgebraicGeometry.Divisors.LineBundles.LineBundle.ReferenceSection
import OAI.AlgebraicGeometry.Divisors.LineBundles.LineBundle.LocalGeneratorPullback
import OAI.AlgebraicGeometry.Divisors.LineBundles.GenericFieldComposition

/-! # Dominant Reference Pullback -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles

noncomputable section

/-! # LineBundleCycles: actual dominant pullback of the reference rational section is nonzero -/

open _root_.AlgebraicGeometry _root_.CategoryTheory

variable {X Y : Scheme.{0}} [IsIntegral X] [IsIntegral Y]
    (f : X ⟶ Y) (hη : f (genericPoint X) = genericPoint Y)

include hη in
theorem LineBundle.DominantReferencePullback.Cycles.genericPointMap_preimage_nonempty (U : Y.Opens) [Nonempty U] : Nonempty (f ⁻¹ᵁ U) := by
  refine ⟨⟨genericPoint X, ?_⟩⟩
  change f (genericPoint X) ∈ U
  rw [hη]
  exact ((genericPoint_spec Y).mem_open_set_iff U.isOpen).mpr (by simpa using ‹Nonempty U›)

variable (L : LineBundles.Scheme.SchemeIdealModule.BundleCycles.SchemeLineBundle Y)

def Scheme.SchemeIdealModule.BundleCycles.SchemeLineBundle.dominantPullbackReferenceCoefficient : X.functionFieldˣ :=
  letI := LineBundle.DominantReferencePullback.Cycles.genericPointMap_preimage_nonempty f hη L.referenceUnitNeighborhood.openSet
  LineBundle.LocalGeneratorPullback.Cycles.lineBundleLocalGeneratorPullbackCoefficient f L L.referenceUnitNeighborhood.openSet L.referenceUnitNeighborhood.trivialization
    L.referenceUnitNeighborhood.localSection (by rw [L.referenceUnitNeighborhood.trivialization_generator]; exact isUnit_one)

theorem Scheme.SchemeIdealModule.BundleCycles.SchemeLineBundle.dominantPullbackReferenceCoefficient_apply :
    letI := LineBundle.DominantReferencePullback.Cycles.genericPointMap_preimage_nonempty f hη L.rationalReferenceOpen
    (L.dominantPullbackReferenceCoefficient f hη).val =
      (L.pullback f).genericSectionCoefficient (f ⁻¹ᵁ L.rationalReferenceOpen)
        (Module.OpenPullbackSections.BundleCycles.moduleSectionPullbackOnOpen f L.sheaf L.rationalReferenceOpen L.referenceSection) := rfl

def Scheme.SchemeIdealModule.BundleCycles.SchemeLineBundle.dominantPullbackSectionCoefficient (a : Y.functionFieldˣ) : X.functionFieldˣ :=
  Units.map (Cycles.Functoriality.FunctionFields.Construction.genericFieldMap f hη).hom.toMonoidHom a * L.dominantPullbackReferenceCoefficient f hη

end

end OAI.AlgebraicGeometry.Divisors.LineBundles
