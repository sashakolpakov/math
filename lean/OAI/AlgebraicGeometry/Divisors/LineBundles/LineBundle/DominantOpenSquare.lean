import OAI.AlgebraicGeometry.Divisors.LineBundles.LineBundle.DominantCoefficientOnReference
import OAI.AlgebraicGeometry.Divisors.LineBundles.LineBundle.GenericRegularRepresentative
import OAI.AlgebraicGeometry.Divisors.LineBundles.LineBundle.OpenSquareCoefficient

/-! # Dominant Open Square -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles.LineBundle.DominantOpenSquare.Cycles

noncomputable section

/-! # LineBundleCycles: actual dominant rational-section pullback commutes with an open restriction square -/

open _root_.AlgebraicGeometry _root_.CategoryTheory

variable {X Y W Z : Scheme.{0}} [IsIntegral X] [IsIntegral Y] [IsIntegral W] [IsIntegral Z]
    (f : X ⟶ Y) (k : W ⟶ X) [IsOpenImmersion k] (j : Z ⟶ Y) [IsOpenImmersion j]
    (q : W ⟶ Z) (hcomm : k ≫ f = q ≫ j)
    (hf : f (genericPoint X) = genericPoint Y) (hq : q (genericPoint W) = genericPoint Z)
    (L : LineBundles.Scheme.SchemeIdealModule.BundleCycles.SchemeLineBundle Y)

theorem dominantPullbackSectionCoefficient_openSquare (a : Y.functionFieldˣ) :
    OpenDivisor.Cycles.lineBundleIsoSectionCoefficient
        (L := (L.pullback f).pullback k) (M := (L.pullback j).pullback q)
        (Module.PullbackSquareSections.BundleCycles.modulePullbackSquareIso f k j q hcomm L.sheaf)
        ((L.pullback f).openPullbackSectionCoefficient k (L.dominantPullbackSectionCoefficient f hf a)) =
      (L.pullback j).dominantPullbackSectionCoefficient q hq (L.openPullbackSectionCoefficient j a) := by
  let D := L.genericRationalSectionUnitNeighborhood a
  let U := D.openSet
  let s := D.localSection
  let V := j ⁻¹ᵁ U
  let S := q ⁻¹ᵁ V
  let := DominantReferencePullback.Cycles.genericPointMap_preimage_nonempty f hf U
  let := DominantReferencePullback.Cycles.genericPointMap_preimage_nonempty j (genericPoint_eq_of_isOpenImmersion j) U
  let := DominantReferencePullback.Cycles.genericPointMap_preimage_nonempty q hq V
  have hp : S ≤ (k ≫ f) ⁻¹ᵁ U := (congrArg (fun m => m ⁻¹ᵁ U) hcomm).ge
  have hs : L.genericSectionCoefficient U s = a.val := L.genericRationalSectionUnitNeighborhood_coefficient a
  have hb := L.genericSectionCoefficient_dominantPullback f hf a U s hs
  have hj := L.genericSectionCoefficient_openPullback_onOpen j a U s hs
  have hsq := OpenSquareCoefficient.Cycles.lineBundleOpenSquare_genericCoefficient f k j q hcomm L U hp s
    (L.dominantPullbackSectionCoefficient f hf a) hb
  have hqg := (L.pullback j).genericSectionCoefficient_dominantPullback q hq
    (L.openPullbackSectionCoefficient j a) V (Module.OpenPullbackSections.BundleCycles.moduleSectionPullbackOnOpen j L.sheaf U s) hj
  apply Units.ext
  exact hsq.symm.trans hqg

end

end OAI.AlgebraicGeometry.Divisors.LineBundles.LineBundle.DominantOpenSquare.Cycles
