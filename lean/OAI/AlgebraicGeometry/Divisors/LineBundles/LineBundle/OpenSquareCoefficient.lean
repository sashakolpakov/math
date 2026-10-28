import OAI.AlgebraicGeometry.Divisors.LineBundles.LineBundle.OpenPullbackCoefficient
import OAI.AlgebraicGeometry.Divisors.LineBundles.Module.PullbackSquareSections

/-! # Open Square Coefficient -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles.LineBundle.OpenSquareCoefficient.Cycles

noncomputable section

/-! # LineBundleCycles: generic coefficients of actual sections respect the open side of a pullback square -/

open _root_.AlgebraicGeometry _root_.CategoryTheory

variable {X Y Z W : Scheme.{0}} [IsIntegral Y] [IsIntegral W]
    (f : Y ⟶ X) (q : W ⟶ Y) [IsOpenImmersion q] (i : Z ⟶ X) (j : W ⟶ Z)
    (h : q ≫ f = j ≫ i) (L : LineBundles.Scheme.SchemeIdealModule.BundleCycles.SchemeLineBundle X)

theorem lineBundleOpenSquare_genericCoefficient (U : X.Opens)
    [Nonempty (f ⁻¹ᵁ U)] [Nonempty (j ⁻¹ᵁ (i ⁻¹ᵁ U))]
    (hq : j ⁻¹ᵁ (i ⁻¹ᵁ U) ≤ (q ≫ f) ⁻¹ᵁ U)
    (s : Γ(L.sheaf, U)) (b : Y.functionFieldˣ)
    (hb : (L.pullback f).genericSectionCoefficient (f ⁻¹ᵁ U)
      (Module.OpenPullbackSections.BundleCycles.moduleSectionPullbackOnOpen f L.sheaf U s) = b.val) :
    ((L.pullback i).pullback j).genericSectionCoefficient (j ⁻¹ᵁ (i ⁻¹ᵁ U))
        (Module.OpenPullbackSections.BundleCycles.moduleSectionPullbackOnOpen j (L.pullback i).sheaf (i ⁻¹ᵁ U)
          (Module.OpenPullbackSections.BundleCycles.moduleSectionPullbackOnOpen i L.sheaf U s)) =
      (OpenDivisor.Cycles.lineBundleIsoSectionCoefficient
        (L := (L.pullback f).pullback q) (M := (L.pullback i).pullback j)
        (Module.PullbackSquareSections.BundleCycles.modulePullbackSquareIso f q i j h L.sheaf)
        ((L.pullback f).openPullbackSectionCoefficient q b)).val := by
  let V := j ⁻¹ᵁ (i ⁻¹ᵁ U)
  let A := (L.pullback f).pullback q
  let B := (L.pullback i).pullback j
  let e : A.sheaf ≅ B.sheaf := Module.PullbackSquareSections.BundleCycles.modulePullbackSquareIso f q i j h L.sheaf
  let c := IsoCoefficient.Cycles.lineBundleIsoRationalCoefficient (L := A) (M := B) e
  let t := Module.OpenPullbackSections.BundleCycles.moduleSectionPullbackOnOpen i L.sheaf U s
  let u := Module.OpenPullbackSections.BundleCycles.moduleSectionPullbackOnOpen f L.sheaf U s
  let v := Module.SectionPullbackComposition.BundleCycles.moduleSectionPullbackToOpen q (L.pullback f).sheaf (f ⁻¹ᵁ U) V hq u
  have hp := Module.PullbackSquareSections.BundleCycles.modulePullbackSquareIso_section f q i j h L.sheaf U V hq le_rfl s
  have hi := GenericCoefficientIso.Cycles.genericSectionCoefficient_iso
    (L := (L.pullback f).pullback q) (M := (L.pullback i).pullback j) e V v
  have hqg := (L.pullback f).genericSectionCoefficient_openPullback q b (f ⁻¹ᵁ U) V hq u hb
  have hr := ((L.pullback i).pullback j).genericSectionCoefficient_restrict le_rfl
    (Module.OpenPullbackSections.BundleCycles.moduleSectionPullbackOnOpen j (L.pullback i).sheaf (i ⁻¹ᵁ U) t)
  calc
    _ = ((L.pullback i).pullback j).genericSectionCoefficient V
        (Module.SectionPullbackComposition.BundleCycles.moduleSectionPullbackToOpen j (L.pullback i).sheaf (i ⁻¹ᵁ U) V le_rfl t) := hr.symm
    _ = ((L.pullback i).pullback j).genericSectionCoefficient V (e.hom.app V v) :=
      congrArg (((L.pullback i).pullback j).genericSectionCoefficient V) hp.symm
    _ = c.val *
        ((L.pullback f).pullback q).genericSectionCoefficient V v := hi
    _ = _ := (congrArg (fun z => c.val * z) hqg).trans (mul_comm _ _)

end

end OAI.AlgebraicGeometry.Divisors.LineBundles.LineBundle.OpenSquareCoefficient.Cycles
