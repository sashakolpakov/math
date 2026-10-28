import OAI.AlgebraicGeometry.FormalGeometry.Completion.Infinitesimal.SectionCoordinates

/-! # Chart Zero Cycles -/

namespace OAI.AlgebraicGeometry.FormalGeometry.Completion.Infinitesimal.ChartZeroCycles.Construction

noncomputable section

/-! The actual reduced zero-cycle coordinates on the inverse images of the original affine charts. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry Opposite
open _root_.AlgebraicGeometry.Scheme.Modules

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

variable {R : Type u} [CommRing R] (I : Ideal R) {X : Scheme.{u}} [X.IsSeparated]
  (f : X ⟶ Spec (CommRingCat.of R))
  {ι : Type u} [LinearOrder ι] [Finite ι] (U : ι → X.Opens)
  (hU : ∀ i, IsAffineOpen (U i)) (hcover : iSup U = ⊤)

/-- The reduced chart coordinate is exactly restriction to the inverse image of that original chart. -/
theorem infinitesimalSectionsZeroCyclesEquiv_chart (n : ℕ)
    (s : (RelativeStructureSections.Construction.relativeStructureSections (pullback.fst f (Neighborhoods.Construction.infinitesimalBaseToSpec I n) ≫ f)).obj (op ⊤))
    (a : SheafCohomology.Projective.OrderedBaseCech.Scheme.Modules.OrderedCechIndex ι 0) :
    (show Γ(Neighborhoods.Construction.infinitesimalNeighborhood I f n,
      pullback.fst f (Neighborhoods.Construction.infinitesimalBaseToSpec I n) ⁻¹ᵁ (∏ᶜ fun k : Fin 1 => U (a.val k))) from
      ChartModules.Construction.affineInfinitesimalSectionsModuleEquiv I f n _ (SheafCohomology.Cech.Cochains.IsAffineOpen.cechIntersection U hU 0 a.val)
        ((SectionCoordinates.Construction.relativeCechProjection f U 0 a).reduceModIdeal (I ^ (n + 1))
          (CechZeroCycles.Construction.infinitesimalSectionsZeroCyclesEquiv I f U hU hcover n s).val)) =
      (Neighborhoods.Construction.infinitesimalNeighborhood I f n).presheaf.map
        (homOfLE (show pullback.fst f (Neighborhoods.Construction.infinitesimalBaseToSpec I n) ⁻¹ᵁ
          (∏ᶜ fun k : Fin 1 => U (a.val k)) ≤ ⊤ from le_top)).op s := by
  let g := pullback.fst f (Neighborhoods.Construction.infinitesimalBaseToSpec I n)
  let P := RelativeStructureSections.Construction.relativeStructureSections (g ≫ f)
  let e := P.mapIso (eqToIso ((SheafCohomology.Cech.SchemeModuleBaseBasic.Scheme.Hom.preimage_cechIntersection g) U 0 a.val)).symm.op
  apply e.toLinearEquiv.injective
  change (CechTerms.Construction.infinitesimalCechFactorIso I f U hU n 0 a).hom
    ((SectionCoordinates.Construction.relativeCechProjection f U 0 a).reduceModIdeal (I ^ (n + 1))
      (CechZeroCycles.Construction.infinitesimalSectionsZeroCyclesEquiv I f U hU hcover n s).val) = _
  rw [SectionCoordinates.Construction.infinitesimalSectionsZeroCyclesEquiv_coordinate]
  have he : P.map (homOfLE (show g ⁻¹ᵁ (∏ᶜ fun k : Fin 1 => U (a.val k)) ≤ ⊤ from le_top)).op ≫
      e.hom = P.map (homOfLE (show (∏ᶜ fun k : Fin 1 => g ⁻¹ᵁ U (a.val k)) ≤ ⊤ from le_top)).op := by
    change P.map _ ≫ P.map _ = P.map _
    rw [← P.map_comp]
    congr 1
  exact (ConcreteCategory.congr_hom he s).symm

end

end OAI.AlgebraicGeometry.FormalGeometry.Completion.Infinitesimal.ChartZeroCycles.Construction
