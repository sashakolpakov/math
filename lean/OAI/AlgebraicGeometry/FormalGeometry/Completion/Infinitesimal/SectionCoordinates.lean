import OAI.AlgebraicGeometry.FormalGeometry.Completion.Infinitesimal.CechZeroCycles

/-! # Section Coordinates -/

namespace OAI.AlgebraicGeometry.FormalGeometry.Completion.Infinitesimal.SectionCoordinates.Construction

noncomputable section

/-! Coordinates of the actual infinitesimal global-section to reduced-zero-cycle equivalence. -/

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

/-- The actual R-linear chart projection of the native Cech term. -/
def relativeCechProjection (q : ℕ) (a : SheafCohomology.Projective.OrderedBaseCech.Scheme.Modules.OrderedCechIndex ι q) :
    (RelativeCechZeroCycles.Construction.relativeStructureCechComplex f U).X q →ₗ[R] RelativeCechTerms.Construction.relativeCechFactor f U q a :=
  ((RelativeCechTerms.Construction.relativeStructureCechTermIso f U q).hom ≫ Pi.π (RelativeCechTerms.Construction.relativeCechFactor f U q) a).hom

/-- The reduced zero-cycle coordinate is the literal restriction of the actual global section. -/
theorem infinitesimalSectionsZeroCyclesEquiv_coordinate (n : ℕ)
    (s : (RelativeStructureSections.Construction.relativeStructureSections (pullback.fst f (Neighborhoods.Construction.infinitesimalBaseToSpec I n) ≫ f)).obj (op ⊤))
    (a : SheafCohomology.Projective.OrderedBaseCech.Scheme.Modules.OrderedCechIndex ι 0) :
    (CechTerms.Construction.infinitesimalCechFactorIso I f U hU n 0 a).hom
        ((relativeCechProjection f U 0 a).reduceModIdeal (I ^ (n + 1))
          (CechZeroCycles.Construction.infinitesimalSectionsZeroCyclesEquiv I f U hU hcover n s).val) =
      (Neighborhoods.Construction.infinitesimalNeighborhood I f n).presheaf.map
        (homOfLE (show (∏ᶜ fun k : Fin 1 =>
          pullback.fst f (Neighborhoods.Construction.infinitesimalBaseToSpec I n) ⁻¹ᵁ U (a.val k)) ≤ ⊤ from le_top)).op s := by
  let g := pullback.fst f (Neighborhoods.Construction.infinitesimalBaseToSpec I n)
  let V := fun i => g ⁻¹ᵁ U i
  let y := CechZeroCycles.Construction.infinitesimalSectionsZeroCyclesEquiv I f U hU hcover n s
  let z := RelativeCechZeroCycles.Construction.relativeStructureGlobalSectionsEquiv (g ≫ f) V
    (CechZeroCycles.Construction.infinitesimalCechCover_covers I f U hcover n) s
  have he := ConcreteCategory.congr_hom (CechCoordinates.Construction.infinitesimalCechTermIso_hom_π I f U hU n 0 a) y.val
  change Pi.π (RelativeCechTerms.Construction.relativeCechFactor (g ≫ f) V 0) a
    ((RelativeCechTerms.Construction.relativeStructureCechTermIso (g ≫ f) V 0).hom
      ((CechTerms.Construction.infinitesimalCechTermIso I f U hU n 0).hom y.val)) =
      (CechTerms.Construction.infinitesimalCechFactorIso I f U hU n 0 a).hom
        ((relativeCechProjection f U 0 a).reduceModIdeal (I ^ (n + 1)) y.val) at he
  have hy : (CechTerms.Construction.infinitesimalCechTermIso I f U hU n 0).hom y.val = z.val :=
    CechZeroCycles.Construction.infinitesimalSectionsZeroCyclesEquiv_value I f U hU hcover n s
  rw [hy] at he
  exact he.symm.trans ((RelativeCechTerms.Construction.relativeStructureCechTermIso_coordinate (g ≫ f) V 0 z.val a).trans
    (RelativeCechZeroCycles.Construction.relativeStructureGlobalSectionsEquiv_coordinate (g ≫ f) V
      (CechZeroCycles.Construction.infinitesimalCechCover_covers I f U hcover n) s a))

end

end OAI.AlgebraicGeometry.FormalGeometry.Completion.Infinitesimal.SectionCoordinates.Construction
