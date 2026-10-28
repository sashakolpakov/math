import OAI.AlgebraicGeometry.FormalGeometry.Completion.Infinitesimal.ChartZeroCycles
import OAI.AlgebraicGeometry.FormalGeometry.Completion.CochainReducedKernels

/-! # Zero Cycle Transitions -/

namespace OAI.AlgebraicGeometry.FormalGeometry.Completion.Infinitesimal.ZeroCycleTransitions.Construction

noncomputable section

/-! Actual infinitesimal section transitions agree with the reduced Cech zero-cycle transitions. -/

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

omit [X.IsSeparated] in
/-- The actual chart projections detect equality even after reduction by an arbitrary ideal. -/
theorem relativeCechReducedCoordinates_ext (q : ℕ)
    (x y : (RelativeCechZeroCycles.Construction.relativeStructureCechComplex f U).X q ⧸
      (I • ⊤ : Submodule R ((RelativeCechZeroCycles.Construction.relativeStructureCechComplex f U).X q)))
    (h : ∀ a : SheafCohomology.Projective.OrderedBaseCech.Scheme.Modules.OrderedCechIndex ι q,
      (SectionCoordinates.Construction.relativeCechProjection f U q a).reduceModIdeal I x =
        (SectionCoordinates.Construction.relativeCechProjection f U q a).reduceModIdeal I y) : x = y := by
  have : Finite (SheafCohomology.Projective.OrderedBaseCech.Scheme.Modules.OrderedCechIndex ι q) := inferInstanceAs (Finite {i : Fin (q + 1) → ι // StrictMono i})
  let F := AdicReduction.Construction.adicReductionFunctor I
  let e := F.mapIso (RelativeCechTerms.Construction.relativeStructureCechTermIso f U q) ≪≫
    PreservesProduct.iso F (RelativeCechTerms.Construction.relativeCechFactor f U q)
  have he (a : SheafCohomology.Projective.OrderedBaseCech.Scheme.Modules.OrderedCechIndex ι q) : e.hom ≫
      Pi.π (fun b => F.obj (RelativeCechTerms.Construction.relativeCechFactor f U q b)) a =
        F.map ((RelativeCechTerms.Construction.relativeStructureCechTermIso f U q).hom ≫ Pi.π (RelativeCechTerms.Construction.relativeCechFactor f U q) a) := by
    change (F.map (RelativeCechTerms.Construction.relativeStructureCechTermIso f U q).hom ≫
      (PreservesProduct.iso F (RelativeCechTerms.Construction.relativeCechFactor f U q)).hom) ≫ _ = _
    rw [Category.assoc, PreservesProduct.iso_hom, piComparison_comp_π, ← F.map_comp]
  apply e.toLinearEquiv.injective
  apply (ModuleCat.piIsoPi _).toLinearEquiv.injective
  funext a
  change (Pi.π (fun b => F.obj (RelativeCechTerms.Construction.relativeCechFactor f U q b)) a) (e.hom x) =
    (Pi.π (fun b => F.obj (RelativeCechTerms.Construction.relativeCechFactor f U q b)) a) (e.hom y)
  exact (ConcreteCategory.congr_hom (he a) x).trans
    ((h a).trans (ConcreteCategory.congr_hom (he a) y).symm)

/-- The degree-zero equivalence respects the literal infinitesimal pullback on global sections. -/
theorem infinitesimalSectionsZeroCyclesEquiv_transition (n : ℕ)
    (s : (RelativeStructureSections.Construction.relativeStructureSections (pullback.fst f (Neighborhoods.Construction.infinitesimalBaseToSpec I (n + 1)) ≫ f)).obj (op ⊤)) :
    CochainReducedKernels.Construction.reducedCycleTransition I (RelativeCechZeroCycles.Construction.relativeStructureCechComplex f U) (Nat.le_succ (n + 1))
        (CechZeroCycles.Construction.infinitesimalSectionsZeroCyclesEquiv I f U hU hcover (n + 1) s) =
      CechZeroCycles.Construction.infinitesimalSectionsZeroCyclesEquiv I f U hU hcover n
        ((Neighborhoods.Construction.infinitesimalTransition I f n).appTop s) := by
  let C := RelativeCechZeroCycles.Construction.relativeStructureCechComplex f U
  let y := CechZeroCycles.Construction.infinitesimalSectionsZeroCyclesEquiv I f U hU hcover (n + 1) s
  let t := (Neighborhoods.Construction.infinitesimalTransition I f n).appTop s
  apply Subtype.ext
  apply relativeCechReducedCoordinates_ext (I ^ (n + 1)) f U 0
  intro a
  let V := ∏ᶜ fun k : Fin 1 => U (a.val k)
  have hV : IsAffineOpen V := SheafCohomology.Cech.Cochains.IsAffineOpen.cechIntersection U hU 0 a.val
  let p := SectionCoordinates.Construction.relativeCechProjection f U 0 a
  apply (ChartModules.Construction.affineInfinitesimalSectionsModuleEquiv I f n V hV).injective
  have hp : p.reduceModIdeal (I ^ (n + 1))
      (AdicCompletion.transitionMap I (C.X 0) (Nat.le_succ (n + 1)) y.val) =
        AdicCompletion.transitionMap I (RelativeCechTerms.Construction.relativeCechFactor f U 0 a) (Nat.le_succ (n + 1))
          (p.reduceModIdeal (I ^ (n + 1 + 1)) y.val) :=
    (LinearMap.congr_fun (AdicCompletion.transitionMap_comp_reduceModIdeal I p
      (Nat.le_succ (n + 1))) y.val).symm
  calc
    _ = ChartModules.Construction.affineInfinitesimalSectionsModuleEquiv I f n V hV
        (AdicCompletion.transitionMap I (RelativeCechTerms.Construction.relativeCechFactor f U 0 a) (Nat.le_succ (n + 1))
          (p.reduceModIdeal (I ^ (n + 1 + 1)) y.val)) := congrArg _ hp
    _ = ChartTransition.Construction.infinitesimalChartSectionTransition I f n V
        (ChartModules.Construction.affineInfinitesimalSectionsModuleEquiv I f (n + 1) V hV
          (p.reduceModIdeal (I ^ (n + 1 + 1)) y.val)) :=
      ModuleNaturality.Construction.affineInfinitesimalSectionsModuleEquiv_transition I f n V hV _
    _ = ChartTransition.Construction.infinitesimalChartSectionTransition I f n V
        ((Neighborhoods.Construction.infinitesimalNeighborhood I f (n + 1)).presheaf.map
          (homOfLE (show pullback.fst f (Neighborhoods.Construction.infinitesimalBaseToSpec I (n + 1)) ⁻¹ᵁ V ≤ ⊤ from le_top)).op s) :=
      congrArg _ (ChartZeroCycles.Construction.infinitesimalSectionsZeroCyclesEquiv_chart I f U hU hcover (n + 1) s a)
    _ = (Neighborhoods.Construction.infinitesimalNeighborhood I f n).presheaf.map
        (homOfLE (show pullback.fst f (Neighborhoods.Construction.infinitesimalBaseToSpec I n) ⁻¹ᵁ V ≤ ⊤ from le_top)).op t :=
      (ConcreteCategory.congr_hom (ChartTransition.Construction.infinitesimalChartSectionTransition_restrict_top I f n V) s).symm
    _ = _ := (ChartZeroCycles.Construction.infinitesimalSectionsZeroCyclesEquiv_chart I f U hU hcover n t a).symm

end

end OAI.AlgebraicGeometry.FormalGeometry.Completion.Infinitesimal.ZeroCycleTransitions.Construction
