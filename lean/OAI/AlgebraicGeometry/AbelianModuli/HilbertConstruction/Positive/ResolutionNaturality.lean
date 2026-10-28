import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.SectionsHomologyNaturality
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Sheaf.BoundaryNaturality
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.ResolutionShiftNaturality

/-! # Resolution Naturality -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Positive.ResolutionNaturality.IntrinsicCech

noncomputable section

/-! The positive-degree comparison for an acyclic resolution commutes with
maps of augmented resolutions. -/
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.TopologicalSpace
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
private def rebundleGroupHom {A B : AddCommGrpCat.{u}} (f : A ⟶ B) :
    AddCommGrpCat.of A ⟶ AddCommGrpCat.of B := AddCommGrpCat.ofHom f.hom

private def cohomologyMap {X : TopCat.{u}} {F G : TopCat.Sheaf AddCommGrpCat.{u} X}
    (f : F ⟶ G) (n : ℕ) :
    AddCommGrpCat.of ((CategoryTheory.Sheaf.functorH (Opens.grothendieckTopology X) n : _ ⥤ AddCommGrpCat.{u}).obj F) ⟶
      AddCommGrpCat.of ((CategoryTheory.Sheaf.functorH (Opens.grothendieckTopology X) n : _ ⥤ AddCommGrpCat.{u}).obj G) :=
  rebundleGroupHom ((CategoryTheory.Sheaf.functorH (Opens.grothendieckTopology X) n : _ ⥤ AddCommGrpCat.{u}).map f)

private theorem compose_three_squares {D : Type*} [Category D]
    {A₀ A₁ A₂ A₃ B₀ B₁ B₂ B₃ : D}
    (f₁ : A₀ ⟶ A₁) (f₂ : A₁ ⟶ A₂) (f₃ : A₂ ⟶ A₃)
    (g₁ : B₀ ⟶ B₁) (g₂ : B₁ ⟶ B₂) (g₃ : B₂ ⟶ B₃)
    (z₀ : A₀ ⟶ B₀) (z₁ : A₁ ⟶ B₁) (z₂ : A₂ ⟶ B₂) (z₃ : A₃ ⟶ B₃)
    (h₁ : z₀ ≫ g₁ = f₁ ≫ z₁) (h₂ : z₁ ≫ g₂ = f₂ ≫ z₂)
    (h₃ : z₂ ≫ g₃ = f₃ ≫ z₃) :
    z₀ ≫ (g₁ ≫ g₂ ≫ g₃) = (f₁ ≫ f₂ ≫ f₃) ≫ z₃ := by
  rw [← Category.assoc z₀ g₁, h₁, Category.assoc,
    ← Category.assoc z₁ g₂, h₂, Category.assoc, h₃]
  simp only [Category.assoc]

variable {X : TopCat.{u}}
    {K L : CochainComplex (TopCat.Sheaf AddCommGrpCat.{u} X) ℕ}
    {F G : TopCat.Sheaf AddCommGrpCat.{u} X}
    (eK : F ⟶ K.X 0) (wK : eK ≫ K.d 0 1 = 0) [Mono eK]
    (eL : G ⟶ L.X 0) (wL : eL ≫ L.d 0 1 = 0) [Mono eL]
    (haugK : (ShortComplex.mk eK (K.d 0 1) wK).Exact)
    (haugL : (ShortComplex.mk eL (L.d 0 1) wL).Exact)
    (hposK : ∀ n, (AcyclicSheafResolution.IntrinsicCech.resolutionDifferentialShortComplex K n).Exact)
    (hposL : ∀ n, (AcyclicSheafResolution.IntrinsicCech.resolutionDifferentialShortComplex L n).Exact)
    (hK : ∀ p q, Subsingleton (CategoryTheory.Sheaf.H (K.X p) (q + 1)))
    (hL : ∀ p q, Subsingleton (CategoryTheory.Sheaf.H (L.X p) (q + 1)))
    (f : F ⟶ G) (ψ : K ⟶ L) (hψ : f ≫ eL = eK ≫ ψ.f 0)

include hψ in
private theorem acyclicResolutionPositiveCohomologyIso_naturality_zero :
    HomologicalComplex.homologyMap (SectionsHomologyNaturality.IntrinsicCech.sheafTopSectionsMap ψ) (0 + 1) ≫
        (AcyclicResolutionCohomology.IntrinsicCech.acyclicResolutionPositiveCohomologyIso L eL wL haugL hposL hL 0).hom =
      (AcyclicResolutionCohomology.IntrinsicCech.acyclicResolutionPositiveCohomologyIso K eK wK haugK hposK hK 0).hom ≫
        cohomologyMap f (0 + 1) := by
  have hc := SectionsHomologyNaturality.IntrinsicCech.sheafTopSectionsHomologyCokernelIso_naturality ψ 0
  let bK := HilbertConstruction.Sheaf.BoundaryCokernel.IntrinsicCech.sheafSectionBoundaryCokernelIso
    (AcyclicSheafResolution.IntrinsicCech.initialResolutionCycleSequence_shortExact K eK wK haugK hposK) (hK 0 0)
  let bL := HilbertConstruction.Sheaf.BoundaryCokernel.IntrinsicCech.sheafSectionBoundaryCokernelIso
    (AcyclicSheafResolution.IntrinsicCech.initialResolutionCycleSequence_shortExact L eL wL haugL hposL) (hL 0 0)
  let aK := AcyclicResolutionCohomology.IntrinsicCech.sheafTopSectionsHomologyCokernelIso K 0
  let aL := AcyclicResolutionCohomology.IntrinsicCech.sheafTopSectionsHomologyCokernelIso L 0
  have hb : SectionsHomologyNaturality.IntrinsicCech.sectionsCycleCokernelMap ψ 0 ≫ bL.hom = bK.hom ≫ cohomologyMap f 1 :=
    HilbertConstruction.Sheaf.BoundaryNaturality.IntrinsicCech.sheafSectionBoundaryCokernelIso_naturality
      (AcyclicSheafResolution.IntrinsicCech.initialResolutionCycleSequence_shortExact K eK wK haugK hposK)
      (AcyclicSheafResolution.IntrinsicCech.initialResolutionCycleSequence_shortExact L eL wL haugL hposL)
      (ResolutionCycleMaps.IntrinsicCech.initialResolutionCycleSequenceMap eK wK eL wL f ψ hψ) (hK 0 0) (hL 0 0)
  change HomologicalComplex.homologyMap (SectionsHomologyNaturality.IntrinsicCech.sheafTopSectionsMap ψ) 1 ≫ aL.hom =
    aK.hom ≫ SectionsHomologyNaturality.IntrinsicCech.sectionsCycleCokernelMap ψ 0 at hc
  change HomologicalComplex.homologyMap (SectionsHomologyNaturality.IntrinsicCech.sheafTopSectionsMap ψ) 1 ≫ (aL.hom ≫ bL.hom) =
    (aK.hom ≫ bK.hom) ≫ cohomologyMap f 1
  rw [← Category.assoc, hc, Category.assoc, hb, ← Category.assoc]

include hψ in
private theorem acyclicResolutionPositiveCohomologyIso_naturality_succ (n : ℕ) :
    HomologicalComplex.homologyMap (SectionsHomologyNaturality.IntrinsicCech.sheafTopSectionsMap ψ) (n + 2) ≫
        (AcyclicResolutionCohomology.IntrinsicCech.acyclicResolutionPositiveCohomologyIso L eL wL haugL hposL hL (n + 1)).hom =
      (AcyclicResolutionCohomology.IntrinsicCech.acyclicResolutionPositiveCohomologyIso K eK wK haugK hposK hK (n + 1)).hom ≫
        cohomologyMap f (n + 2) := by
  have hc := SectionsHomologyNaturality.IntrinsicCech.sheafTopSectionsHomologyCokernelIso_naturality ψ (n + 1)
  let bK := HilbertConstruction.Sheaf.BoundaryCokernel.IntrinsicCech.sheafSectionBoundaryCokernelIso
    (AcyclicSheafResolution.IntrinsicCech.successiveResolutionCycleSequence_shortExact K hposK n) (hK (n + 1) 0)
  let bL := HilbertConstruction.Sheaf.BoundaryCokernel.IntrinsicCech.sheafSectionBoundaryCokernelIso
    (AcyclicSheafResolution.IntrinsicCech.successiveResolutionCycleSequence_shortExact L hposL n) (hL (n + 1) 0)
  let dK := (AcyclicResolutionDimensionShift.IntrinsicCech.resolutionCycleCohomologyShift K eK wK haugK hposK hK n 0).toAddCommGrpIso
  let dL := (AcyclicResolutionDimensionShift.IntrinsicCech.resolutionCycleCohomologyShift L eL wL haugL hposL hL n 0).toAddCommGrpIso
  let hm := cohomologyMap (ShortComplex.cyclesMap (ResolutionCycleMaps.IntrinsicCech.resolutionDifferentialShortComplexMap ψ n)) 1
  have hb : SectionsHomologyNaturality.IntrinsicCech.sectionsCycleCokernelMap ψ (n + 1) ≫ bL.hom = bK.hom ≫ hm :=
    HilbertConstruction.Sheaf.BoundaryNaturality.IntrinsicCech.sheafSectionBoundaryCokernelIso_naturality
      (AcyclicSheafResolution.IntrinsicCech.successiveResolutionCycleSequence_shortExact K hposK n)
      (AcyclicSheafResolution.IntrinsicCech.successiveResolutionCycleSequence_shortExact L hposL n)
      (ResolutionCycleMaps.IntrinsicCech.successiveResolutionCycleSequenceMap ψ n) (hK (n + 1) 0) (hL (n + 1) 0)
  have hd : hm ≫ dL.hom = dK.hom ≫
      cohomologyMap f (n + 2) := by
    ext x
    exact ResolutionShiftNaturality.IntrinsicCech.resolutionCycleCohomologyShift_naturality eK wK eL wL haugK haugL
      hposK hposL hK hL f ψ hψ n 0 x
  let aK := AcyclicResolutionCohomology.IntrinsicCech.sheafTopSectionsHomologyCokernelIso K (n + 1)
  let aL := AcyclicResolutionCohomology.IntrinsicCech.sheafTopSectionsHomologyCokernelIso L (n + 1)
  change HomologicalComplex.homologyMap (SectionsHomologyNaturality.IntrinsicCech.sheafTopSectionsMap ψ) (n + 2) ≫ aL.hom =
    aK.hom ≫ SectionsHomologyNaturality.IntrinsicCech.sectionsCycleCokernelMap ψ (n + 1) at hc
  change HomologicalComplex.homologyMap (SectionsHomologyNaturality.IntrinsicCech.sheafTopSectionsMap ψ) (n + 2) ≫
    (aL.hom ≫ bL.hom ≫ dL.hom) =
      (aK.hom ≫ bK.hom ≫ dK.hom) ≫ cohomologyMap f (n + 2)
  exact compose_three_squares aK.hom bK.hom dK.hom aL.hom bL.hom dL.hom
    (HomologicalComplex.homologyMap (SectionsHomologyNaturality.IntrinsicCech.sheafTopSectionsMap ψ) (n + 2))
    (SectionsHomologyNaturality.IntrinsicCech.sectionsCycleCokernelMap ψ (n + 1)) hm (cohomologyMap f (n + 2)) hc hb hd

include hψ in
theorem acyclicResolutionPositiveCohomologyIso_naturality (n : ℕ) :
    HomologicalComplex.homologyMap (SectionsHomologyNaturality.IntrinsicCech.sheafTopSectionsMap ψ) (n + 1) ≫
        (AcyclicResolutionCohomology.IntrinsicCech.acyclicResolutionPositiveCohomologyIso L eL wL haugL hposL hL n).hom =
      (AcyclicResolutionCohomology.IntrinsicCech.acyclicResolutionPositiveCohomologyIso K eK wK haugK hposK hK n).hom ≫
        cohomologyMap f (n + 1) := by
  cases n with
  | zero =>
      exact acyclicResolutionPositiveCohomologyIso_naturality_zero
        eK wK eL wL haugK haugL hposK hposL hK hL f ψ hψ
  | succ n =>
      exact acyclicResolutionPositiveCohomologyIso_naturality_succ
        eK wK eL wL haugK haugL hposK hposL hK hL f ψ hψ n

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Positive.ResolutionNaturality.IntrinsicCech
