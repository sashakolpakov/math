import OAI.AlgebraicGeometry.Crystalline.Cohomology.Base.IntrinsicCechScalarBicomplex
import OAI.AlgebraicGeometry.Crystalline.Cohomology.BaseAffine.ChangeFormUnit
import OAI.AlgebraicGeometry.Crystalline.Cohomology.Cech.SectionTotal
import OAI.NumberTheory.PadicHodge.GeometricComparison.SheafificationComplex

/-! # Coordinate Cech Unit -/

namespace OAI.AlgebraicGeometry.Crystalline.Cohomology.Base.CoordinateCechUnit.BaseCoordinateCechUnit

noncomputable section

/-! The actual sheafification unit identifies coordinate Cech complexes with the original sheaf Cech complexes before and after geometric base change. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry Opposite Simplicial

universe u
variable (R : Type u) [CommRing R] (X : Over (Spec (CommRingCat.of R)))

section General
variable {ι : Type u} (U : ι → X.left.Opens)

local instance : (Cech.Descent.CechDescent.cechFunctor R X U).Additive := by
  change (FormalCoproduct.cochainComplexFunctor (FormalCoproduct.mk ι U).cech).Additive
  infer_instance

def map : Cech.Descent.CechDescent.bicomplex R X U ⟶
    Cech.SectionTotal.CechSectionTotal.directBicomplex R X U (DeRhamGlobalId.DeRhamGlobal.sheafComplex R X) :=
  ((Cech.Descent.CechDescent.cechFunctor R X U).mapHomologicalComplex (.up ℕ)).map
    (NumberTheory.PadicHodge.GeometricComparison.SheafificationComplex.SheafificationComplexUnit.unit (Opens.grothendieckTopology X.left)
      (DeRhamGlobalId.DeRhamGlobal.presheafComplex R X))

end General

variable [IsProper X.hom] [Smooth X.hom]
local notation "U" => OAI.AlgebraicGeometry.Crystalline.Cohomology.Base.ProperOrdinaryFormCharts.BaseSmoothProperOrdinaryFormCharts.opens R X

local instance schemeSeparated : X.left.IsSeparated := by
  constructor
  rw [← terminal.comp_from X.hom]
  infer_instance

theorem source_forms (q : ℕ) (t : Fin (q + 1) → SmoothProperEtaleCover.BaseSmoothProperEtaleCover.Index R X) (n : ℕ) :
    IsIso ((toSheafify (Opens.grothendieckTopology X.left)
      (DeRhamGlobalId.DeRhamGlobal.formsPresheaf R X n)).app (op (∏ᶜ (U ∘ t)))) := by
  have hI : IsAffineOpen (∏ᶜ (U ∘ t)) :=
    SheafCohomology.Cech.Cochains.IsAffineOpen.cechIntersection U (ProperOrdinaryFormCharts.BaseSmoothProperOrdinaryFormCharts.affine R X) q t
  let I : X.left.affineOpens := ⟨∏ᶜ (U ∘ t), hI⟩
  let i := t 0
  have hi : I.val ≤ ProperOrdinaryFormCharts.BaseSmoothProperOrdinaryFormCharts.opens R X i := leOfHom (Pi.π (U ∘ t) 0)
  let σ := SmoothProperEtaleCover.BaseSmoothProperEtaleCover.coordinateIndex R X i
  let : LinearOrder σ := LinearOrder.lift' (Fintype.equivFin σ) (Fintype.equivFin σ).injective
  exact @BaseAffine.OpenOrdinaryFormUnit.BaseAffineOpenOrdinaryFormUnit.forms R inferInstance X I.val I.property σ inferInstance
    (EtaleSubchartCoordinates.BaseEtaleSubchartCoordinates.polynomialAlgebra R X I i hi)
    (EtaleSubchartCoordinates.BaseEtaleSubchartCoordinates.tower R X I i hi)
    (EtaleSubchartCoordinates.BaseEtaleSubchartCoordinates.etale R X I i hi) n

theorem source_row_isIso (n : ℕ) : IsIso ((BaseCoordinateCechUnit.map R X U).f n) :=
  NumberTheory.PadicHodge.GeometricComparison.Cech.TermwiseIso.CechTermwiseIso.isIso (FormalCoproduct.mk (SmoothProperEtaleCover.BaseSmoothProperEtaleCover.Index R X) U).cech
    (toSheafify (Opens.grothendieckTopology X.left) (DeRhamGlobalId.DeRhamGlobal.formsPresheaf R X n))
    (fun q t => source_forms R X q t n)

def sourceIso : Cech.Descent.CechDescent.bicomplex R X U ≅
    Cech.SectionTotal.CechSectionTotal.directBicomplex R X U (DeRhamGlobalId.DeRhamGlobal.sheafComplex R X) := by
  let (n : ℕ) : IsIso ((BaseCoordinateCechUnit.map R X U).f n) := source_row_isIso R X n
  let : IsIso (BaseCoordinateCechUnit.map R X U) := HomologicalComplex.Hom.isIso_of_components _
  exact asIso (BaseCoordinateCechUnit.map R X U)

variable (S : Type u) [CommRing S] [Algebra R S]
  (Y : Over (Spec (CommRingCat.of S))) (f : Y.left ⟶ X.left)
  (hp : IsPullback f Y.hom X.hom (Spec.map (CommRingCat.ofHom (algebraMap R S))))

local instance : PreservesFiniteLimits (TopologicalSpace.Opens.map f.base) :=
  IntrinsicCechScalarBicomplex.BaseIntrinsicCechScalarBicomplex.opensFiniteLimits R S X Y f

include hp in
theorem target_forms (q : ℕ) (t : Fin (q + 1) → SmoothProperEtaleCover.BaseSmoothProperEtaleCover.Index R X) (n : ℕ) :
    IsIso ((toSheafify (Opens.grothendieckTopology Y.left)
      (DeRhamGlobalId.DeRhamGlobal.formsPresheaf S Y n)).app (op (∏ᶜ (fun j => f ⁻¹ᵁ U (t j))))) := by
  let e := PreservesProduct.iso (TopologicalSpace.Opens.map f.base) (U ∘ t)
  have he : f ⁻¹ᵁ (∏ᶜ (U ∘ t)) = ∏ᶜ (fun j => f ⁻¹ᵁ U (t j)) :=
    le_antisymm (leOfHom e.hom) (leOfHom e.inv)
  rw [← he]
  have hI : IsAffineOpen (∏ᶜ (U ∘ t)) :=
    SheafCohomology.Cech.Cochains.IsAffineOpen.cechIntersection U (ProperOrdinaryFormCharts.BaseSmoothProperOrdinaryFormCharts.affine R X) q t
  let I : X.left.affineOpens := ⟨∏ᶜ (U ∘ t), hI⟩
  let i := t 0
  have hi : I.val ≤ ProperOrdinaryFormCharts.BaseSmoothProperOrdinaryFormCharts.opens R X i := leOfHom (Pi.π (U ∘ t) 0)
  let σ := SmoothProperEtaleCover.BaseSmoothProperEtaleCover.coordinateIndex R X i
  let : LinearOrder σ := LinearOrder.lift' (Fintype.equivFin σ) (Fintype.equivFin σ).injective
  exact @BaseAffine.ChangeFormUnit.BaseAffineBaseChangeFormUnit.forms R S inferInstance inferInstance inferInstance X Y f hp
    I.val I.property σ inferInstance
    (EtaleSubchartCoordinates.BaseEtaleSubchartCoordinates.polynomialAlgebra R X I i hi)
    (EtaleSubchartCoordinates.BaseEtaleSubchartCoordinates.tower R X I i hi)
    (EtaleSubchartCoordinates.BaseEtaleSubchartCoordinates.etale R X I i hi) n

include hp in
theorem target_row_isIso (n : ℕ) : IsIso ((BaseCoordinateCechUnit.map S Y (fun i => f ⁻¹ᵁ U i)).f n) :=
  NumberTheory.PadicHodge.GeometricComparison.Cech.TermwiseIso.CechTermwiseIso.isIso
    (FormalCoproduct.mk (SmoothProperEtaleCover.BaseSmoothProperEtaleCover.Index R X) (fun i => f ⁻¹ᵁ U i)).cech
    (toSheafify (Opens.grothendieckTopology Y.left) (DeRhamGlobalId.DeRhamGlobal.formsPresheaf S Y n))
    (fun q t => target_forms R X S Y f hp q t n)

def targetIso : Cech.Descent.CechDescent.bicomplex S Y (fun i => f ⁻¹ᵁ U i) ≅
    Cech.SectionTotal.CechSectionTotal.directBicomplex S Y (fun i => f ⁻¹ᵁ U i) (DeRhamGlobalId.DeRhamGlobal.sheafComplex S Y) := by
  let (n : ℕ) : IsIso ((BaseCoordinateCechUnit.map S Y (fun i => f ⁻¹ᵁ U i)).f n) := target_row_isIso R X S Y f hp n
  let : IsIso (BaseCoordinateCechUnit.map S Y (fun i => f ⁻¹ᵁ U i)) := HomologicalComplex.Hom.isIso_of_components _
  exact asIso (BaseCoordinateCechUnit.map S Y (fun i => f ⁻¹ᵁ U i))

end

end OAI.AlgebraicGeometry.Crystalline.Cohomology.Base.CoordinateCechUnit.BaseCoordinateCechUnit
