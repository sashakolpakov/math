import OAI.NumberTheory.PadicHodge.IntegralComparison.Affine.CoordinateSections
import OAI.AlgebraicGeometry.Crystalline.Cohomology.BaseAffine.SectionTowers
import Mathlib.RingTheory.Etale.Basic

/-! # Section Coordinates -/

namespace OAI.AlgebraicGeometry.Crystalline.Cohomology.BaseAffine.SectionCoordinates.BaseAffineSectionCoordinates

noncomputable section

/-!
# Original principal-open sections inherit etale coordinates over any commutative base
-/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

variable (k C σ : Type u) [CommRing k] [CommRing C] [Algebra k C]
  [Algebra (MvPolynomial σ k) C] [IsScalarTower k (MvPolynomial σ k) C]

@[instance_reducible]
def polynomialAlgebra (U : (Spec (CommRingCat.of C)).Opens) :
    Algebra (MvPolynomial σ k) Γ(Spec (CommRingCat.of C), U) := by
  let : Algebra C Γ(Spec (CommRingCat.of C), U) := SectionTowers.BaseAffineSectionTowers.coordinateAlgebra C U
  exact ((algebraMap C Γ(Spec (CommRingCat.of C), U)).comp (algebraMap (MvPolynomial σ k) C)).toAlgebra

omit [Algebra k C] [IsScalarTower k (MvPolynomial σ k) C] in
theorem coordinate_tower (U : (Spec (CommRingCat.of C)).Opens) :
    letI : Algebra C Γ(Spec (CommRingCat.of C), U) := SectionTowers.BaseAffineSectionTowers.coordinateAlgebra C U
    letI : Algebra (MvPolynomial σ k) Γ(Spec (CommRingCat.of C), U) := polynomialAlgebra k C σ U
    IsScalarTower (MvPolynomial σ k) C Γ(Spec (CommRingCat.of C), U) := by
  let : Algebra C Γ(Spec (CommRingCat.of C), U) := SectionTowers.BaseAffineSectionTowers.coordinateAlgebra C U
  let : Algebra (MvPolynomial σ k) Γ(Spec (CommRingCat.of C), U) := polynomialAlgebra k C σ U
  exact IsScalarTower.of_algebraMap_eq (fun _ => rfl)

theorem base_tower (U : (Spec (CommRingCat.of C)).Opens) :
    letI : Algebra k Γ(Spec (CommRingCat.of C), U) :=
      AlgebraicForms.AlgebraicDeRham.sectionAlgebra k (SectionTowers.BaseAffineSectionTowers.affineScheme k C) U
    letI : Algebra (MvPolynomial σ k) Γ(Spec (CommRingCat.of C), U) := polynomialAlgebra k C σ U
    IsScalarTower k (MvPolynomial σ k) Γ(Spec (CommRingCat.of C), U) := by
  let : Algebra k Γ(Spec (CommRingCat.of C), U) :=
    AlgebraicForms.AlgebraicDeRham.sectionAlgebra k (SectionTowers.BaseAffineSectionTowers.affineScheme k C) U
  let : Algebra C Γ(Spec (CommRingCat.of C), U) := SectionTowers.BaseAffineSectionTowers.coordinateAlgebra C U
  let : Algebra (MvPolynomial σ k) Γ(Spec (CommRingCat.of C), U) := polynomialAlgebra k C σ U
  apply IsScalarTower.of_algebraMap_eq
  intro r
  exact (DFunLike.congr_fun (SectionTowers.BaseAffineSectionTowers.sectionBaseMap k C U) r).trans
    (congrArg (algebraMap C Γ(Spec (CommRingCat.of C), U)) (IsScalarTower.algebraMap_apply k (MvPolynomial σ k) C r))

variable [Algebra.FormallyEtale (MvPolynomial σ k) C]

omit [Algebra k C] [IsScalarTower k (MvPolynomial σ k) C] in
theorem principal_etale (c : C) :
    letI : Algebra (MvPolynomial σ k) Γ(Spec (CommRingCat.of C), PrimeSpectrum.basicOpen c) :=
      polynomialAlgebra k C σ (PrimeSpectrum.basicOpen c)
    Algebra.FormallyEtale (MvPolynomial σ k) Γ(Spec (CommRingCat.of C), PrimeSpectrum.basicOpen c) := by
  let U : (Spec (CommRingCat.of C)).Opens := PrimeSpectrum.basicOpen c
  let : Algebra C Γ(Spec (CommRingCat.of C), U) := SectionTowers.BaseAffineSectionTowers.coordinateAlgebra C U
  let : Algebra (MvPolynomial σ k) Γ(Spec (CommRingCat.of C), U) := polynomialAlgebra k C σ U
  let : IsScalarTower (MvPolynomial σ k) C Γ(Spec (CommRingCat.of C), U) := coordinate_tower k C σ U
  let : IsLocalization.Away c Γ(Spec (CommRingCat.of C), U) := NumberTheory.PadicHodge.IntegralComparison.Affine.CoordinateSections.principal_localization C c
  let : Algebra.FormallyEtale C Γ(Spec (CommRingCat.of C), U) :=
    Algebra.FormallyEtale.of_isLocalization (Submonoid.powers c)
  exact Algebra.FormallyEtale.comp (MvPolynomial σ k) C Γ(Spec (CommRingCat.of C), U)

end

end OAI.AlgebraicGeometry.Crystalline.Cohomology.BaseAffine.SectionCoordinates.BaseAffineSectionCoordinates
