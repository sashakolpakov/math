import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Geometric.ComparisonSpecialization
import OAI.NumberTheory.PadicHodge.GeometricComparison.HeckeScalar

/-! # Specialized -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Specialized.CM.Hecke

noncomputable section

/-! Rational specialization of GeometricComparison's Hecke realization respects its
actual integral representatives and their stated denominator clearings. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj TensorProduct
open OAI.NumberTheory.PadicHodge.GeometricComparison.HeckeScalar
open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Geometric.ComparisonSpecialization.CM

variable {K : Type} [Field K] [NumberField K]
  {q : ℕ} [Fact q.Prime] {jq : K →+* ℚ_[q]} (A : NumberTheory.PadicHodge.GeometricComparison.Geometry.AbelianH1Model K q jq)

def specializeRational : FormalGeometry.Completion.Endomorphisms.Construction.RationalAlgebraicEnd A.variety.scheme →ₐ[ℚ]
    FormalGeometry.Completion.Endomorphisms.Construction.RationalAlgebraicEnd A.specialFiber.scheme :=
  Algebra.TensorProduct.map (AlgHom.id ℚ ℚ) (Geometric.ComparisonSpecialization.CM.specializeEnd A).toIntAlgHom

theorem specializeRational_tmul (r : ℚ) (f : FormalGeometry.Completion.Endomorphisms.Construction.AlgebraicEnd A.variety.scheme) :
    specializeRational A (r ⊗ₜ[ℤ] f) = r ⊗ₜ[ℤ] Geometric.ComparisonSpecialization.CM.specializeEnd A f := by
  simp [specializeRational]

def specialEndOfExtending (f : A.ExtendingEndomorphism) : FormalGeometry.Completion.Endomorphisms.Construction.AlgebraicEnd A.specialFiber.scheme := by
  let u : A.integral.scheme ⟶ A.integral.scheme := f.integral.toMul.hom.hom
  let : IsMonHom u := f.integral.toMul.hom.isMonHom_hom
  let : GrpObj ((Over.pullback (NumberTheory.PadicHodge.GeometricComparison.Geometry.scalarBaseMap (PadicInt.toZMod : ℤ_[q] →+* ZMod q))).obj
      A.integral.scheme) :=
    Functor.grpObjObj (F := Over.pullback (NumberTheory.PadicHodge.GeometricComparison.Geometry.scalarBaseMap (PadicInt.toZMod : ℤ_[q] →+* ZMod q)))
  let fS : A.specialFiber.scheme ⟶ A.specialFiber.scheme :=
    (Over.pullback (NumberTheory.PadicHodge.GeometricComparison.Geometry.scalarBaseMap (PadicInt.toZMod : ℤ_[q] →+* ZMod q))).map u
  let : IsMonHom fS := inferInstanceAs (IsMonHom
    ((Over.pullback (NumberTheory.PadicHodge.GeometricComparison.Geometry.scalarBaseMap (PadicInt.toZMod : ℤ_[q] →+* ZMod q))).map u))
  exact Additive.ofMul (Grp.ofHom fS)

theorem specializeEnd_eq (f : A.ExtendingEndomorphism) :
    Geometric.ComparisonSpecialization.CM.specializeEnd A f.generic = specialEndOfExtending A f := by
  apply Additive.toMul.injective
  apply Grp.hom_ext
  exact Geometric.ComparisonSpecialization.CM.specializeEnd_extending A f

variable {H : Type} [CommRing H] [Algebra ℚ H]

def specializedHeckeAction (ρ : A.HeckeRealization H) :
    H →ₐ[ℚ] FormalGeometry.Completion.Endomorphisms.Construction.RationalAlgebraicEnd A.specialFiber.scheme :=
  (specializeRational A).comp ρ.action

theorem specializedHeckeAction_presentation (ρ : A.HeckeRealization H) (h : H) :
    (ρ.presentation h).sum (fun f r => r ⊗ₜ[ℤ] specialEndOfExtending A f) =
      specializedHeckeAction A ρ h := by
  calc
    _ = (ρ.presentation h).sum (fun f r => specializeRational A (r ⊗ₜ[ℤ] f.generic)) := by
      apply Finsupp.sum_congr
      intro f _
      rw [specializeRational_tmul, specializeEnd_eq]
    _ = specializeRational A ((ρ.presentation h).sum (fun f r => r ⊗ₜ[ℤ] f.generic)) :=
      (map_finsuppSum (specializeRational A) _ _).symm
    _ = specializedHeckeAction A ρ h := congrArg (specializeRational A) (ρ.represents h)

end

end OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Specialized.CM.Hecke
