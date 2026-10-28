import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Polynomial.Place
import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Parameter.Branches

/-! # Local Map -/

namespace OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Parameter.LocalMap

noncomputable section

/-! A function vanishing in a local ring defines an actual map from
the parameter's zero local ring, with its prescribed fraction-field map. -/

open IsLocalRing

open OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Polynomial.Place OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.CurveParameter OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Parameter.Branches

variable (k B : Type) [Field k] [CommRing B] [IsLocalRing B] [Algebra k B]
  (b : B) (hb : b ∈ maximalIdeal B)

include hb

theorem aeval_isUnit (p : Polynomial k) (hp : p ∈ (ProjectionFormula.Polynomial.Place.zeroIdeal k).primeCompl) :
    IsUnit (Polynomial.aeval b p) := by
  have hc : p.coeff 0 ≠ 0 := by
    intro h
    exact hp (Ideal.mem_span_singleton.mpr (Polynomial.X_dvd_iff.mpr h))
  apply (residue_ne_zero_iff_isUnit _).mp
  have he := Polynomial.aeval_algHom_apply (IsScalarTower.toAlgHom k B (ResidueField B)) b p
  change Polynomial.aeval (algebraMap B (ResidueField B) b) p =
    algebraMap B (ResidueField B) (Polynomial.aeval b p) at he
  have hz : algebraMap B (ResidueField B) b = 0 := (residue_eq_zero_iff b).mpr hb
  rw [hz, ← Polynomial.coeff_zero_eq_aeval_zero'] at he
  change algebraMap B (ResidueField B) (Polynomial.aeval b p) ≠ 0
  rw [← he]
  exact (map_ne_zero_iff _ (algebraMap k (ResidueField B)).injective).mpr hc

def localMap : ProjectionFormula.Polynomial.Place.localRing k →+* B :=
  IsLocalization.lift (M := (ProjectionFormula.Polynomial.Place.zeroIdeal k).primeCompl)
    (g := (Polynomial.aeval b).toRingHom)
    (fun p => aeval_isUnit k B b hb p p.property)

theorem localMap_algebraMap (p : Polynomial k) :
    localMap k B b hb (algebraMap (Polynomial k) (ProjectionFormula.Polynomial.Place.localRing k) p) = Polynomial.aeval b p :=
  IsLocalization.lift_eq _ p

variable (L : Type) [Field L] [Algebra k L] [Algebra B L] [IsScalarTower k B L]
  (g : L) (hg : Transcendental k g) (hbg : algebraMap B L b = g)

include hbg

theorem localMap_field :
    letI := CurveParameter.polynomialAlgebra k L g
    letI := CurveParameter.fractionAlgebra k L g hg
    letI := Branches.localAlgebra k L g hg
    (algebraMap B L).comp (localMap k B b hb) = algebraMap (ProjectionFormula.Polynomial.Place.localRing k) L := by
  let := CurveParameter.polynomialAlgebra k L g
  let := CurveParameter.fractionAlgebra k L g hg
  let := Branches.localAlgebra k L g hg
  let := Branches.localTower k L g hg
  let : FaithfulSMul (Polynomial k) L :=
    (faithfulSMul_iff_algebraMap_injective (Polynomial k) L).mpr (CurveParameter.polynomialAlgebra_injective k L g hg)
  let : IsScalarTower (Polynomial k) (FractionRing (Polynomial k)) L :=
    FractionRing.isScalarTower_liftAlgebra (Polynomial k) L
  apply IsLocalization.ringHom_ext (ProjectionFormula.Polynomial.Place.zeroIdeal k).primeCompl
  apply RingHom.ext
  intro p
  change algebraMap B L (localMap k B b hb (algebraMap (Polynomial k) (ProjectionFormula.Polynomial.Place.localRing k) p)) =
    algebraMap (ProjectionFormula.Polynomial.Place.localRing k) L (algebraMap (Polynomial k) (ProjectionFormula.Polynomial.Place.localRing k) p)
  rw [localMap_algebraMap, IsScalarTower.algebraMap_apply (ProjectionFormula.Polynomial.Place.localRing k) (FractionRing (Polynomial k)) L,
    ← IsScalarTower.algebraMap_apply (Polynomial k) (ProjectionFormula.Polynomial.Place.localRing k) (FractionRing (Polynomial k)),
    ← IsScalarTower.algebraMap_apply]
  exact (Polynomial.aeval_algHom_apply (IsScalarTower.toAlgHom k B L) b p).symm.trans
    (congrArg (fun x : L => Polynomial.aeval x p) hbg)

end

end OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Parameter.LocalMap
