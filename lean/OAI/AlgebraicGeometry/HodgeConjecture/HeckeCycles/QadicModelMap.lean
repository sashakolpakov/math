import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Local.Lattice
import OAI.AlgebraicGeometry.PELModuli.CMPoints.Arithmetic
import OAI.AlgebraicGeometry.AbelianScheme.TateComparison.Data

/-! # Qadic Model Map -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.QadicModelMap.CM

noncomputable section

/-! Extend the chosen integral completion map to the actual arithmetic
localization, and prove its compatibility with the generic-fiber map. -/

open _root_.NumberField _root_.CategoryTheory _root_.AlgebraicGeometry
open OAI.AlgebraicGeometry.AbelianScheme.TateComparison.Data

variable {K : Type} [Field K] [NumberField K] {κ : K →+* ℂ}
  {q : ℕ} [Fact q.Prime] (j : PELModuli.CMPoints.Arithmetic.QadicChoice K κ q)

def localFieldEmbedding : K →+* ℚ_[q] :=
  j.completion.toRingHom.comp (NumberField.FinitePlace.embedding j.prime)

def integralMap (d : ℕ) (hcop : Nat.Coprime q d) : AbelianScheme.TateComparison.Data.modelRing K d →+* ℤ_[q] :=
  IsLocalization.Away.lift (d : RingOfIntegers K)
    (g := j.integralEmbedding)
    (by simpa only [map_natCast] using Local.Lattice.CM.natCast_isUnit d hcop)

theorem integralMap_on_integers (d : ℕ) (hcop : Nat.Coprime q d)
    (a : RingOfIntegers K) :
    integralMap j d hcop (algebraMap (RingOfIntegers K) (AbelianScheme.TateComparison.Data.modelRing K d) a) =
      j.integralEmbedding a := IsLocalization.Away.lift_eq _ _ a

theorem integralMap_generic (d : ℕ) (hd : d ≠ 0) (hcop : Nat.Coprime q d) :
    PadicInt.Coe.ringHom.comp (integralMap j d hcop) =
      (localFieldEmbedding j).comp (ArithmeticGeometry.Models.Algebra.Constructions.Foundations.integersAwayToField K d hd) := by
  apply IsLocalization.ringHom_ext (Submonoid.powers (d : RingOfIntegers K))
  ext a
  change PadicInt.Coe.ringHom (integralMap j d hcop (algebraMap _ _ a)) =
    localFieldEmbedding j (ArithmeticGeometry.Models.Algebra.Constructions.Foundations.integersAwayToField K d hd (algebraMap _ _ a))
  rw [integralMap_on_integers, ArithmeticGeometry.Models.Algebra.Constructions.Foundations.integersAwayToField_algebraMap]
  exact RingHom.congr_fun j.integral_compatibility a

def integralBase (d : ℕ) (hcop : Nat.Coprime q d) : Spec (.of ℤ_[q]) ⟶ AbelianScheme.TateComparison.Data.modelBase K d :=
  Spec.map (CommRingCat.ofHom (integralMap j d hcop))

theorem generic_base_compatible (d : ℕ) (hd : d ≠ 0) (hcop : Nat.Coprime q d) :
    Spec.map (CommRingCat.ofHom (algebraMap ℤ_[q] ℚ_[q])) ≫ integralBase j d hcop =
      Spec.map (CommRingCat.ofHom (localFieldEmbedding j)) ≫ AbelianScheme.TateComparison.Data.modelGeneric K d hd := by
  dsimp only [integralBase, AbelianScheme.TateComparison.Data.modelGeneric]
  rw [← Spec.map_comp, ← Spec.map_comp]
  exact congrArg (fun f : AbelianScheme.TateComparison.Data.modelRing K d →+* ℚ_[q] => Spec.map (CommRingCat.ofHom f))
    (integralMap_generic j d hd hcop)

/-- Any residue map supplied by CMPoints on this localization is the reduction
of the constructed integral completion map. -/
theorem integralMap_residue (d : ℕ) (hcop : Nat.Coprime q d)
    (residue : AbelianScheme.TateComparison.Data.modelRing K d →+* ZMod q)
    (hres : residue.comp (algebraMap (RingOfIntegers K) (AbelianScheme.TateComparison.Data.modelRing K d)) = j.residue) :
    PadicInt.toZMod.comp (integralMap j d hcop) = residue := by
  apply IsLocalization.ringHom_ext (Submonoid.powers (d : RingOfIntegers K))
  ext a
  change PadicInt.toZMod (integralMap j d hcop (algebraMap _ _ a)) =
    residue (algebraMap _ _ a)
  rw [integralMap_on_integers]
  exact (RingHom.congr_fun hres a).symm

theorem special_base_compatible (d : ℕ) (hcop : Nat.Coprime q d)
    (residue : AbelianScheme.TateComparison.Data.modelRing K d →+* ZMod q)
    (hres : residue.comp (algebraMap (RingOfIntegers K) (AbelianScheme.TateComparison.Data.modelRing K d)) = j.residue) :
    Spec.map (CommRingCat.ofHom (PadicInt.toZMod : ℤ_[q] →+* ZMod q)) ≫
        integralBase j d hcop = Spec.map (CommRingCat.ofHom residue) := by
  dsimp only [integralBase]
  rw [← Spec.map_comp]
  exact congrArg (fun f : AbelianScheme.TateComparison.Data.modelRing K d →+* ZMod q => Spec.map (CommRingCat.ofHom f))
    (integralMap_residue j d hcop residue hres)

end

end OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.QadicModelMap.CM
