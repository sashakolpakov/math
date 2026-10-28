import OAI.NumberTheory.PadicHodge.IntegralComparison.Truncated.SmoothDividedPowers
import OAI.NumberTheory.PadicHodge.IntegralComparison.Bounded.WittBase
import OAI.NumberTheory.PadicHodge.IntegralComparison.Crystalline.Presentation
import OAI.NumberTheory.PadicHodge.IntegralComparison.Truncated.ChartDeRham

/-! # Smooth Frame -/

namespace OAI

noncomputable section

namespace NumberTheory.PadicHodge.IntegralComparison.Truncated.SmoothFrame

/-! The actual ring of a smooth finite-Witt-level lift is a bounded
crystalline frame for its actual special fiber. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

open OAI.NumberTheory.PadicHodge.IntegralComparison.Crystalline.Presentation OAI.NumberTheory.PadicHodge.IntegralComparison.Witt.Crystalline

variable (p : ℕ) (A C : Type) [CommRing A] [CommRing C]
  (ρ : A →+* C) (hρ : Function.Surjective ρ) (hker : RingHom.ker ρ = Ideal.span {(p : A)})

def quotientEquiv : (A ⧸ Ideal.span {(p : A)}) ≃+* C :=
  (Ideal.quotEquivOfEq hker.symm).trans (RingHom.quotientKerEquivOfSurjective hρ)

theorem quotientEquiv_mk (a : A) :
    quotientEquiv p A C ρ hρ hker (Ideal.Quotient.mk (Ideal.span {(p : A)}) a) = ρ a := by
  change RingHom.quotientKerEquivOfSurjective hρ
    ((Ideal.quotEquivOfEq hker.symm) (Ideal.Quotient.mk _ a)) = _
  rw [Ideal.quotEquivOfEq_mk]
  rfl

variable [Fact p.Prime] (k : Type) [Field k] [Fintype k] [CharP k p] (n : ℕ)
  [Algebra (Witt.Ring p k n) A]

local notation "W" => WittVector p k
local notation "S" => OAI.NumberTheory.PadicHodge.IntegralComparison.Truncated.Witt.Ring p k n

def base : W →+* A := (algebraMap S A).comp (Witt.quotient p k n)

omit [Fintype k] [CharP k p] in
include k in
theorem prime_power_zero : (p : A) ^ (n + 1) = 0 := by
  have h := congrArg (algebraMap S A) (Witt.prime_power_zero p k n)
  simpa only [map_pow, map_natCast, map_zero] using h

variable [Algebra.Smooth (Witt.Ring p k n) A] [Algebra k C]
  (hbase : ∀ w : WittVector p k,
    ρ ((algebraMap (Witt.Ring p k n) A) (Witt.quotient p k n w)) =
      algebraMap k C (WittVector.constantCoeff w))

local notation "e" => OAI.NumberTheory.PadicHodge.IntegralComparison.Truncated.SmoothFrame.quotientEquiv p A C ρ hρ hker

def object : BigCrystallineSite.Object p W (Ideal.span {(p : W)})
    (AlgebraicGeometry.Crystalline.Cohomology.Witt.DividedPowers.WittDividedPowers.wittDividedPowers p k)
    (Witt.Crystalline.wittStructureMap p k (Crystalline.Presentation.affineScheme k C)) where
  ring := CommRingCat.of A
  base := SmoothFrame.base p A k n
  ideal := Ideal.span {(p : A)}
  dividedPowers := SmoothDividedPowers.dividedPowers p k n A
  baseCompatible := SmoothDividedPowers.wittBase_isDPMorphism p k n A
  primeNilpotent := ⟨n + 1, prime_power_zero p A k n⟩
  nilIdeal := by
    intro x hx
    obtain ⟨a, rfl⟩ := Ideal.mem_span_singleton.mp hx
    exact ⟨n + 1, by rw [mul_pow, prime_power_zero p A k n, zero_mul]⟩
  mapToX := Spec.map (CommRingCat.ofHom (e).symm.toRingHom)
  overBase := by
    rw [Crystalline.Presentation.affine_wittStructureMap]
    change Spec.map (CommRingCat.ofHom (e).symm.toRingHom) ≫
        Spec.map (CommRingCat.ofHom ((algebraMap k C).comp WittVector.constantCoeff)) =
      Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (Ideal.span {(p : A)}))) ≫
        Spec.map (CommRingCat.ofHom (SmoothFrame.base p A k n))
    rw [← Spec.map_comp, ← Spec.map_comp]
    congr 1
    apply CommRingCat.hom_ext
    apply RingHom.ext
    intro w
    apply (e).injective
    change (e) ((e).symm (algebraMap k C (WittVector.constantCoeff w))) =
      (e) (Ideal.Quotient.mk _ (SmoothFrame.base p A k n w))
    rw [RingEquiv.apply_symm_apply, quotientEquiv_mk]
    exact (hbase w).symm

def boundedFrame : BoundedCrystalline.Site.Objects (p := p)
    (J := Ideal.span {(p : W)}) (δ := AlgebraicGeometry.Crystalline.Cohomology.Witt.DividedPowers.WittDividedPowers.wittDividedPowers p k)
    (Witt.Crystalline.wittStructureMap p k (Crystalline.Presentation.affineScheme k C)) n :=
  ⟨object p A C ρ hρ hker k n hbase, prime_power_zero p A k n⟩

end NumberTheory.PadicHodge.IntegralComparison.Truncated.SmoothFrame

namespace NumberTheory.PadicHodge.IntegralComparison.Truncated.SmoothFrame.Complex

/-! The actual finite-level frame complex is the ordinary de Rham
complex of the same smooth algebra over the truncated Witt ring. -/

open _root_.CategoryTheory

open _root_.Complex

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable (p : ℕ) [Fact p.Prime] (k : Type) [Field k] [Fintype k] [CharP k p]
  (n : ℕ) (A : Type) [CommRing A]
  [Algebra (Witt.Ring p k n) A]
  [Algebra.Smooth (Witt.Ring p k n) A]

local notation "W" => WittVector p k
local notation "S" => OAI.NumberTheory.PadicHodge.IntegralComparison.Truncated.Witt.Ring p k n
local notation "I" => Ideal.span {(p : A)}
local notation "δ" => OAI.NumberTheory.PadicHodge.IntegralComparison.Truncated.SmoothDividedPowers.dividedPowers p k n A

@[instance_reducible] def wittAlgebra : Algebra W A :=
  (SmoothFrame.base p A k n).toAlgebra

omit [Fintype k] [CharP k p] [Algebra.Smooth S A] in
theorem ideal_eq : letI := wittAlgebra p k n A;
    I = Ideal.span {algebraMap W A (p : W)} := by
  let := wittAlgebra p k n A
  rw [map_natCast]

def iso : letI := wittAlgebra p k n A; AlgebraicGeometry.Crystalline.Cohomology.PD.DeRham.PDDeRham.complex W A I δ ≅
    ((ModuleCat.restrictScalars (algebraMap W S)).mapHomologicalComplex (.up ℕ)).obj
      (AlgebraicGeometry.Crystalline.Cohomology.DeRhamPresentationTo.DeRhamPresentation.complex S A) := by
  letI := wittAlgebra p k n A
  letI : IsScalarTower W S A := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  exact Principal.BaseComplex.ofIdealEq W A (p : W)
    (AlgebraicGeometry.Crystalline.Cohomology.Witt.DividedPowers.WittDividedPowers.wittDividedPowers p k) I δ (ideal_eq p k n A)
    (SmoothDividedPowers.wittBase_isDPMorphism p k n A) ≪≫
      GeometricComparison.SurjectiveBase.SurjectiveBaseDeRham.iso W S A Ideal.Quotient.mk_surjective

omit [Fintype k] in
theorem iso_symbol (m : ℕ) (a : A) (v : Fin m → A) :
    letI := wittAlgebra p k n A;
    ((iso p k n A).hom.f m) (AlgebraicGeometry.Crystalline.Cohomology.PD.DeRham.PDDeRham.symbol W A I δ a v) =
      AlgebraicGeometry.Crystalline.Cohomology.DeRhamPresentationTo.DeRhamPresentation.symbol S A a v := by
  let := wittAlgebra p k n A
  let : IsScalarTower W S A := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  change OrdinaryBaseQuotient.Ordinary.formsEquiv W S A Ideal.Quotient.mk_surjective m
    (((Principal.BaseComplex.ofIdealEq W A (p : W)
      (AlgebraicGeometry.Crystalline.Cohomology.Witt.DividedPowers.WittDividedPowers.wittDividedPowers p k) I δ (ideal_eq p k n A)
      (SmoothDividedPowers.wittBase_isDPMorphism p k n A)).hom.f m)
        (AlgebraicGeometry.Crystalline.Cohomology.PD.DeRham.PDDeRham.symbol W A I δ a v)) = _
  rw [ChartDeRham.PrincipalBaseComplex.ofIdealEq_symbol]
  exact OrdinaryBaseQuotient.Ordinary.formsEquiv_symbol W S A Ideal.Quotient.mk_surjective m a v

end NumberTheory.PadicHodge.IntegralComparison.Truncated.SmoothFrame.Complex

end

end OAI
