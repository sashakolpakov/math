import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.ComparisonPolynomial
import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Specialized

/-! # Specialization -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Source.Specialization.CM

noncomputable section

/-! Specialization into the original arithmetic Albanese product is
constructed from Neron extension and the proved special-fiber isomorphism.
Its rational Hecke operators and all denominator clearings transport to
the very same GeometricComparison Hecke realization. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj TensorProduct
open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.AlbaneseModel.CM OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.ComparisonPolynomial.CM
open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Geometric.ComparisonSpecialization.CM OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Specialized.CM.Hecke

variable {E K : Type} [Field E] [NumberField E] [NumberField.IsCMField E]
  [Field K] [NumberField K] {s q : ℕ} [Fact q.Prime]
  (D : AbelianScheme.TateComparison.Data.SphericalPELAlbaneseData E K s q) (hg : D.HasIntegralModelGeometry)
  (j : PELModuli.CMPoints.Arithmetic.QadicChoice K D.complexEmbedding q)
  (hcop : Nat.Coprime q D.denominator)
  (res : AbelianScheme.TateComparison.Data.modelRing K D.denominator →+* ZMod q)
  (hres : res.comp (algebraMap (NumberField.RingOfIntegers K)
    (AbelianScheme.TateComparison.Data.modelRing K D.denominator)) = j.residue)

local notation "A" => OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.AlbaneseModel.CM.comparisonModel D hg j hcop
local notation "G" => OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.ComparisonPolynomial.CM.sourceGroup D res
local notation "e" => OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.ComparisonPolynomial.CM.specialEndTransport D hg j hcop res hres

local instance : GrpObj (G).X := (G).grp
local instance : IsCommMonObj (G).X := (G).comm

def sourceSpecialization : FormalGeometry.Completion.Endomorphisms.Construction.AlgebraicEnd (A).variety.scheme →+* FormalGeometry.Completion.Endomorphisms.Construction.AlgebraicEnd (G).X :=
  (e).symm.toRingHom.comp (Geometric.ComparisonSpecialization.CM.specializeEnd A)

theorem transport_sourceSpecialization (f : FormalGeometry.Completion.Endomorphisms.Construction.AlgebraicEnd (A).variety.scheme) :
    e (sourceSpecialization D hg j hcop res hres f) = Geometric.ComparisonSpecialization.CM.specializeEnd A f :=
  (e).apply_symm_apply _

def rationalTransport : FormalGeometry.Completion.Endomorphisms.Construction.RationalAlgebraicEnd (G).X ≃ₐ[ℚ]
    FormalGeometry.Completion.Endomorphisms.Construction.RationalAlgebraicEnd (A).specialFiber.scheme :=
  Algebra.TensorProduct.congr (AlgEquiv.refl : ℚ ≃ₐ[ℚ] ℚ) (e).toIntAlgEquiv

theorem rationalTransport_tmul (r : ℚ) (f : FormalGeometry.Completion.Endomorphisms.Construction.AlgebraicEnd (G).X) :
    rationalTransport D hg j hcop res hres (r ⊗ₜ[ℤ] f) = r ⊗ₜ[ℤ] e f := by
  rfl

def rationalSourceSpecialization : FormalGeometry.Completion.Endomorphisms.Construction.RationalAlgebraicEnd (A).variety.scheme →ₐ[ℚ]
    FormalGeometry.Completion.Endomorphisms.Construction.RationalAlgebraicEnd (G).X :=
  (rationalTransport D hg j hcop res hres).symm.toAlgHom.comp (Specialized.CM.Hecke.specializeRational A)

theorem rationalSourceSpecialization_tmul (r : ℚ)
    (f : FormalGeometry.Completion.Endomorphisms.Construction.AlgebraicEnd (A).variety.scheme) :
    rationalSourceSpecialization D hg j hcop res hres (r ⊗ₜ[ℤ] f) =
      r ⊗ₜ[ℤ] sourceSpecialization D hg j hcop res hres f := by
  apply (rationalTransport D hg j hcop res hres).injective
  change rationalTransport D hg j hcop res hres
    ((rationalTransport D hg j hcop res hres).symm (Specialized.CM.Hecke.specializeRational A (r ⊗ₜ[ℤ] f))) = _
  rw [AlgEquiv.apply_symm_apply, Specialized.CM.Hecke.specializeRational_tmul, rationalTransport_tmul,
    transport_sourceSpecialization]
  rfl

theorem transport_rationalSourceSpecialization (f : FormalGeometry.Completion.Endomorphisms.Construction.RationalAlgebraicEnd (A).variety.scheme) :
    rationalTransport D hg j hcop res hres
      (rationalSourceSpecialization D hg j hcop res hres f) = Specialized.CM.Hecke.specializeRational A f :=
  (rationalTransport D hg j hcop res hres).apply_symm_apply _

variable {H : Type} [CommRing H] [Algebra ℚ H]

def sourceHeckeAction (ρ : (A).HeckeRealization H) :
    H →ₐ[ℚ] FormalGeometry.Completion.Endomorphisms.Construction.RationalAlgebraicEnd (G).X :=
  (rationalSourceSpecialization D hg j hcop res hres).comp ρ.action

theorem transport_sourceHeckeAction (ρ : (A).HeckeRealization H) (h : H) :
    rationalTransport D hg j hcop res hres (sourceHeckeAction D hg j hcop res hres ρ h) =
      Specialized.CM.Hecke.specializedHeckeAction A ρ h :=
  transport_rationalSourceSpecialization D hg j hcop res hres (ρ.action h)

theorem sourceHeckeAction_presentation (ρ : (A).HeckeRealization H) (h : H) :
    (ρ.presentation h).sum (fun f r =>
      r ⊗ₜ[ℤ] sourceSpecialization D hg j hcop res hres f.generic) =
        sourceHeckeAction D hg j hcop res hres ρ h := by
  calc
    _ = (ρ.presentation h).sum (fun f r =>
        rationalSourceSpecialization D hg j hcop res hres (r ⊗ₜ[ℤ] f.generic)) := by
      apply Finsupp.sum_congr
      intro f _
      exact (rationalSourceSpecialization_tmul D hg j hcop res hres _ f.generic).symm
    _ = rationalSourceSpecialization D hg j hcop res hres
        ((ρ.presentation h).sum (fun f r => r ⊗ₜ[ℤ] f.generic)) :=
      (map_finsuppSum (rationalSourceSpecialization D hg j hcop res hres) _ _).symm
    _ = sourceHeckeAction D hg j hcop res hres ρ h :=
      congrArg (rationalSourceSpecialization D hg j hcop res hres) (ρ.represents h)

theorem sourceHeckeAction_clearing (ρ : (A).HeckeRealization H) (h : H)
    (n : ℕ) (f : FormalGeometry.Completion.Endomorphisms.Construction.AlgebraicEnd (A).variety.scheme)
    (hc : n • ρ.action h = (1 : ℚ) ⊗ₜ[ℤ] f) :
    n • sourceHeckeAction D hg j hcop res hres ρ h =
      (1 : ℚ) ⊗ₜ[ℤ] sourceSpecialization D hg j hcop res hres f := by
  exact (map_nsmul (rationalSourceSpecialization D hg j hcop res hres) n (ρ.action h)).symm.trans
    ((congrArg (rationalSourceSpecialization D hg j hcop res hres) hc).trans
      (rationalSourceSpecialization_tmul D hg j hcop res hres 1 f))

theorem specializedHeckeAction_integral (ρ : (A).HeckeRealization H) (h : H)
    (f : FormalGeometry.Completion.Endomorphisms.Construction.AlgebraicEnd (A).variety.scheme) (hf : ρ.action h = (1 : ℚ) ⊗ₜ[ℤ] f) :
    Specialized.CM.Hecke.specializedHeckeAction A ρ h =
      (1 : ℚ) ⊗ₜ[ℤ] e (sourceSpecialization D hg j hcop res hres f) := by
  change Specialized.CM.Hecke.specializeRational A (ρ.action h) = _
  rw [hf, Specialized.CM.Hecke.specializeRational_tmul, transport_sourceSpecialization]
  rfl

/-- Once the raw ordinary formulas prove the polynomial for the actual
specializations, it holds for the identical GeometricComparison Hecke operators. -/
theorem specializedHecke_polynomial (ρ : (A).HeckeRealization H) (h : Fin 3 → H)
    (f : Fin 3 → FormalGeometry.Completion.Endomorphisms.Construction.AlgebraicEnd (A).variety.scheme)
    (hf : ∀ i, ρ.action (h i) = (1 : ℚ) ⊗ₜ[ℤ] f i)
    (hpoly : Ordinary.Polynomial.CM.heckePolynomialValue q
      (FormalGeometry.Completion.Endomorphisms.Construction.algebraicFrobenius (ZMod q) (G).X)
      (fun i => sourceSpecialization D hg j hcop res hres (f i)) = 0) :
    Ordinary.Polynomial.CM.heckePolynomialValue q
      (FormalGeometry.Completion.Endomorphisms.Construction.rationalAlgebraicFrobenius (ZMod q) (A).specialFiber.scheme)
      (fun i => Specialized.CM.Hecke.specializedHeckeAction A ρ (h i)) = 0 := by
  have hp := ComparisonPolynomial.CM.specialFiber_polynomial D hg j hcop res hres
    (fun i => sourceSpecialization D hg j hcop res hres (f i)) hpoly
  have hr := EndTransport.CM.rational_frobenius_polynomial
    (ComparisonPolynomial.CM.targetGroup D hg j hcop) q
    (fun i => e (sourceSpecialization D hg j hcop res hres (f i))) hp
  have hc : (fun i => Specialized.CM.Hecke.specializedHeckeAction A ρ (h i)) =
      (fun i => (1 : ℚ) ⊗ₜ[ℤ] e (sourceSpecialization D hg j hcop res hres (f i))) :=
    funext (fun i => specializedHeckeAction_integral D hg j hcop res hres ρ (h i) (f i) (hf i))
  rw [hc]
  exact hr

end

end OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Source.Specialization.CM
