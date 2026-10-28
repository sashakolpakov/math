import OAI.AlgebraicGeometry.Crystalline.Cohomology.Multivariable.Forms
import OAI.AlgebraicGeometry.Crystalline.Cohomology.PD.FormSurjective
import OAI.AlgebraicGeometry.Crystalline.Cohomology.Base.IdealQuotient
import Mathlib.RingTheory.DividedPowers.SubDPIdeal

/-! # Quotient Multivariable D -/

namespace OAI.AlgebraicGeometry.Crystalline.Cohomology.QuotientMultivariableD.QuotientMultivariableForms

noncomputable section

/-!
# Actual multivariable PD forms modulo base ideals

For a base sub-DP ideal, the inherited quotient divided powers support
the descended coordinate derivatives. Their duality with the coordinate
differentials proves an actual form basis on the finite quotient.
-/

open _root_.CategoryTheory Classical

universe u

variable (R σ K : Type u) [CommRing R] [Field K] [CharZero K] [Algebra R K]
  (h : Function.Injective (algebraMap R K))
  (I : Ideal R) (δ : DividedPowers I) (hunit : ∃ a ∈ I, IsUnit (algebraMap R K a))
  (L : Ideal R) (hL : DividedPowers.IsSubDPIdeal δ L)

local notation "G" => DividedPowerAlgebra R (σ →₀ R)
local notation "IG" => OAI.AlgebraicGeometry.Crystalline.Cohomology.Multivariable.DividedPowers.MultivariableDividedPowers.ideal R σ I
local notation "γ" => OAI.AlgebraicGeometry.Crystalline.Cohomology.Multivariable.DividedPowers.MultivariableDividedPowers.dividedPowers R σ K h I δ hunit
local notation "Q" => L.map (algebraMap R G)

def Ring := G ⧸ Q

instance ringCommRing : CommRing (Ring R σ L) := inferInstanceAs (CommRing (G ⧸ Q))

instance ringAlgebra : Algebra R (Ring R σ L) := inferInstanceAs (Algebra R (G ⧸ Q))

def quotient : G →ₐ[R] Ring R σ L := Ideal.Quotient.mkₐ R Q

def ideal : Ideal (Ring R σ L) := (IG).map (quotient R σ L).toRingHom

include hL in
theorem quotient_subDP : DividedPowers.IsSubDPIdeal γ Q :=
  DividedPowers.isSubDPIdeal_map_of_isSubDPIdeal
    (Multivariable.DividedPowers.MultivariableDividedPowers.base_isDPMorphism R σ K h I δ hunit) hL

include hL in
theorem kernel_subDP : DividedPowers.IsSubDPIdeal γ
    (RingHom.ker (quotient R σ L).toRingHom ⊓ IG) := by
  change DividedPowers.IsSubDPIdeal γ (RingHom.ker (Ideal.Quotient.mk Q) ⊓ IG)
  rw [Ideal.mk_ker, inf_of_le_left (quotient_subDP R σ K h I δ hunit L hL).1]
  exact quotient_subDP R σ K h I δ hunit L hL

def dividedPowers : DividedPowers (A := Ring R σ L) (ideal R σ I L) :=
  DividedPowers.Quotient.OfSurjective.dividedPowers γ
    (f := (quotient R σ L).toRingHom) (J := ideal R σ I L)
    Ideal.Quotient.mk_surjective rfl (kernel_subDP R σ K h I δ hunit L hL)

theorem quotient_isDPMorphism :
    DividedPowers.IsDPMorphism γ (QuotientMultivariableForms.dividedPowers R σ K h I δ hunit L hL) (quotient R σ L).toRingHom :=
  DividedPowers.Quotient.OfSurjective.isDPMorphism (A := G) (B := Ring R σ L)
    (I := IG) (J := ideal R σ I L) γ (f := (quotient R σ L).toRingHom)
    Ideal.Quotient.mk_surjective rfl (kernel_subDP R σ K h I δ hunit L hL)

local notation "B" => OAI.AlgebraicGeometry.Crystalline.Cohomology.QuotientMultivariableD.QuotientMultivariableForms.Ring R σ L
local notation "IB" => OAI.AlgebraicGeometry.Crystalline.Cohomology.QuotientMultivariableD.QuotientMultivariableForms.ideal R σ I L
local notation "ε" => OAI.AlgebraicGeometry.Crystalline.Cohomology.QuotientMultivariableD.QuotientMultivariableForms.dividedPowers R σ K h I δ hunit L hL
local notation "q" => OAI.AlgebraicGeometry.Crystalline.Cohomology.QuotientMultivariableD.QuotientMultivariableForms.quotient R σ L
local notation "hq" => OAI.AlgebraicGeometry.Crystalline.Cohomology.QuotientMultivariableD.QuotientMultivariableForms.quotient_isDPMorphism R σ K h I δ hunit L hL
local notation "dG" => OAI.AlgebraicGeometry.Crystalline.Cohomology.Multivariable.CoordinateDerivation.MultivariableCoordinateDerivation.derivation R σ K h I δ hunit

def coordinate (i : σ) : B := q (Multivariable.DividedAlgebra.MultivariableDividedAlgebra.generator R σ 1 i)

def derivation (i : σ) : Derivation R B B := Base.IdealQuotient.BaseIdealQuotient.derivation L (dG i)

theorem derivation_quotient (i : σ) (a : G) :
    derivation R σ K h I δ hunit L i (q a) = q (dG i a) :=
  Base.IdealQuotient.BaseIdealQuotient.derivation_mk L (dG i) a

theorem derivation_dpow (i : σ) (n : ℕ) (a : B) (hx : a ∈ IB) :
    derivation R σ K h I δ hunit L i ((ε).dpow (n + 1) a) =
      (ε).dpow n a • derivation R σ K h I δ hunit L i a := by
  obtain ⟨a, ha, rfl⟩ := (Ideal.mem_map_iff_of_surjective (q).toRingHom
    Ideal.Quotient.mk_surjective).mp hx
  have hm (m : ℕ) : q ((γ).dpow m a) = (ε).dpow m (q a) := (hq).map_dpow ha
  change derivation R σ K h I δ hunit L i ((ε).dpow (n + 1) (q a)) =
    (ε).dpow n (q a) * derivation R σ K h I δ hunit L i (q a)
  rw [← hm (n + 1), derivation_quotient,
    Multivariable.CoordinateDerivation.MultivariableCoordinateDerivation.derivation_dpow R σ K h I δ hunit i n ha,
    map_mul, hm n, derivation_quotient]

theorem derivation_coordinate (i j : σ) :
    derivation R σ K h I δ hunit L i (coordinate R σ L j) = if j = i then 1 else 0 := by
  rw [coordinate, derivation_quotient, Multivariable.CoordinateDerivation.MultivariableCoordinateDerivation.derivation_coordinate]
  split_ifs <;> simp only [map_one, map_zero]

theorem derivations_commute (i j : σ) :
    Function.Commute (derivation R σ K h I δ hunit L i) (derivation R σ K h I δ hunit L j) := by
  intro a
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective a
  change derivation R σ K h I δ hunit L i (derivation R σ K h I δ hunit L j (q a)) =
    derivation R σ K h I δ hunit L j (derivation R σ K h I δ hunit L i (q a))
  rw [derivation_quotient, derivation_quotient, derivation_quotient, derivation_quotient,
    Multivariable.CoordinateDerivation.MultivariableCoordinateDerivation.derivations_commute]

def formMap (n : ℕ) : PD.DeRham.PDDeRham.Form R G IG γ n →ₗ[R] PD.DeRham.PDDeRham.Form R B IB ε n :=
  PD.DeRhamGlobal.PDDeRhamGlobal.formMap (CommAlgCat.ofHom q) hq n

theorem formMap_D (a : G) : formMap R σ K h I δ hunit L hL 1 (PD.OneForms.PDOneForms.D R G IG γ a) =
    PD.OneForms.PDOneForms.D R B IB ε (q a) := PD.FormSurjective.PDFormSurjective.formMap_D (CommAlgCat.ofHom q) hq a

variable [Fintype σ]

theorem D_eq_sum (a : B) : PD.OneForms.PDOneForms.D R B IB ε a =
    ∑ i, derivation R σ K h I δ hunit L i a • PD.OneForms.PDOneForms.D R B IB ε (coordinate R σ L i) := by
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective a
  change PD.OneForms.PDOneForms.D R B IB ε (q a) = _
  rw [← formMap_D, Multivariable.Forms.MultivariableForms.D_eq_sum R σ K h I δ hunit, map_sum]
  apply Finset.sum_congr rfl
  intro i _
  have hs := PD.DeRhamGlobal.PDDeRhamGlobal.formMap_smul (CommAlgCat.ofHom q) hq 1 (dG i a)
    (PD.OneForms.PDOneForms.D R G IG γ (Multivariable.DividedAlgebra.MultivariableDividedAlgebra.generator R σ 1 i))
  change formMap R σ K h I δ hunit L hL 1 (dG i a • _) =
    q (dG i a) • formMap R σ K h I δ hunit L hL 1 _ at hs
  change formMap R σ K h I δ hunit L hL 1 (dG i a • _) =
    derivation R σ K h I δ hunit L i (q a) • PD.OneForms.PDOneForms.D R B IB ε (coordinate R σ L i)
  rw [hs, formMap_D, derivation_quotient]
  rfl

def basis : Module.Basis σ B (PD.DeRham.PDDeRham.Form R B IB ε 1) :=
  PD.CoordinateBasis.PDCoordinateBasis.basis R B σ IB ε (coordinate R σ L) (derivation R σ K h I δ hunit L)
    (derivation_dpow R σ K h I δ hunit L hL) (D_eq_sum R σ K h I δ hunit L hL)
    (derivation_coordinate R σ K h I δ hunit L)

theorem basis_apply (i : σ) : basis R σ K h I δ hunit L hL i =
    PD.OneForms.PDOneForms.D R B IB ε (coordinate R σ L i) :=
  PD.CoordinateBasis.PDCoordinateBasis.basis_apply R B σ IB ε (coordinate R σ L) (derivation R σ K h I δ hunit L)
    (derivation_dpow R σ K h I δ hunit L hL) (D_eq_sum R σ K h I δ hunit L hL)
    (derivation_coordinate R σ K h I δ hunit L) i

end

end OAI.AlgebraicGeometry.Crystalline.Cohomology.QuotientMultivariableD.QuotientMultivariableForms
