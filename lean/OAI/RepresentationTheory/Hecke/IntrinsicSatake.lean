import OAI.RepresentationTheory.Hecke.GaloisValuationIntrinsic
import OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.SatakeBaseChange

/-! # Intrinsic Satake -/

namespace OAI.RepresentationTheory.Hecke.IntrinsicSatake.GaloisValuationIntrinsic

noncomputable section

/-! Instantiate the full RationalStructure proposition on the actual rational constant term.
The auxiliary ambient lattice includes the negatives of the native three
coordinates with zero multiplier, matching RationalStructure's opposite rho convention.
Descent is evaluated back on the native coordinates. -/

open scoped Classical TensorProduct
open OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.SatakeBaseChange.Iwasawa
open OAI.RepresentationTheory.Satake.RationalStructure.Construction

abbrev Lattice := (⊤ : AddSubgroup (Satake.RationalStructure.Construction.AmbientCocharacters 1))

def embedHeight : (Fin 3 → ℤ) →+ Lattice where
  toFun ell := ⟨(fun _ => -ell, 0), trivial⟩
  map_zero' := by
    apply Subtype.ext
    apply Prod.ext
    · funext i k
      exact neg_zero
    · rfl
  map_add' a b := by
    apply Subtype.ext
    apply Prod.ext
    · funext i k
      change -(a k + b k) = -a k + -b k
      abel
    · rfl

def readHeight : Lattice →+ (Fin 3 → ℤ) where
  toFun l := -l.val.1 0
  map_zero' := by simp
  map_add' a b := by
    change -(a.val.1 0 + b.val.1 0) = -a.val.1 0 + -b.val.1 0
    abel

theorem read_embed (ell : Fin 3 → ℤ) : readHeight (embedHeight ell) = ell := by
  change -(-ell) = ell
  exact neg_neg ell

theorem embedHeight_injective : Function.Injective embedHeight :=
  Function.LeftInverse.injective read_embed

theorem rho_embed (ell : Fin 3 → ℤ) : Satake.RationalStructure.Construction.rhoPairing (embedHeight ell) = ell 2 - ell 0 := by
  simp [Satake.RationalStructure.Construction.rhoPairing, embedHeight]
  ring

variable (q : ℕ) [Fact q.Prime]

def rationalCoefficients (T : Theta.Geometric.SphericalGU.Spherical.SL3Hecke q) : Lattice →₀ ℚ :=
  Finsupp.mapDomain embedHeight (AlgebraicGeometry.HodgeConjecture.CMExtraction.RadialSatake.Iwasawa.rationalSatakeCoefficients q T)

def complexTransform : (Theta.Geometric.SphericalGU.Spherical.SL3Hecke q →₀ ℂ) →ₗ[ℂ] (Lattice →₀ ℂ) :=
  Finsupp.linearCombination ℂ (fun T => Satake.RationalStructure.Construction.extendQ (rationalCoefficients q T))

def rawCoefficient (T : Theta.Geometric.SphericalGU.Spherical.SL3Hecke q) (l : Lattice) : ℚ :=
  rationalCoefficients q T l * (q : ℚ) ^ (-Satake.RationalStructure.Construction.rhoPairing l)

theorem rawCoefficient_native (T : Theta.Geometric.SphericalGU.Spherical.SL3Hecke q) (ell : Fin 3 → ℤ) :
    rawCoefficient q T (embedHeight ell) =
      Finsupp.mapDomain (AlgebraicGeometry.HodgeConjecture.CMExtraction.Borel.Iwasawa.decomposition q).height
        (Theta.Geometric.SphericalGU.Spherical.kernel (Theta.Geometric.SphericalGU.Spherical.integralSL3 q) T) ell := by
  unfold rawCoefficient rationalCoefficients
  rw [Finsupp.mapDomain_apply_of_injective embedHeight_injective, rho_embed]
  simp only [AlgebraicGeometry.HodgeConjecture.CMExtraction.RadialSatake.Iwasawa.rationalSatakeCoefficients, Finsupp.onFinset_apply, zpow_neg]
  have hq : (q : ℚ) ≠ 0 := by exact_mod_cast (Fact.out : q.Prime).ne_zero
  exact mul_inv_cancel_right₀ (zpow_ne_zero _ hq) _

theorem complexTransform_single (T : Theta.Geometric.SphericalGU.Spherical.SL3Hecke q) :
    complexTransform q (Finsupp.single T 1) = Satake.RationalStructure.Construction.extendQ (rationalCoefficients q T) := by
  simp [complexTransform]

theorem native_formula (T : Theta.Geometric.SphericalGU.Spherical.SL3Hecke q) (l : Lattice) :
    complexTransform q (Finsupp.single T 1) l =
      (q : ℂ) ^ Satake.RationalStructure.Construction.rhoPairing l * (rawCoefficient q T l : ℂ) := by
  rw [complexTransform_single]
  have hq : (q : ℂ) ≠ 0 := by exact_mod_cast (Fact.out : q.Prime).ne_zero
  change (rationalCoefficients q T l : ℂ) =
    (q : ℂ) ^ Satake.RationalStructure.Construction.rhoPairing l *
      ((rationalCoefficients q T l * (q : ℚ) ^ (-Satake.RationalStructure.Construction.rhoPairing l) : ℚ) : ℂ)
  push_cast
  rw [zpow_neg]
  field_simp

/-- This is the full RationalStructure input specialized to native Hecke coefficients. -/
theorem rational_descent (hRationalStructure : GaloisValuationIntrinsic.Intrinsic.RationalStructure.Proposition.{0}) :
    ∃ SQ : (Theta.Geometric.SphericalGU.Spherical.SL3Hecke q →₀ ℚ) →ₗ[ℚ] (Lattice →₀ ℚ),
      ∀ T, SQ (Finsupp.single T 1) = rationalCoefficients q T := by
  obtain ⟨SQ, hSQ⟩ := (hRationalStructure 1 ⊤ (Theta.Geometric.SphericalGU.Spherical.SL3Hecke q) q
    (Fact.out : q.Prime) (rawCoefficient q) (complexTransform q) (native_formula q)).1
  refine ⟨SQ, ?_⟩
  intro T
  have h := hSQ (Finsupp.single T 1)
  have he : Satake.RationalStructure.Construction.extendQ (Finsupp.single T (1 : ℚ)) = Finsupp.single T (1 : ℂ) := by
    simp [Satake.RationalStructure.Construction.extendQ]
  rw [he, complexTransform_single] at h
  ext l
  have hl := DFunLike.congr_fun h l
  exact (algebraMap ℚ ℂ).injective hl

def evaluate {k : Type*} [Field k] [Algebra ℚ k]
    (β : Fin 3 → kˣ) (f : Lattice →₀ ℚ) : k :=
  f.sum (fun l a => algebraMap ℚ k a *
    (AlgebraicGeometry.HodgeConjecture.CMExtraction.SatakeBaseChange.Iwasawa.torusCharacterOver β (Multiplicative.ofAdd (readHeight l)) : k))

theorem evaluate_native {k : Type*} [Field k] [Algebra ℚ k]
    (β : Fin 3 → kˣ) (T : Theta.Geometric.SphericalGU.Spherical.SL3Hecke q) :
    evaluate β (rationalCoefficients q T) = AlgebraicGeometry.HodgeConjecture.CMExtraction.SatakeBaseChange.Iwasawa.torusSatakeOver q β T := by
  unfold evaluate rationalCoefficients
  rw [Finsupp.sum_mapDomain_index]
  · unfold AlgebraicGeometry.HodgeConjecture.CMExtraction.SatakeBaseChange.Iwasawa.torusSatakeOver AlgebraicGeometry.HodgeConjecture.CMExtraction.SatakeBaseChange.Iwasawa.rationalLatticeEvaluation
    rw [AlgHom.comp_apply, AddMonoidAlgebra.lift_apply']
    simp only [read_embed]
    rfl
  · intro l
    simp
  · intro l a b
    simp only [map_add, add_mul]

theorem evaluate_map {k k' : Type*} [Field k] [Field k']
    [Algebra ℚ k] [Algebra ℚ k'] (j : k →ₐ[ℚ] k')
    (β : Fin 3 → kˣ) (f : Lattice →₀ ℚ) :
    j (evaluate β f) = evaluate (fun i => Units.map j.toMonoidHom (β i)) f := by
  unfold evaluate
  rw [map_finsuppSum]
  apply Finsupp.sum_congr
  intro l _
  rw [map_mul, j.commutes]
  congr 1
  exact AlgebraicGeometry.HodgeConjecture.CMExtraction.SatakeBaseChange.Iwasawa.torusCharacterOver_map j.toRingHom β (Multiplicative.ofAdd (readHeight l))

/-- RationalStructure's rational descent yields scalar equivariance of the actual native
Satake evaluation, over any characteristic-zero coefficient fields. -/
theorem satake_map (hRationalStructure : GaloisValuationIntrinsic.Intrinsic.RationalStructure.Proposition.{0})
    {k k' : Type*} [Field k] [Field k'] [Algebra ℚ k] [Algebra ℚ k']
    (j : k →ₐ[ℚ] k') (β : Fin 3 → kˣ) (T : Theta.Geometric.SphericalGU.Spherical.SL3Hecke q) :
    j (AlgebraicGeometry.HodgeConjecture.CMExtraction.SatakeBaseChange.Iwasawa.torusSatakeOver q β T) =
      AlgebraicGeometry.HodgeConjecture.CMExtraction.SatakeBaseChange.Iwasawa.torusSatakeOver q (fun i => Units.map j.toMonoidHom (β i)) T := by
  obtain ⟨SQ, hSQ⟩ := rational_descent q hRationalStructure
  have hvalue (γ : Fin 3 → kˣ) :
      AlgebraicGeometry.HodgeConjecture.CMExtraction.SatakeBaseChange.Iwasawa.torusSatakeOver q γ T = evaluate γ (SQ (Finsupp.single T 1)) := by
    rw [hSQ, evaluate_native]
  rw [hvalue, evaluate_map, hSQ, evaluate_native]

end

end OAI.RepresentationTheory.Hecke.IntrinsicSatake.GaloisValuationIntrinsic
