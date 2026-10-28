import OAI.AlgebraicGeometry.Crystalline.Cohomology.WittPolynomial.Poincare

/-! # Polynomial Poincare -/

namespace OAI.AlgebraicGeometry.Crystalline.Cohomology.WittPolynomial.PolynomialPoincare.WittPolynomialPoincare

noncomputable section

/-!
# The completed rank-one crystalline Poincaré sequence over W(k)

Completeness and separatedness identify compatible positive p-power
residues with the Witt ring itself. This gives the augmented exact
sequence W(k) → lim Γ(W)/p^e → lim Ω¹_PD and vanishing of higher forms.
-/

open _root_.CategoryTheory

universe u

variable (p : ℕ) [Fact p.Prime] (k : Type u) [Field k] [CharP k p] [PerfectRing k p]

local notation "W" => WittVector p k
local notation "I₀" => Ideal.span {(p : W)}
local notation "L" => OAI.AlgebraicGeometry.Crystalline.Cohomology.WittPolynomial.Thickening.WittPolynomialThickening.baseIdeal p k
local notation "T" => OAI.AlgebraicGeometry.Crystalline.Cohomology.WittPolynomial.Tower.WittPolynomialTower.tower p k
local notation "C" => OAI.AlgebraicGeometry.Crystalline.Cohomology.PD.InverseLimit.PDInverseLimit.Ring p k k T
local notation "Ω" => OAI.AlgebraicGeometry.Crystalline.Cohomology.PD.PDDeRham.CompletedForm p k k T 1
local notation "Coefficients" => OAI.AlgebraicGeometry.Crystalline.Cohomology.WittPolynomial.Poincare.WittPolynomialPoincare.coefficients p k

def ofCoefficients : W →ₗ[W] Coefficients where
  toFun a := ⟨fun n => Ideal.Quotient.mk (L n) a, fun _ _ _ => rfl⟩
  map_add' _ _ := Subtype.ext (funext (fun _ => map_add _ _ _))
  map_smul' w a := Subtype.ext (funext (fun n => (Ideal.Quotient.mkₐ W (L n)).toLinearMap.map_smul w a))

theorem ofCoefficients_injective : Function.Injective (ofCoefficients p k) := by
  intro a b hab
  apply IsHausdorff.eq_iff_smodEq (I := I₀) |>.mpr
  intro n
  have heq : Ideal.Quotient.mk (L n) a = Ideal.Quotient.mk (L n) b :=
    congrArg (fun x : Coefficients => x.val n) hab
  have hm : a - b ∈ I₀ ^ n :=
    Ideal.pow_le_pow_right (Nat.le_succ n) (Ideal.Quotient.eq.mp heq)
  apply SModEq.sub_mem.mpr
  simpa only [Ideal.smul_eq_mul, Ideal.mul_top] using hm

theorem ofCoefficients_surjective : Function.Surjective (ofCoefficients p k) := by
  intro a
  choose f hf using fun n => Ideal.Quotient.mk_surjective (a.val n)
  have hmod (m n : ℕ) (hmn : m ≤ n) :
      Ideal.Quotient.mk (L m) (f n) = Ideal.Quotient.mk (L m) (f m) := by
    calc
      _ = Poincare.WittPolynomialPoincare.coefficientTransition p k m n hmn
          (Ideal.Quotient.mk (L n) (f n)) := rfl
      _ = Poincare.WittPolynomialPoincare.coefficientTransition p k m n hmn (a.val n) :=
        congrArg (Poincare.WittPolynomialPoincare.coefficientTransition p k m n hmn) (hf n)
      _ = a.val m := a.property m n hmn
      _ = _ := (hf m).symm
  have hCauchy : ∀ {m n : ℕ}, m ≤ n →
      f m ≡ f n [SMOD (I₀ ^ m • ⊤ : Submodule W W)] := by
    intro m n hmn
    have hm : f m - f n ∈ I₀ ^ m :=
      Ideal.pow_le_pow_right (Nat.le_succ m) (Ideal.Quotient.eq.mp (hmod m n hmn).symm)
    apply SModEq.sub_mem.mpr
    simpa only [Ideal.smul_eq_mul, Ideal.mul_top] using hm
  obtain ⟨w, hw⟩ := IsPrecomplete.prec (inferInstance : IsPrecomplete I₀ W) hCauchy
  refine ⟨w, Subtype.ext (funext (fun n => ?_))⟩
  have hn : f (n + 1) - w ∈ I₀ ^ (n + 1) := by
    simpa only [Ideal.smul_eq_mul, Ideal.mul_top] using SModEq.sub_mem.mp (hw (n + 1))
  change Ideal.Quotient.mk (L n) w = a.val n
  exact (Ideal.Quotient.eq.mpr hn).symm.trans ((hmod n (n + 1) (Nat.le_succ n)).trans (hf n))

/-- The constant term of the completed crystalline calculation is W(k). -/
def coefficientsEquiv : W ≃ₗ[W] Coefficients :=
  LinearEquiv.ofBijective (ofCoefficients p k)
    ⟨ofCoefficients_injective p k, ofCoefficients_surjective p k⟩

def constants : W →ₗ[W] C :=
  (Poincare.WittPolynomialPoincare.constants p k).comp (ofCoefficients p k)

theorem constants_eq_algebraMap (w : W) : constants p k w = algebraMap W C w := by
  apply PD.InverseLimit.PDInverseLimit.ext p k k T
  intro n
  rfl

def sequence : ShortComplex (ModuleCat.{u} W) :=
  ShortComplex.moduleCatMk (constants p k) (PD.PDDeRham.differentialRing p k k T) (by
    apply LinearMap.ext
    intro w
    exact Poincare.WittPolynomialPoincare.differential_constants p k (ofCoefficients p k w))

def sequenceIso : sequence p k ≅ Poincare.WittPolynomialPoincare.sequence p k :=
  ShortComplex.isoMk (coefficientsEquiv p k).toModuleIso (Iso.refl _) (Iso.refl _)
    (by
      apply ModuleCat.hom_ext
      apply LinearMap.ext
      intro w
      rfl)
    (by
      apply ModuleCat.hom_ext
      apply LinearMap.ext
      intro a
      rfl)

/-- Integral Poincaré exactness for the actual completed crystalline form complex. -/
theorem sequence_shortExact : (sequence p k).ShortExact :=
  ShortComplex.shortExact_of_iso (sequenceIso p k).symm
    (Poincare.WittPolynomialPoincare.sequence_shortExact p k)

end

end OAI.AlgebraicGeometry.Crystalline.Cohomology.WittPolynomial.PolynomialPoincare.WittPolynomialPoincare
