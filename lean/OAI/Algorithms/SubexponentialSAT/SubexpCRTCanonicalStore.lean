import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SubexpPolynomialPowerProgram
import OAI.Algorithms.SubexponentialSAT.SubexpLocalSeedProgram

namespace OAI.Algorithms

/-! The literal clean local-store representation used by the outer loop.
The readiness proof checks native multiplication, addition, and negation
views, and the actual cache-initialization updates, coordinate by coordinate.
-/

namespace SubexponentialSAT.SubexpCRTCanonicalInput

attribute [local simp] Fin.coe_ofNat_eq_mod

open SubexpLiftRing SubexpQuarticRing SubexpConvolutionControl
open SubexpPolynomialPowerProgram

structure Context where
  modulus : List Bool
  width : List Bool
  reduction : List Bool
  exponent : List Bool
  one : List Bool
  minusOne : List Bool
  theta : List Bool
  nodes : List Bool
  index : List Bool
  jet : List Bool
  dimension : List Bool
  zero : List Bool

def store (c : Context) (j : Fin 256) : List Bool :=
  if h : 128 ≤ j.val ∧ j.val < 205 then
    SubexpQuarticFlatMul.bankStore (fun _ => []) c.modulus c.reduction c.width []
      ⟨j.val - 128, by omega⟩
  else if j = 5 then c.modulus else if j = 10 then c.width else
  if j = 104 then c.zero else if j = 206 then c.exponent else
  if j = 207 then c.one else if j = 211 then c.minusOne else
  if j = 213 then c.theta else if j = 214 then c.nodes else
  if j = 216 then c.index else if j = 225 then c.jet else
  if j = 243 then c.dimension else []

theorem store_high (c : Context) (i : Fin 77) :
    store c (SubexpConvolutionPair.highPort i) =
      SubexpQuarticFlatMul.bankStore (fun _ => []) c.modulus c.reduction c.width [] i := by
  have h1 : 128 ≤ 128 + i.val := by omega
  have h2 : 128 + i.val < 205 := by omega
  simp [store, SubexpConvolutionPair.highPort, h1, h2]

variable (p D : ℕ) [Fact p.Prime] (M : SubexpPreparedQuartic.Modulus p (D + 1))

abbrev Coeff := Coefficient p (D + 1)
abbrev Poly := FixedPolynomial p (D + 1) D

def context (t theta one : Coeff p D) (minusOne : Word (baseWidth p (D + 1)))
    (width exponent : List Bool) (nodes : List (Coeff p D)) (index : List Bool) (J : Poly p D) :
    Context where
  modulus := M.bits
  width := width
  reduction := SubexpFlatAdd.encode t
  exponent := exponent
  one := SubexpFlatAdd.encode one
  minusOne := minusOne.val
  theta := SubexpFlatAdd.encode theta
  nodes := nodes.flatMap SubexpFlatAdd.encode
  index := index
  jet := encode p (D + 1) J
  dimension := List.replicate D true
  zero := List.replicate (4 * baseWidth p (D + 1)) false

def canonical (t theta one : Coeff p D) (minusOne : Word (baseWidth p (D + 1)))
    (width exponent : List Bool) (nodes : List (Coeff p D)) (index : List Bool) (J : Poly p D) :
    Store := store (context p D M t theta one minusOne width exponent nodes index J)

variable (t theta one : Coeff p D) (minusOne : Word (baseWidth p (D + 1)))
  (width exponent : List Bool) (nodes : List (Coeff p D)) (index : List Bool) (J : Poly p D)

local notation "s" => canonical p D M t theta one minusOne width exponent nodes index J

omit [Fact p.Prime] in
theorem baseReady (hw : width.length = baseWidth p (D + 1)) :
    SubexpConvolutionPairSpec.BaseReady p (D + 1) M s t width (fun _ => []) := by
  constructor
  · intro i _ _
    rw [canonical, store_high]
    simp only [context, SubexpConvolutionPair.flat_eq_encode]
  · intro i
    fin_cases i <;> simp [canonical, store, context, SubexpConvolutionPair.lowPort,
      SubexpJetCellProgram.scalarPorts, SubexpFlatAdd.ready, SubexpFlatAdd.state,
      SubexpFlatAdd.stacks, Fin.addCases, Fin.coe_ofNat_eq_mod]
  · simp [canonical, store, context]
  · exact hw
  · intro i hlo hhi
    have h5 : i ≠ 5 := by intro h; subst i; norm_num at hlo
    have h10 : i ≠ 10 := by intro h; subst i; norm_num at hlo
    have h104 : i ≠ 104 := by intro h; subst i; norm_num at hlo
    have hn : ¬ (128 ≤ i.val ∧ i.val < 205) := by omega
    have h206 : i ≠ 206 := by intro h; subst i; norm_num at hhi
    have h207 : i ≠ 207 := by intro h; subst i; norm_num at hhi
    have h211 : i ≠ 211 := by intro h; subst i; norm_num at hhi
    have h213 : i ≠ 213 := by intro h; subst i; norm_num at hhi
    have h214 : i ≠ 214 := by intro h; subst i; norm_num at hhi
    have h216 : i ≠ 216 := by intro h; subst i; norm_num at hhi
    have h225 : i ≠ 225 := by intro h; subst i; norm_num at hhi
    have h243 : i ≠ 243 := by intro h; subst i; norm_num at hhi
    simp [canonical, store, hn, h5, h10, h104, h206, h207, h211, h213, h214, h216, h225, h243]

omit [Fact p.Prime] in
theorem blank_negation : ∀ i,
    s (SubexpLocalLinearFactorProgram.negatePorts i) =
      SubexpLocalSeedProgram.blankNegation minusOne.val M.bits width i := by
  intro i
  fin_cases i <;> simp [canonical, store, context, SubexpLocalLinearFactorProgram.negatePorts,
    SubexpLocalSeedProgram.blankNegation, SubexpQuarticFlatNeg.bankStore,
    SubexpQuarticFlatNeg.emptyBank, Fin.coe_ofNat_eq_mod]

end SubexponentialSAT.SubexpCRTCanonicalInput

end OAI.Algorithms
