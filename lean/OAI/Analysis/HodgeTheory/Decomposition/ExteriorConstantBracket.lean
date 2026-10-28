import OAI.Analysis.HodgeTheory.Decomposition.CovectorSymbolAction
import OAI.Analysis.DifferentialForms.Manifold.ExteriorDerivativeSmooth

/-! # Exterior Constant Bracket -/

namespace OAI.Analysis.HodgeTheory.Decomposition.ExteriorConstantBracket.Constructions

noncomputable section

section

/-! Exterior differentiation with a constant direction map. Its derivative
is an explicit alternation of the actual second Fréchet derivative. -/

open scoped ContDiff

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

def alternationWithDirection (n : ℕ) (A : E →L[ℝ] E) :
    (E →L[ℝ] DifferentialForms.Manifold.Basic.FormValue E n) →L[ℝ] DifferentialForms.Manifold.Basic.FormValue E (n + 1) :=
  (ContinuousAlternatingMap.alternatizeUncurryFinCLM ℝ E ℂ).comp
    ((ContinuousLinearMap.compL ℝ E E (DifferentialForms.Manifold.Basic.FormValue E n)).flip A)

theorem alternationWithDirection_apply (n : ℕ) (A : E →L[ℝ] E) (L : E →L[ℝ] DifferentialForms.Manifold.Basic.FormValue E n) :
    alternationWithDirection n A L = ContinuousAlternatingMap.alternatizeUncurryFin (L.comp A) := rfl

def directionalExteriorDerivative (n : ℕ) (A : E →L[ℝ] E) (a : E → DifferentialForms.Manifold.Basic.FormValue E n) (x : E) :
    DifferentialForms.Manifold.Basic.FormValue E (n + 1) := alternationWithDirection n A (fderiv ℝ a x)

theorem directionalExteriorDerivative_id (n : ℕ) (a : E → DifferentialForms.Manifold.Basic.FormValue E n) :
    directionalExteriorDerivative n (ContinuousLinearMap.id ℝ E) a = extDeriv a := by
  funext x
  rw [directionalExteriorDerivative, alternationWithDirection_apply, ContinuousLinearMap.comp_id]
  rfl

theorem directionalExteriorDerivative_twisted (n : ℕ) (A : E →L[ℝ] E) (a : E → DifferentialForms.Manifold.Basic.FormValue E n) :
    CovectorSymbolAction.Constructions.twistedExteriorDerivative n A a = fun x => -directionalExteriorDerivative n A a x := rfl

theorem directionalExteriorDerivative_smoothOn (n : ℕ) (A : E →L[ℝ] E)
    (a : E → DifferentialForms.Manifold.Basic.FormValue E n) {U : Set E} (hU : IsOpen U) (ha : ContDiffOn ℝ ∞ a U) :
    ContDiffOn ℝ ∞ (directionalExteriorDerivative n A a) U :=
  (alternationWithDirection n A).contDiff.comp_contDiffOn (ha.fderiv_of_isOpen hU (by simp))

theorem directionalExteriorDerivative_fderiv (n : ℕ) (A : E →L[ℝ] E)
    (a : E → DifferentialForms.Manifold.Basic.FormValue E n) {x : E} (ha : ContDiffAt ℝ ∞ a x) :
    fderiv ℝ (directionalExteriorDerivative n A a) x =
      (alternationWithDirection n A).comp (fderiv ℝ (fderiv ℝ a) x) := by
  have hs : ContDiffAt ℝ ∞ (fderiv ℝ a) x := ha.fderiv_right (by simp)
  have hd := hs.differentiableAt (by simp)
  exact ((alternationWithDirection n A).hasFDerivAt.comp x hd.hasFDerivAt).fderiv

def secondDerivativeDirections (n : ℕ) (A B : E →L[ℝ] E)
    (T : E →L[ℝ] E →L[ℝ] DifferentialForms.Manifold.Basic.FormValue E n) : E →L[ℝ] E →L[ℝ] DifferentialForms.Manifold.Basic.FormValue E n :=
  ((ContinuousLinearMap.compL ℝ E E (DifferentialForms.Manifold.Basic.FormValue E n)).flip B).comp (T.comp A)

theorem directionalExteriorDerivative_twice (n : ℕ) (A B : E →L[ℝ] E)
    (a : E → DifferentialForms.Manifold.Basic.FormValue E n) {x : E} (ha : ContDiffAt ℝ ∞ a x) :
    directionalExteriorDerivative (n + 1) A (directionalExteriorDerivative n B a) x =
      ContinuousAlternatingMap.alternatizeUncurryFin
        ((ContinuousAlternatingMap.alternatizeUncurryFinCLM ℝ E ℂ).comp
          (secondDerivativeDirections n A B (fderiv ℝ (fderiv ℝ a) x))) := by
  rw [directionalExteriorDerivative, directionalExteriorDerivative_fderiv n B a ha,
    alternationWithDirection_apply]
  rfl

end

section

/-! Constant-direction exterior derivatives square to zero and anticommute.
Both statements follow from symmetry of the actual second derivative. -/

open scoped ContDiff

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

local instance constantFormLinearNormed (n : ℕ) : NormedAddCommGroup (E →L[ℝ] DifferentialForms.Manifold.Basic.FormValue E n) := inferInstance
local instance constantFormLinearNormedSpace (n : ℕ) : NormedSpace ℝ (E →L[ℝ] DifferentialForms.Manifold.Basic.FormValue E n) := inferInstance

theorem directionalExteriorDerivative_squared (n : ℕ) (A : E →L[ℝ] E)
    (a : E → DifferentialForms.Manifold.Basic.FormValue E n) {x : E} (ha : ContDiffAt ℝ ∞ a x) :
    directionalExteriorDerivative (n + 1) A (directionalExteriorDerivative n A a) x = 0 := by
  rw [directionalExteriorDerivative_twice n A A a ha]
  apply ContinuousAlternatingMap.alternatizeUncurryFin_alternatizeUncurryFinCLM_comp_of_symmetric
  intro u v
  change fderiv ℝ (fderiv ℝ a) x (A u) (A v) = fderiv ℝ (fderiv ℝ a) x (A v) (A u)
  exact ha.isSymmSndFDerivAt (by
      rw [minSmoothness_of_isRCLikeNormedField]
      exact WithTop.coe_le_coe.mpr (show (2 : ℕ∞) ≤ ⊤ from le_top)) _ _

theorem directionalExteriorDerivative_anticommute (n : ℕ) (A B : E →L[ℝ] E)
    (a : E → DifferentialForms.Manifold.Basic.FormValue E n) {x : E} (ha : ContDiffAt ℝ ∞ a x) :
    directionalExteriorDerivative (n + 1) A (directionalExteriorDerivative n B a) x +
      directionalExteriorDerivative (n + 1) B (directionalExteriorDerivative n A a) x = 0 := by
  rw [directionalExteriorDerivative_twice n A B a ha, directionalExteriorDerivative_twice n B A a ha]
  let T := fderiv ℝ (fderiv ℝ a) x
  have hT : ∀ u v, T u v = T v u :=
    ha.isSymmSndFDerivAt (by
      rw [minSmoothness_of_isRCLikeNormedField]
      exact WithTop.coe_le_coe.mpr (show (2 : ℕ∞) ≤ ⊤ from le_top))
  have hsym : ∀ u v, (secondDerivativeDirections n A B T + secondDerivativeDirections n B A T) u v =
      (secondDerivativeDirections n A B T + secondDerivativeDirections n B A T) v u := by
    intro u v
    change T (A u) (B v) + T (B u) (A v) = T (A v) (B u) + T (B v) (A u)
    rw [hT (A u) (B v), hT (B u) (A v), add_comm]
  have h := ContinuousAlternatingMap.alternatizeUncurryFin_alternatizeUncurryFinCLM_comp_of_symmetric hsym
  rw [ContinuousLinearMap.comp_add, ContinuousAlternatingMap.alternatizeUncurryFin_add] at h
  exact h

end

section

/-! The actual complex-structure-twisted exterior derivative squares to
zero and anticommutes with the actual exterior derivative. -/

open scoped ContDiff

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem directionalExteriorDerivative_neg (n : ℕ) (A : E →L[ℝ] E)
    (a : E → DifferentialForms.Manifold.Basic.FormValue E n) (x : E) :
    directionalExteriorDerivative n A (fun y => -a y) x = -directionalExteriorDerivative n A a x := by
  rw [directionalExteriorDerivative, fderiv_fun_neg]
  exact (alternationWithDirection n A).map_neg (fderiv ℝ a x)

theorem twistedExteriorDerivative_smoothOn (n : ℕ) (A : E →L[ℝ] E)
    (a : E → DifferentialForms.Manifold.Basic.FormValue E n) {U : Set E} (hU : IsOpen U) (ha : ContDiffOn ℝ ∞ a U) :
    ContDiffOn ℝ ∞ (CovectorSymbolAction.Constructions.twistedExteriorDerivative n A a) U :=
  (directionalExteriorDerivative_smoothOn n A a hU ha).neg

theorem twistedExteriorDerivative_squared (n : ℕ) (A : E →L[ℝ] E)
    (a : E → DifferentialForms.Manifold.Basic.FormValue E n) {x : E} (ha : ContDiffAt ℝ ∞ a x) :
    CovectorSymbolAction.Constructions.twistedExteriorDerivative (n + 1) A (CovectorSymbolAction.Constructions.twistedExteriorDerivative n A a) x = 0 := by
  simp only [directionalExteriorDerivative_twisted]
  rw [directionalExteriorDerivative_neg, directionalExteriorDerivative_squared n A a ha, neg_zero, neg_zero]

theorem twistedExteriorDerivative_anticommute (n : ℕ) (A : E →L[ℝ] E)
    (a : E → DifferentialForms.Manifold.Basic.FormValue E n) {x : E} (ha : ContDiffAt ℝ ∞ a x) :
    extDeriv (CovectorSymbolAction.Constructions.twistedExteriorDerivative n A a) x + CovectorSymbolAction.Constructions.twistedExteriorDerivative (n + 1) A (extDeriv a) x = 0 := by
  rw [← directionalExteriorDerivative_id (n + 1), ← directionalExteriorDerivative_id n]
  simp only [directionalExteriorDerivative_twisted]
  rw [directionalExteriorDerivative_neg, ← neg_add,
    directionalExteriorDerivative_anticommute n (ContinuousLinearMap.id ℝ E) A a ha, neg_zero]

end

section

/-! Locality and linearity of the genuine constant-direction and twisted
exterior operators on differentiable coefficient fields. -/

open scoped _root_.Topology

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem directionalExteriorDerivative_congr (n : ℕ) (A : E →L[ℝ] E)
    {a b : E → DifferentialForms.Manifold.Basic.FormValue E n} {x : E} (h : a =ᶠ[𝓝 x] b) :
    directionalExteriorDerivative n A a x = directionalExteriorDerivative n A b x := by
  rw [directionalExteriorDerivative, h.fderiv_eq]
  rfl

theorem twistedExteriorDerivative_congr (n : ℕ) (A : E →L[ℝ] E)
    {a b : E → DifferentialForms.Manifold.Basic.FormValue E n} {x : E} (h : a =ᶠ[𝓝 x] b) :
    CovectorSymbolAction.Constructions.twistedExteriorDerivative n A a x = CovectorSymbolAction.Constructions.twistedExteriorDerivative n A b x := by
  exact congrArg (fun v : DifferentialForms.Manifold.Basic.FormValue E (n + 1) => -v) (directionalExteriorDerivative_congr n A h)

theorem directionalExteriorDerivative_sub (n : ℕ) (A : E →L[ℝ] E)
    (a b : E → DifferentialForms.Manifold.Basic.FormValue E n) {x : E} (ha : DifferentiableAt ℝ a x) (hb : DifferentiableAt ℝ b x) :
    directionalExteriorDerivative n A (fun y => a y - b y) x =
      directionalExteriorDerivative n A a x - directionalExteriorDerivative n A b x := by
  rw [directionalExteriorDerivative, fderiv_fun_sub ha hb]
  exact (alternationWithDirection n A).map_sub (fderiv ℝ a x) (fderiv ℝ b x)

theorem twistedExteriorDerivative_sub (n : ℕ) (A : E →L[ℝ] E)
    (a b : E → DifferentialForms.Manifold.Basic.FormValue E n) {x : E} (ha : DifferentiableAt ℝ a x) (hb : DifferentiableAt ℝ b x) :
    CovectorSymbolAction.Constructions.twistedExteriorDerivative n A (fun y => a y - b y) x =
      CovectorSymbolAction.Constructions.twistedExteriorDerivative n A a x - CovectorSymbolAction.Constructions.twistedExteriorDerivative n A b x := by
  simp only [directionalExteriorDerivative_twisted]
  rw [directionalExteriorDerivative_sub n A a b ha hb]
  abel

end

section

/-! A degree-minus-two family has an anticommuting derived bracket with
the square-zero twisted differential. The proof includes the boundary degree. -/

open scoped ContDiff

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

def lefschetzTwistedBracketZero (A : E →L[ℝ] E)
    (K : E → DifferentialForms.Manifold.Basic.FormValue E 2 →L[ℝ] DifferentialForms.Manifold.Basic.FormValue E 0) (a : E → DifferentialForms.Manifold.Basic.FormValue E 1) (x : E) : DifferentialForms.Manifold.Basic.FormValue E 0 :=
  K x (CovectorSymbolAction.Constructions.twistedExteriorDerivative 1 A a x)

def lefschetzTwistedBracket (n : ℕ) (A : E →L[ℝ] E)
    (Knext : E → DifferentialForms.Manifold.Basic.FormValue E (n + 1 + 1 + 1) →L[ℝ] DifferentialForms.Manifold.Basic.FormValue E (n + 1))
    (Kprev : E → DifferentialForms.Manifold.Basic.FormValue E (n + 1 + 1) →L[ℝ] DifferentialForms.Manifold.Basic.FormValue E n)
    (a : E → DifferentialForms.Manifold.Basic.FormValue E (n + 1 + 1)) (x : E) : DifferentialForms.Manifold.Basic.FormValue E (n + 1) :=
  Knext x (CovectorSymbolAction.Constructions.twistedExteriorDerivative (n + 1 + 1) A a x) -
    CovectorSymbolAction.Constructions.twistedExteriorDerivative n A (fun y => Kprev y (a y)) x

theorem lefschetzTwistedBracket_anticommute_zero (A : E →L[ℝ] E)
    (K0 : E → DifferentialForms.Manifold.Basic.FormValue E 2 →L[ℝ] DifferentialForms.Manifold.Basic.FormValue E 0)
    (K1 : E → DifferentialForms.Manifold.Basic.FormValue E 3 →L[ℝ] DifferentialForms.Manifold.Basic.FormValue E 1)
    (a : E → DifferentialForms.Manifold.Basic.FormValue E 1) {x : E} (ha : ContDiffAt ℝ ∞ a x) :
    CovectorSymbolAction.Constructions.twistedExteriorDerivative 0 A (lefschetzTwistedBracketZero A K0 a) x +
      lefschetzTwistedBracket 0 A K1 K0 (CovectorSymbolAction.Constructions.twistedExteriorDerivative 1 A a) x = 0 := by
  change CovectorSymbolAction.Constructions.twistedExteriorDerivative 0 A (fun y => K0 y (CovectorSymbolAction.Constructions.twistedExteriorDerivative 1 A a y)) x +
    (K1 x (CovectorSymbolAction.Constructions.twistedExteriorDerivative 2 A (CovectorSymbolAction.Constructions.twistedExteriorDerivative 1 A a) x) -
      CovectorSymbolAction.Constructions.twistedExteriorDerivative 0 A (fun y => K0 y (CovectorSymbolAction.Constructions.twistedExteriorDerivative 1 A a y)) x) = 0
  rw [twistedExteriorDerivative_squared 1 A a ha, map_zero]
  abel

theorem lefschetzTwistedBracket_anticommute (n : ℕ) (A : E →L[ℝ] E)
    (K0 : E → DifferentialForms.Manifold.Basic.FormValue E (n + 1 + 1) →L[ℝ] DifferentialForms.Manifold.Basic.FormValue E n)
    (K1 : E → DifferentialForms.Manifold.Basic.FormValue E (n + 1 + 1 + 1) →L[ℝ] DifferentialForms.Manifold.Basic.FormValue E (n + 1))
    (K2 : E → DifferentialForms.Manifold.Basic.FormValue E (n + 1 + 1 + 1 + 1) →L[ℝ] DifferentialForms.Manifold.Basic.FormValue E (n + 1 + 1))
    (a : E → DifferentialForms.Manifold.Basic.FormValue E (n + 1 + 1)) {U : Set E} (hU : IsOpen U)
    {x : E} (hx : x ∈ U) (ha : ContDiffAt ℝ ∞ a x)
    (hKa : ContDiffOn ℝ ∞ (fun y => K0 y (a y)) U)
    (hKDa : ContDiffOn ℝ ∞ (fun y => K1 y (CovectorSymbolAction.Constructions.twistedExteriorDerivative (n + 1 + 1) A a y)) U) :
    CovectorSymbolAction.Constructions.twistedExteriorDerivative (n + 1) A (lefschetzTwistedBracket n A K1 K0 a) x +
      lefschetzTwistedBracket (n + 1) A K2 K1 (CovectorSymbolAction.Constructions.twistedExteriorDerivative (n + 1 + 1) A a) x = 0 := by
  have hfirst := (hKDa.contDiffAt (hU.mem_nhds hx)).differentiableAt (by simp)
  have hsecond := ((twistedExteriorDerivative_smoothOn n A _ hU hKa).contDiffAt
    (hU.mem_nhds hx)).differentiableAt (by simp)
  change CovectorSymbolAction.Constructions.twistedExteriorDerivative (n + 1) A
    (fun y => K1 y (CovectorSymbolAction.Constructions.twistedExteriorDerivative (n + 1 + 1) A a y) -
      CovectorSymbolAction.Constructions.twistedExteriorDerivative n A (fun z => K0 z (a z)) y) x +
    (K2 x (CovectorSymbolAction.Constructions.twistedExteriorDerivative (n + 1 + 1 + 1) A (CovectorSymbolAction.Constructions.twistedExteriorDerivative (n + 1 + 1) A a) x) -
      CovectorSymbolAction.Constructions.twistedExteriorDerivative (n + 1) A (fun y => K1 y (CovectorSymbolAction.Constructions.twistedExteriorDerivative (n + 1 + 1) A a y)) x) = 0
  rw [twistedExteriorDerivative_sub (n + 1) A _ _ hfirst hsecond,
    twistedExteriorDerivative_squared (n + 1 + 1) A a ha,
    twistedExteriorDerivative_squared n A _ (hKa.contDiffAt (hU.mem_nhds hx)), map_zero]
  abel

end

section

/-! Locality, linearity, and smoothness of the explicit Kähler bracket. -/

open scoped ContDiff _root_.Topology

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem lefschetzTwistedBracket_congr (n : ℕ) (A : E →L[ℝ] E)
    (K1 : E → DifferentialForms.Manifold.Basic.FormValue E (n + 1 + 1 + 1) →L[ℝ] DifferentialForms.Manifold.Basic.FormValue E (n + 1))
    (K0 : E → DifferentialForms.Manifold.Basic.FormValue E (n + 1 + 1) →L[ℝ] DifferentialForms.Manifold.Basic.FormValue E n)
    {a b : E → DifferentialForms.Manifold.Basic.FormValue E (n + 1 + 1)} {x : E} (h : a =ᶠ[𝓝 x] b) :
    lefschetzTwistedBracket n A K1 K0 a x = lefschetzTwistedBracket n A K1 K0 b x := by
  have hK : (fun y => K0 y (a y)) =ᶠ[𝓝 x] (fun y => K0 y (b y)) := h.mono fun y hy => congrArg (K0 y) hy
  rw [lefschetzTwistedBracket, lefschetzTwistedBracket,
    twistedExteriorDerivative_congr (n + 1 + 1) A h, twistedExteriorDerivative_congr n A hK]

theorem lefschetzTwistedBracket_neg (n : ℕ) (A : E →L[ℝ] E)
    (K1 : E → DifferentialForms.Manifold.Basic.FormValue E (n + 1 + 1 + 1) →L[ℝ] DifferentialForms.Manifold.Basic.FormValue E (n + 1))
    (K0 : E → DifferentialForms.Manifold.Basic.FormValue E (n + 1 + 1) →L[ℝ] DifferentialForms.Manifold.Basic.FormValue E n)
    (a : E → DifferentialForms.Manifold.Basic.FormValue E (n + 1 + 1)) (x : E) :
    lefschetzTwistedBracket n A K1 K0 (fun y => -a y) x = -lefschetzTwistedBracket n A K1 K0 a x := by
  simp only [lefschetzTwistedBracket, map_neg, directionalExteriorDerivative_twisted,
    directionalExteriorDerivative_neg]
  abel

theorem lefschetzTwistedBracket_sub (n : ℕ) (A : E →L[ℝ] E)
    (K1 : E → DifferentialForms.Manifold.Basic.FormValue E (n + 1 + 1 + 1) →L[ℝ] DifferentialForms.Manifold.Basic.FormValue E (n + 1))
    (K0 : E → DifferentialForms.Manifold.Basic.FormValue E (n + 1 + 1) →L[ℝ] DifferentialForms.Manifold.Basic.FormValue E n)
    (a b : E → DifferentialForms.Manifold.Basic.FormValue E (n + 1 + 1)) {x : E}
    (ha : DifferentiableAt ℝ a x) (hb : DifferentiableAt ℝ b x)
    (hKa : DifferentiableAt ℝ (fun y => K0 y (a y)) x)
    (hKb : DifferentiableAt ℝ (fun y => K0 y (b y)) x) :
    lefschetzTwistedBracket n A K1 K0 (fun y => a y - b y) x =
      lefschetzTwistedBracket n A K1 K0 a x - lefschetzTwistedBracket n A K1 K0 b x := by
  simp only [lefschetzTwistedBracket, map_sub]
  rw [twistedExteriorDerivative_sub (n + 1 + 1) A a b ha hb, map_sub,
    twistedExteriorDerivative_sub n A _ _ hKa hKb]
  abel

theorem lefschetzTwistedBracket_smoothOn (n : ℕ) (A : E →L[ℝ] E)
    (K1 : E → DifferentialForms.Manifold.Basic.FormValue E (n + 1 + 1 + 1) →L[ℝ] DifferentialForms.Manifold.Basic.FormValue E (n + 1))
    (K0 : E → DifferentialForms.Manifold.Basic.FormValue E (n + 1 + 1) →L[ℝ] DifferentialForms.Manifold.Basic.FormValue E n)
    (a : E → DifferentialForms.Manifold.Basic.FormValue E (n + 1 + 1)) {U : Set E} (hU : IsOpen U)
    (hKa : ContDiffOn ℝ ∞ (fun y => K0 y (a y)) U)
    (hKDa : ContDiffOn ℝ ∞ (fun y => K1 y (CovectorSymbolAction.Constructions.twistedExteriorDerivative (n + 1 + 1) A a y)) U) :
    ContDiffOn ℝ ∞ (lefschetzTwistedBracket n A K1 K0 a) U :=
  hKDa.sub (twistedExteriorDerivative_smoothOn n A _ hU hKa)

end

/-! The bracket for the negative ordinary exterior derivative also
anticommutes with the ordinary exterior derivative itself. -/

open scoped ContDiff

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem lefschetzBracket_ordinary_anticommute (n : ℕ)
    (K0 : E → DifferentialForms.Manifold.Basic.FormValue E (n + 1 + 1) →L[ℝ] DifferentialForms.Manifold.Basic.FormValue E n)
    (K1 : E → DifferentialForms.Manifold.Basic.FormValue E (n + 1 + 1 + 1) →L[ℝ] DifferentialForms.Manifold.Basic.FormValue E (n + 1))
    (K2 : E → DifferentialForms.Manifold.Basic.FormValue E (n + 1 + 1 + 1 + 1) →L[ℝ] DifferentialForms.Manifold.Basic.FormValue E (n + 1 + 1))
    (a : E → DifferentialForms.Manifold.Basic.FormValue E (n + 1 + 1)) {U : Set E} (hU : IsOpen U)
    {x : E} (hx : x ∈ U) (ha : ContDiffAt ℝ ∞ a x)
    (hKa : ContDiffOn ℝ ∞ (fun y => K0 y (a y)) U)
    (hKDa : ContDiffOn ℝ ∞ (fun y => K1 y (CovectorSymbolAction.Constructions.twistedExteriorDerivative (n + 1 + 1) (ContinuousLinearMap.id ℝ E) a y)) U) :
    extDeriv (lefschetzTwistedBracket n (ContinuousLinearMap.id ℝ E) K1 K0 a) x +
      lefschetzTwistedBracket (n + 1) (ContinuousLinearMap.id ℝ E) K2 K1 (extDeriv a) x = 0 := by
  have h := lefschetzTwistedBracket_anticommute n (ContinuousLinearMap.id ℝ E) K0 K1 K2 a hU hx ha hKa hKDa
  simp only [directionalExteriorDerivative_twisted, directionalExteriorDerivative_id,
    lefschetzTwistedBracket_neg] at h
  exact neg_eq_zero.mp ((neg_add _ _).trans h)

theorem smoothField_differentiableAt {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {f : E → F} {U : Set E} (hU : IsOpen U) (hf : ContDiffOn ℝ ∞ f U) {x : E} (hx : x ∈ U) :
    DifferentiableAt ℝ f x := (hf.contDiffAt (hU.mem_nhds hx)).differentiableAt (by simp)

end

end OAI.Analysis.HodgeTheory.Decomposition.ExteriorConstantBracket.Constructions
