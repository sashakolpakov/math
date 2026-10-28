import OAI.RepresentationTheory.Weil.UnitarySplitting.UltraMultiplier

/-! # Local Constancy -/

namespace OAI.RepresentationTheory.Theta.Adelic.LocalConstancy

noncomputable section

/-! Compact locally constant functions have uniform stabilizers under
small linear coordinate changes and small quadratic multipliers.
These are properties of the actual LocalWeil functions, with no Weil-action
smoothness assumption. -/

open Filter OAI.RepresentationTheory.Weil.UnitarySplitting.UltraMultiplier.Construction
open scoped _root_.Topology

theorem compact_eventually_eq
    {P X Y : Type*} [TopologicalSpace P] [TopologicalSpace X]
    (p₀ : P) (K : Set X) (hK : IsCompact K)
    (f : X → Y) (hf : IsLocallyConstant f)
    (a : P → X → X) (ha : Continuous (Function.uncurry a))
    (ha₀ : ∀ x, a p₀ x = x) :
    ∀ᶠ p in 𝓝 p₀, ∀ x ∈ K, f (a p x) = f x := by
  apply hK.eventually_forall_of_forall_eventually
  intro x _
  have hleft : ∀ᶠ z : P × X in 𝓝 (p₀, x), f (a z.1 z.2) = f x := by
    have h := (ha.tendsto (p₀, x)).eventually (hf.eventually_eq (a p₀ x))
    change ∀ᶠ z : P × X in 𝓝 (p₀, x), f (a z.1 z.2) = f (a p₀ x) at h
    simpa only [ha₀] using h
  have hright : ∀ᶠ z : P × X in 𝓝 (p₀, x), f z.2 = f x :=
    (continuous_snd.tendsto (p₀, x)).eventually (hf.eventually_eq x)
  filter_upwards [hleft, hright] with z hz hz'
  exact hz.trans hz'.symm

theorem compact_locallyConstant_coordinate_stabilizer
    {P X : Type*} [TopologicalSpace P] [TopologicalSpace X]
    (p₀ : P) (f : X → ℂ) (hf : IsLocallyConstant f)
    (hs : HasCompactSupport f)
    (a b : P → X → X)
    (ha : Continuous (Function.uncurry a))
    (hb : Continuous (Function.uncurry b))
    (ha₀ : ∀ x, a p₀ x = x) (hb₀ : ∀ x, b p₀ x = x)
    (hba : ∀ p x, b p (a p x) = x) :
    ∀ᶠ p in 𝓝 p₀, ∀ x, f (a p x) = f x := by
  have h₁ := compact_eventually_eq p₀ (tsupport f) hs f hf a ha ha₀
  have h₂ := compact_eventually_eq p₀ (tsupport f) hs f hf b hb hb₀
  filter_upwards [h₁, h₂] with p hp hp'
  intro x
  by_cases hx : x ∈ tsupport f
  · exact hp x hx
  · by_cases hax : a p x ∈ tsupport f
    · have h := hp' (a p x) hax
      simpa only [hba] using h.symm
    · rw [image_eq_zero_of_notMem_tsupport hx, image_eq_zero_of_notMem_tsupport hax]

variable {k : Type} [NormedField k] [IsUltrametricDist k] {N : ℕ}

theorem substitution_eventually_fixes (f : Weil.Local.FunctionsMetaplectic.Construction.schwartzBruhat k N) :
    ∀ᶠ A : Weil.Local.FunctionsMetaplectic.Construction.GeneralLinear k N in 𝓝 1, Weil.Local.FunctionsMetaplectic.Construction.substitutionOperator A f.val = f.val := by
  obtain ⟨hf, hs⟩ := Weil.UnitarySplitting.UltraMultiplier.Construction.schwartzBruhat_ultra_iff.mp f.property
  have h := compact_locallyConstant_coordinate_stabilizer
    (1 : Weil.Local.FunctionsMetaplectic.Construction.GeneralLinear k N) f.val hf hs
    (fun A x => (↑(A⁻¹) : Matrix (Fin N) (Fin N) k).mulVec x)
    (fun A x => (↑A : Matrix (Fin N) (Fin N) k).mulVec x)
    (by fun_prop) (by fun_prop)
    (by intro x; simp) (by intro x; simp)
    (by intro A x; simp [Matrix.mulVec_mulVec])
  filter_upwards [h] with A hA
  exact funext hA

theorem quadratic_eventually_fixes
    (ψ : AddChar k ℂ) (hψ : Continuous (fun t : k => ψ t))
    (f : Weil.Local.FunctionsMetaplectic.Construction.schwartzBruhat k N) :
    ∀ᶠ B : Matrix (Fin N) (Fin N) k in 𝓝 0,
      Weil.Local.FunctionsMetaplectic.Construction.quadraticOperator ψ B f.val = f.val := by
  have hlocal := Weil.UnitarySplitting.LocalTest.Construction.additiveCharacter_locallyConstant_ultra ψ hψ
  have hphase : ∀ᶠ B : Matrix (Fin N) (Fin N) k in 𝓝 0,
      ∀ x ∈ tsupport f.val, ψ (Weil.Local.FunctionsMetaplectic.Construction.quadratic B x) = 1 := by
    apply (Weil.UnitarySplitting.UltraMultiplier.Construction.schwartzBruhat_ultra_iff.mp f.property).2.eventually_forall_of_forall_eventually
    intro x _
    have hc : Continuous (fun p : Matrix (Fin N) (Fin N) k × Weil.Local.FunctionsMetaplectic.Construction.Position k N =>
        Weil.Local.FunctionsMetaplectic.Construction.quadratic p.1 p.2) := by unfold Weil.Local.FunctionsMetaplectic.Construction.quadratic; fun_prop
    have h := (hc.tendsto (0, x)).eventually (hlocal.eventually_eq (Weil.Local.FunctionsMetaplectic.Construction.quadratic 0 x))
    simpa [Weil.Local.FunctionsMetaplectic.Construction.quadratic] using h
  filter_upwards [hphase] with B hB
  funext x
  rw [Weil.Local.FunctionsMetaplectic.Construction.quadraticOperator_apply]
  by_cases hx : x ∈ tsupport f.val
  · rw [hB x hx, one_mul]
  · rw [image_eq_zero_of_notMem_tsupport hx, mul_zero]

end

end OAI.RepresentationTheory.Theta.Adelic.LocalConstancy
