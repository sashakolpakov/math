import OAI.AlgebraicGeometry.FormalGeometry.Completion.Finite.CoefficientTopology

/-! # Coefficient Limit -/

namespace OAI.AlgebraicGeometry.FormalGeometry.Completion.CoefficientLimit.Construction

noncomputable section

/-!
# Completion: integral coefficients as the inverse limit of finite coefficients

The inverse-limit description includes the topology. Compatible continuous
finite-coefficient functions therefore reconstruct a unique continuous
integral coefficient function.
-/

variable (ℓ : ℕ) [Fact ℓ.Prime]

/-- Compatible residues in all finite coefficient rings. -/
def coherentFiniteCoefficients : Subring (∀ n : ℕ, ZMod (ℓ ^ n)) where
  carrier := {a | ∀ m n (h : m ≤ n), ZMod.castHom (pow_dvd_pow ℓ h) (ZMod (ℓ ^ m)) (a n) = a m}
  zero_mem' := fun m n h => (ZMod.castHom (pow_dvd_pow ℓ h) (ZMod (ℓ ^ m))).map_zero
  one_mem' := fun m n h => (ZMod.castHom (pow_dvd_pow ℓ h) (ZMod (ℓ ^ m))).map_one
  add_mem' := by
    intro a b ha hb m n h
    exact (map_add _ _ _).trans (congrArg₂ (· + ·) (ha m n h) (hb m n h))
  mul_mem' := by
    intro a b ha hb m n h
    exact (map_mul _ _ _).trans (congrArg₂ (· * ·) (ha m n h) (hb m n h))
  neg_mem' := by
    intro a ha m n h
    exact (map_neg _ _).trans (congrArg Neg.neg (ha m n h))

/-- Projection to one finite coefficient ring. -/
def coherentFiniteProjection (n : ℕ) : coherentFiniteCoefficients ℓ →+* ZMod (ℓ ^ n) where
  toFun a := a.val n
  map_zero' := rfl
  map_one' := rfl
  map_add' _ _ := rfl
  map_mul' _ _ := rfl

omit [Fact ℓ.Prime] in
theorem coherentFiniteProjection_compatible (m n : ℕ) (h : m ≤ n) :
    (ZMod.castHom (pow_dvd_pow ℓ h) (ZMod (ℓ ^ m))).comp
      (coherentFiniteProjection ℓ n) = coherentFiniteProjection ℓ m := by
  ext a
  exact a.property m n h

/-- The integral coefficient determined by a compatible residue tower. -/
def coherentFiniteLift : coherentFiniteCoefficients ℓ →+* ℤ_[ℓ] :=
  PadicInt.lift (coherentFiniteProjection_compatible ℓ)

theorem coherentFiniteLift_spec (a : coherentFiniteCoefficients ℓ) (n : ℕ) :
    PadicInt.toZModPow n (coherentFiniteLift ℓ a) = a.val n :=
  congrArg (fun f => f a) (PadicInt.lift_spec (coherentFiniteProjection_compatible ℓ) n)

/-- All residues of an integral coefficient, as a compatible tower. -/
def padicIntToCoherentFinite : ℤ_[ℓ] →+* coherentFiniteCoefficients ℓ where
  toFun a := ⟨fun n => PadicInt.toZModPow n a, fun m n h =>
    congrArg (fun f => f a) (PadicInt.zmod_cast_comp_toZModPow m n h)⟩
  map_zero' := by ext n; exact map_zero _
  map_one' := by ext n; exact map_one _
  map_add' a b := by ext n; exact map_add _ _ _
  map_mul' a b := by ext n; exact map_mul _ _ _

/-- Integral coefficients and coherent finite coefficients are isomorphic as rings. -/
def padicIntCoherentFiniteEquiv : ℤ_[ℓ] ≃+* coherentFiniteCoefficients ℓ where
  __ := padicIntToCoherentFinite ℓ
  invFun := coherentFiniteLift ℓ
  left_inv a := PadicInt.ext_of_toZModPow.mp fun n => coherentFiniteLift_spec ℓ _ n
  right_inv a := by
    apply Subtype.ext
    funext n
    exact coherentFiniteLift_spec ℓ a n

theorem continuous_padicIntToCoherentFinite : Continuous (padicIntToCoherentFinite ℓ) :=
  (continuous_pi (fun n => Finite.CoefficientTopology.Construction.continuous_padicInt_toZModPow ℓ n)).subtype_mk _

/-- The inverse-limit ring isomorphism respects the actual ℓ-adic topology. -/
def padicIntCoherentFiniteHomeomorph : ℤ_[ℓ] ≃ₜ coherentFiniteCoefficients ℓ :=
  (padicIntCoherentFiniteEquiv ℓ).toEquiv.toHomeomorphOfContinuousClosed
    (continuous_padicIntToCoherentFinite ℓ) (continuous_padicIntToCoherentFinite ℓ).isClosedMap

/-- Compatible continuous finite-coefficient functions reconstruct uniquely. -/
theorem continuousMap_existsUnique_of_coherentFinite {T : Type*} [TopologicalSpace T]
    (f : ∀ n : ℕ, C(T, ZMod (ℓ ^ n)))
    (hf : ∀ m n (h : m ≤ n) t,
      ZMod.castHom (pow_dvd_pow ℓ h) (ZMod (ℓ ^ m)) (f n t) = f m t) :
    ∃! g : C(T, ℤ_[ℓ]), ∀ n t, PadicInt.toZModPow n (g t) = f n t := by
  let a : C(T, coherentFiniteCoefficients ℓ) :=
    ⟨fun t => ⟨fun n => f n t, fun m n h => hf m n h t⟩,
      (continuous_pi (fun n => (f n).continuous)).subtype_mk _⟩
  let g : C(T, ℤ_[ℓ]) := ⟨fun t => coherentFiniteLift ℓ (a t),
    (padicIntCoherentFiniteHomeomorph ℓ).symm.continuous.comp a.continuous⟩
  refine ⟨g, fun n t => coherentFiniteLift_spec ℓ (a t) n, ?_⟩
  intro g' hg'
  apply ContinuousMap.ext
  intro t
  apply PadicInt.ext_of_toZModPow.mp
  intro n
  exact (hg' n t).trans (coherentFiniteLift_spec ℓ (a t) n).symm

end

end OAI.AlgebraicGeometry.FormalGeometry.Completion.CoefficientLimit.Construction
