import Mathlib

/-! # Generic Character Correction -/

namespace OAI.RepresentationTheory.Weil.UnitarySplitting.GenericCharacterCorrection.Construction

noncomputable section

section

/-! Extending a multiplicative formula from a subset meeting every finite
family of right translates. This isolates the passage from generic unitary
matrices to all matrices without assuming a splitting homomorphism. -/

section Algebra

variable {G M : Type} [Group G] [Group M]
variable (D : Set G) (f : G → M)
variable (hD : ∀ s : Finset G, ∃ t : G, ∀ g ∈ s, g * t ∈ D)
variable (hm : ∀ a ∈ D, ∀ b ∈ D, a * b ∈ D → f (a * b) = f a * f b)

include hD in
theorem generic_denominator (g : G) : ∃ t, t ∈ D ∧ g * t ∈ D := by
  classical
  obtain ⟨t, ht⟩ := hD {1, g}
  exact ⟨t, by simpa using ht 1 (by simp), ht g (by simp)⟩

include hm in
theorem generic_fraction_change (g t u : G)
    (ht : t ∈ D) (hgt : g * t ∈ D) (hu : u ∈ D) (hgu : g * u ∈ D)
    (htu : t⁻¹ * u ∈ D) : f (g * t) * (f t)⁻¹ = f (g * u) * (f u)⁻¹ := by
  have h1 : f (g * u) = f (g * t) * f (t⁻¹ * u) := by
    simpa only [mul_assoc, mul_inv_cancel_left] using
      hm (g * t) hgt (t⁻¹ * u) htu (by simpa only [mul_assoc, mul_inv_cancel_left] using hgu)
  have h2 : f u = f t * f (t⁻¹ * u) := by
    simpa only [mul_inv_cancel_left] using
      hm t ht (t⁻¹ * u) htu (by simpa only [mul_inv_cancel_left] using hu)
  rw [h1, h2]
  group

include hD hm in
theorem generic_fraction_independent (g t u : G)
    (ht : t ∈ D) (hgt : g * t ∈ D) (hu : u ∈ D) (hgu : g * u ∈ D) :
    f (g * t) * (f t)⁻¹ = f (g * u) * (f u)⁻¹ := by
  classical
  obtain ⟨v, hv⟩ := hD {1, g, t⁻¹, u⁻¹}
  have hvD : v ∈ D := by simpa using hv 1 (by simp)
  have hgv : g * v ∈ D := hv g (by simp)
  exact (generic_fraction_change D f hm g t v ht hgt hvD hgv (hv t⁻¹ (by simp))).trans
    (generic_fraction_change D f hm g u v hu hgu hvD hgv (hv u⁻¹ (by simp))).symm

def genericExtension (g : G) : M :=
  let t := (generic_denominator D hD g).choose
  f (g * t) * (f t)⁻¹

include hm in
theorem genericExtension_apply (g t : G) (ht : t ∈ D) (hgt : g * t ∈ D) :
    genericExtension D f hD g = f (g * t) * (f t)⁻¹ := by
  exact generic_fraction_independent D f hD hm g _ t
    (generic_denominator D hD g).choose_spec.1
    (generic_denominator D hD g).choose_spec.2 ht hgt

include hm in
theorem genericExtension_eq (g : G) (hg : g ∈ D) : genericExtension D f hD g = f g := by
  obtain ⟨t, ht, hgt⟩ := generic_denominator D hD g
  rw [genericExtension_apply D f hD hm g t ht hgt, hm g hg t ht hgt, mul_inv_cancel_right]

def genericExtensionHom : G →* M where
  toFun := genericExtension D f hD
  map_one' := by
    obtain ⟨t, ht, h1t⟩ := generic_denominator D hD 1
    rw [genericExtension_apply D f hD hm 1 t ht h1t, one_mul, mul_inv_cancel]
  map_mul' g h := by
    classical
    obtain ⟨t, ht⟩ := hD {1, h, g * h}
    have htD : t ∈ D := by simpa using ht 1 (by simp)
    have hht : h * t ∈ D := ht h (by simp)
    have hght : (g * h) * t ∈ D := ht (g * h) (by simp)
    rw [genericExtension_apply D f hD hm (g * h) t htD hght,
      genericExtension_apply D f hD hm h t htD hht,
      genericExtension_apply D f hD hm g (h * t) hht (by rwa [← mul_assoc])]
    group

theorem genericExtensionHom_projection {N : Type} [Group N]
    (p : M →* N) (a : G →* N) (hp : ∀ g ∈ D, p (f g) = a g) (g : G) :
    p (genericExtensionHom D f hD hm g) = a g := by
  obtain ⟨t, ht, hgt⟩ := generic_denominator D hD g
  change p (genericExtension D f hD g) = a g
  rw [genericExtension_apply D f hD hm g t ht hgt,
    map_mul, map_inv, hp (g * t) hgt, hp t ht, map_mul, mul_inv_cancel_right]

end Algebra

variable {G M : Type} [Group G] [Group M] [TopologicalSpace G] [TopologicalSpace M]
variable [IsTopologicalGroup G] [IsTopologicalGroup M]

theorem genericExtension_continuous
    (D : Set G) (f : G → M)
    (hD : ∀ s : Finset G, ∃ t : G, ∀ g ∈ s, g * t ∈ D)
    (hm : ∀ a ∈ D, ∀ b ∈ D, a * b ∈ D → f (a * b) = f a * f b)
    (hopen : IsOpen D) (hc : ContinuousOn f D) : Continuous (genericExtension D f hD) := by
  rw [continuous_iff_continuousAt]
  intro g
  obtain ⟨t, ht, hgt⟩ := generic_denominator D hD g
  have hmul : ContinuousAt (fun x : G => x * t) g := continuousAt_id.mul continuousAt_const
  have hfun : ContinuousAt (fun x : G => f (x * t) * (f t)⁻¹) g :=
    ((hc.continuousAt (hopen.mem_nhds hgt)).comp (f := fun x : G => x * t) hmul).mul continuousAt_const
  apply hfun.congr_of_eventuallyEq
  filter_upwards [hmul.preimage_mem_nhds (hopen.mem_nhds hgt)] with x hx
  exact genericExtension_apply D f hD hm x t ht hx

def genericExtensionContinuousHom
    (D : Set G) (f : G → M)
    (hD : ∀ s : Finset G, ∃ t : G, ∀ g ∈ s, g * t ∈ D)
    (hm : ∀ a ∈ D, ∀ b ∈ D, a * b ∈ D → f (a * b) = f a * f b)
    (hopen : IsOpen D) (hc : ContinuousOn f D) : G →ₜ* M :=
  ⟨genericExtensionHom D f hD hm, genericExtension_continuous D f hD hm hopen hc⟩

end

/-! A determinant-character coboundary removes the Gaussian phase from
the multiplication law on a generic domain. -/

variable {G Z A : Type} [Group G] [CommGroup Z] [Group A]

def characterCorrectedLift (ι : Z →* A) (ℓ : Z) (κ : G → Z) (a : G → A) (g : G) : A :=
  ι ((ℓ * κ g)⁻¹) * a g

theorem characterCorrectedLift_mul
    (ι : Z →* A) (hcentral : ∀ z : Z, ∀ x : A, Commute (ι z) x)
    (ℓ : Z) (κ : G → Z) (a : G → A) (g h : G)
    (hmul : a g * a h = ι (ℓ * κ g * κ h * (κ (g * h))⁻¹) * a (g * h)) :
    characterCorrectedLift ι ℓ κ a g * characterCorrectedLift ι ℓ κ a h =
      characterCorrectedLift ι ℓ κ a (g * h) := by
  unfold characterCorrectedLift
  calc
    _ = (ι ((ℓ * κ g)⁻¹) * ι ((ℓ * κ h)⁻¹)) * (a g * a h) := by
      exact (hcentral ((ℓ * κ h)⁻¹) (a g)).symm.mul_mul_mul_comm _ _
    _ = ι (((ℓ * κ g)⁻¹ * (ℓ * κ h)⁻¹) *
        (ℓ * κ g * κ h * (κ (g * h))⁻¹)) * a (g * h) := by
      rw [hmul, ← map_mul, ← mul_assoc, ← map_mul]
    _ = _ := by
      congr 2
      calc
        _ = (ℓ⁻¹ * ℓ) * ((κ g)⁻¹ * κ g) * ((κ h)⁻¹ * κ h) *
            ((κ (g * h))⁻¹ * ℓ⁻¹) := by simp only [mul_inv_rev]; ac_rfl
        _ = _ := by simp only [inv_mul_cancel, one_mul, mul_inv_rev]

omit [Group G] in
theorem characterCorrectedLift_projects
    {P : Type} [Group P] (ι : Z →* A) (π : A →* P) (hscalar : ∀ z, π (ι z) = 1)
    (ℓ : Z) (κ : G → Z) (a : G → A) (p : G → P) (ha : ∀ g, π (a g) = p g) (g : G) :
    π (characterCorrectedLift ι ℓ κ a g) = p g := by
  rw [characterCorrectedLift, map_mul, hscalar, one_mul, ha]

omit [Group G] in
theorem characterCorrectedLift_continuousOn
    [TopologicalSpace G] [TopologicalSpace Z] [IsTopologicalGroup Z]
    [TopologicalSpace A] [ContinuousMul A]
    (ι : Z →* A) (hι : Continuous ι) (ℓ : Z) (κ : G → Z) (a : G → A)
    (D : Set G) (hκ : ContinuousOn κ D) (ha : ContinuousOn a D) :
    ContinuousOn (characterCorrectedLift ι ℓ κ a) D :=
  (hι.comp_continuousOn (continuousOn_const.mul hκ).inv).mul ha

end

end OAI.RepresentationTheory.Weil.UnitarySplitting.GenericCharacterCorrection.Construction
