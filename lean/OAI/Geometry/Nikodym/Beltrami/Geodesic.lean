import OAI.Geometry.Nikodym.Beltrami.Connection

noncomputable section
namespace OAI.Geometry.Nikodym

open Set
open scoped RealInnerProductSpace

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- An affinely parametrized geodesic for the verified Beltrami connection.
The velocity is recorded explicitly to avoid any regularity conventions for
the total derivative outside the parameter interval. -/
structure IsBeltramiGeodesic (κ : ℝ) (γ v : ℝ → E) (I : Set ℝ) : Prop where
  position_derivative : ∀ t ∈ I, HasDerivAt γ (v t) t
  velocity_derivative : ∀ t ∈ I,
    HasDerivAt v (-beltramiChristoffel κ (γ t) (v t) (v t)) t
  regular : ∀ t ∈ I, 0 < beltramiDenominator κ (γ t)

theorem IsBeltramiGeodesic.velocity_eq
    {κ : ℝ} {γ v : ℝ → E} {I : Set ℝ}
    (h : IsBeltramiGeodesic κ γ v I) (hI : IsOpen I) (hconn : IsPreconnected I)
    {t₀ t : ℝ} (h₀ : t₀ ∈ I) (ht : t ∈ I) :
    v t = beltramiDenominator κ (γ t) •
      ((beltramiDenominator κ (γ t₀))⁻¹ • v t₀) := by
  let F : ℝ → E := fun s => (beltramiDenominator κ (γ s))⁻¹ • v s
  have hF : ∀ s ∈ I, HasDerivAt F 0 s := fun s hs =>
    hasDerivAt_rescaled_geodesic_velocity (h.position_derivative s hs)
      (h.velocity_derivative s hs) (h.regular s hs).ne'
  have heq : F t = F t₀ := hI.is_const_of_deriv_eq_zero hconn
    (fun s hs => (hF s hs).differentiableAt.differentiableWithinAt)
    (fun s hs => (hF s hs).deriv) ht h₀
  calc
    v t = beltramiDenominator κ (γ t) • F t := by
      simp [F,smul_smul,(h.regular t ht).ne']
    _ = _ := congrArg (fun w => beltramiDenominator κ (γ t) • w) heq

/-- Every genuine model geodesic is contained in one Euclidean affine line.
No hypothesis about the geodesic's image being a line is supplied. -/
theorem IsBeltramiGeodesic.image_in_line
    {κ : ℝ} {γ v : ℝ → E} {I : Set ℝ}
    (h : IsBeltramiGeodesic κ γ v I) (hI : IsOpen I) (hconn : IsPreconnected I)
    {t₀ : ℝ} (h₀ : t₀ ∈ I) :
    ∃ c : E, ∀ t ∈ I, ∃ s : ℝ, γ t = γ t₀ + s • c := by
  let c : E := (beltramiDenominator κ (γ t₀))⁻¹ • v t₀
  have hv : ∀ t ∈ I, v t = beltramiDenominator κ (γ t) • c :=
    fun t ht => h.velocity_eq hI hconn h₀ ht
  refine ⟨c,?_⟩
  by_cases hc : c = 0
  · have hd : ∀ t ∈ I, HasDerivAt γ 0 t := by
      intro t ht
      simpa [hv t ht,hc] using h.position_derivative t ht
    intro t ht
    refine ⟨0,?_⟩
    simpa using hI.is_const_of_deriv_eq_zero hconn
      (fun s hs => (hd s hs).differentiableAt.differentiableWithinAt)
      (fun s hs => (hd s hs).deriv) ht h₀
  · have hn : ‖c‖ ^ 2 ≠ 0 := pow_ne_zero 2 (norm_ne_zero_iff.mpr hc)
    let F : ℝ → E := fun t => γ t - (⟪c,γ t⟫ / ‖c‖^2) • c
    have hd : ∀ t ∈ I, HasDerivAt F 0 t := by
      intro t ht
      have hi : HasDerivAt (fun s => ⟪c,γ s⟫) ⟪c,v t⟫ t := by
        simpa using (hasDerivAt_const t c).inner ℝ (h.position_derivative t ht)
      have hh := (h.position_derivative t ht).sub ((hi.div_const (‖c‖^2)).smul_const c)
      convert hh using 1
      rw [hv t ht,inner_smul_right,real_inner_self_eq_norm_sq]
      simp [hn]
    intro t ht
    have heq := hI.is_const_of_deriv_eq_zero hconn
      (fun s hs => (hd s hs).differentiableAt.differentiableWithinAt)
      (fun s hs => (hd s hs).deriv) ht h₀
    refine ⟨⟪c,γ t⟫ / ‖c‖^2 - ⟪c,γ t₀⟫ / ‖c‖^2,?_⟩
    dsimp [F] at heq
    rw [sub_smul]
    calc
      γ t = (γ t - (⟪c,γ t⟫ / ‖c‖^2) • c) + (⟪c,γ t⟫ / ‖c‖^2) • c := by abel
      _ = (γ t₀ - (⟪c,γ t₀⟫ / ‖c‖^2) • c) + (⟪c,γ t⟫ / ‖c‖^2) • c := by rw [heq]
      _ = _ := by abel

end OAI.Geometry.Nikodym
