import OAI.RepresentationTheory.Weil.Local.OscillatoryTailTools

/-! # Planar Radial Compact -/

namespace OAI.RepresentationTheory.Weil.Local.PlanarRadialCompact.Construction

noncomputable section

section

/-! Explicit first and second derivatives of radial amplitudes on the plane. -/

def planarRadiusSquared (z : ℝ × ℝ) : ℝ := z.1 ^ 2 + z.2 ^ 2

def planarRadial (F : ℝ → ℂ) (z : ℝ × ℝ) : ℂ := F (planarRadiusSquared z)

def planarRadialX (F' : ℝ → ℂ) (z : ℝ × ℝ) : ℂ :=
  (2 * z.1 : ℝ) * F' (planarRadiusSquared z)

def planarRadialY (F' : ℝ → ℂ) (z : ℝ × ℝ) : ℂ :=
  (2 * z.2 : ℝ) * F' (planarRadiusSquared z)

def planarRadialXX (F' F'' : ℝ → ℂ) (z : ℝ × ℝ) : ℂ :=
  2 * F' (planarRadiusSquared z) + (4 * z.1 ^ 2 : ℝ) * F'' (planarRadiusSquared z)

def planarRadialYY (F' F'' : ℝ → ℂ) (z : ℝ × ℝ) : ℂ :=
  2 * F' (planarRadiusSquared z) + (4 * z.2 ^ 2 : ℝ) * F'' (planarRadiusSquared z)

theorem planarRadiusSquared_nonneg (z : ℝ × ℝ) : 0 ≤ planarRadiusSquared z :=
  add_nonneg (sq_nonneg _) (sq_nonneg _)

theorem planarRadial_hasDerivAt_x (F F' : ℝ → ℂ)
    (hF : ∀ t, 0 ≤ t → HasDerivAt F (F' t) t) (x y : ℝ) :
    HasDerivAt (fun t => planarRadial F (t, y)) (planarRadialX F' (x, y)) x := by
  have hd := (hF (x ^ 2 + y ^ 2) (add_nonneg (sq_nonneg x) (sq_nonneg y))).scomp x
    (((hasDerivAt_id x).pow 2).add_const (y ^ 2))
  dsimp only [id_eq, Pi.pow_apply] at hd
  convert! hd using 1
  unfold planarRadialX planarRadiusSquared
  norm_num [Complex.real_smul]

theorem planarRadial_hasDerivAt_y (F F' : ℝ → ℂ)
    (hF : ∀ t, 0 ≤ t → HasDerivAt F (F' t) t) (x y : ℝ) :
    HasDerivAt (fun t => planarRadial F (x, t)) (planarRadialY F' (x, y)) y := by
  have hd := (hF (x ^ 2 + y ^ 2) (add_nonneg (sq_nonneg x) (sq_nonneg y))).scomp y
    (((hasDerivAt_id y).pow 2).const_add (x ^ 2))
  dsimp only [id_eq, Pi.pow_apply] at hd
  convert! hd using 1
  unfold planarRadialY planarRadiusSquared
  norm_num [Complex.real_smul]

theorem planarRadialX_hasDerivAt_x (F' F'' : ℝ → ℂ)
    (hF' : ∀ t, 0 ≤ t → HasDerivAt F' (F'' t) t) (x y : ℝ) :
    HasDerivAt (fun t => planarRadialX F' (t, y)) (planarRadialXX F' F'' (x, y)) x := by
  have hd := (((hasDerivAt_id x).const_mul 2).ofReal_comp).mul
    (planarRadial_hasDerivAt_x F' F'' hF' x y)
  dsimp only [id_eq] at hd
  convert! hd using 1
  unfold planarRadialXX planarRadialX planarRadial
  push_cast
  ring

theorem planarRadialY_hasDerivAt_y (F' F'' : ℝ → ℂ)
    (hF' : ∀ t, 0 ≤ t → HasDerivAt F' (F'' t) t) (x y : ℝ) :
    HasDerivAt (fun t => planarRadialY F' (x, t)) (planarRadialYY F' F'' (x, y)) y := by
  have hd := (((hasDerivAt_id y).const_mul 2).ofReal_comp).mul
    (planarRadial_hasDerivAt_y F' F'' hF' x y)
  dsimp only [id_eq] at hd
  convert! hd using 1
  unfold planarRadialYY planarRadialY planarRadial
  push_cast
  ring

theorem planarRadial_laplacian (F' F'' : ℝ → ℂ) (z : ℝ × ℝ) :
    planarRadialXX F' F'' z + planarRadialYY F' F'' z =
      4 * ((planarRadiusSquared z : ℂ) * F'' (planarRadiusSquared z) + F' (planarRadiusSquared z)) := by
  unfold planarRadialXX planarRadialYY planarRadiusSquared
  push_cast
  ring

end

/-! Compact support of radial amplitudes with an upper squared-radius cutoff. -/

open Set

theorem planarRadiusSquared_continuous : Continuous planarRadiusSquared := by
  unfold planarRadiusSquared
  fun_prop

theorem planarRadiusSquared_sublevel_compact (U : ℝ) :
    IsCompact {z : ℝ × ℝ | planarRadiusSquared z ≤ U} := by
  let b := |U| + 1
  have hb : 0 ≤ b := by dsimp [b]; positivity
  have hUb : U ≤ b ^ 2 := by dsimp [b]; nlinarith [le_abs_self U, abs_nonneg U]
  have hs : {z : ℝ × ℝ | planarRadiusSquared z ≤ U} ⊆ Icc (-b, -b) (b, b) := by
    intro z hz
    have hx : z.1 ^ 2 ≤ b ^ 2 := by
      change z.1 ^ 2 + z.2 ^ 2 ≤ U at hz
      nlinarith [sq_nonneg z.2]
    have hy : z.2 ^ 2 ≤ b ^ 2 := by
      change z.1 ^ 2 + z.2 ^ 2 ≤ U at hz
      nlinarith [sq_nonneg z.1]
    obtain ⟨hx1, hx2⟩ := abs_le_of_sq_le_sq' hx hb
    obtain ⟨hy1, hy2⟩ := abs_le_of_sq_le_sq' hy hb
    exact ⟨⟨hx1, hy1⟩, ⟨hx2, hy2⟩⟩
  exact isCompact_Icc.of_isClosed_subset
    (isClosed_le planarRadiusSquared_continuous continuous_const) hs

theorem planarRadial_compactSupport (F : ℝ → ℂ) (U : ℝ) (hF : ∀ t, U ≤ t → F t = 0) :
    HasCompactSupport (planarRadial F) := by
  apply (planarRadiusSquared_sublevel_compact U).of_isClosed_subset (isClosed_tsupport _)
  apply closure_minimal _ (isClosed_le planarRadiusSquared_continuous continuous_const)
  intro z hz
  change F (planarRadiusSquared z) ≠ 0 at hz
  exact (lt_of_not_ge (fun h => hz (hF _ h))).le

theorem planarRadial_continuous (F : ℝ → ℂ) (hF : Continuous F) : Continuous (planarRadial F) :=
  hF.comp planarRadiusSquared_continuous

theorem planarRadial_compactSupport_deriv (F : ℝ → ℂ) (U : ℝ)
    (hF : Function.support F ⊆ Iic U) : HasCompactSupport (planarRadial (deriv F)) := by
  have hs : tsupport F ⊆ Iic U := closure_minimal hF isClosed_Iic
  apply (planarRadiusSquared_sublevel_compact U).of_isClosed_subset (isClosed_tsupport _)
  apply closure_minimal _ (isClosed_le planarRadiusSquared_continuous continuous_const)
  intro z hz
  exact hs (support_deriv_subset hz)

end

end OAI.RepresentationTheory.Weil.Local.PlanarRadialCompact.Construction
