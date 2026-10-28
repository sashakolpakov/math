import OAI.NumberTheory.ArithmeticGroups.Data

/-! # Period -/

namespace OAI.NumberTheory.ArithmeticGroups.Period.CongruenceLevel

noncomputable section

open scoped Classical

variable {Y : Type*} [AddCommGroup Y] [Module ℂ Y]
  (κ : Y ≃ₗ⋆[ℂ] Y) (hκ : Function.Involutive κ)
  (Ψ : LinearMap.BilinForm ℂ Y) (P : Submodule ℂ Y)

include hκ

def conjugateSubspace : Submodule ℂ Y := P.comap κ.toLinearMap

omit hκ in
lemma mem_conjugateSubspace (x : Y) :
    x ∈ conjugateSubspace κ P ↔ κ x ∈ P := Iff.rfl

lemma conjugate_mem (x : Y) (hx : x ∈ P) :
    κ x ∈ conjugateSubspace κ P := by
  change κ (κ x) ∈ P
  rwa [hκ]

theorem positivePeriod_isCompl (r : ℕ)
    (hP : Geometry.ComplexBall.PrescribedSignsB.PositivePeriod r (fun x y => Ψ x y) κ P) : IsCompl P (conjugateSubspace κ P) := by
  constructor
  · apply Submodule.disjoint_def.mpr
    intro x hx hcx
    by_contra hn
    have hpos := (hP.2.2.2.1 x hx hn).2
    have hiso := hP.2.2.1 x hx (κ x) hcx
    rw [hiso] at hpos
    simp at hpos
  · apply codisjoint_iff_le_sup.mpr
    intro x _
    obtain ⟨uv, huv, _⟩ := hP.2.2.2.2 x
    exact Submodule.mem_sup.mpr
      ⟨uv.1, huv.1, κ uv.2, conjugate_mem κ hκ P uv.2 huv.2.1, huv.2.2.symm⟩

def conjugateHermitian :
    conjugateSubspace κ P →ₗ⋆[ℂ]
      conjugateSubspace κ P →ₗ[ℂ] ℂ where
  toFun u := (-2 * Complex.I) • ((Ψ (κ (u : Y))).comp (conjugateSubspace κ P).subtype)
  map_add' u v := by
    ext w
    simp only [Submodule.coe_add, map_add, LinearMap.add_apply, LinearMap.smul_apply,
      LinearMap.comp_apply, smul_eq_mul, mul_add]
  map_smul' a u := by
    ext v
    simp only [Submodule.coe_smul, map_smulₛₗ,
      LinearMap.smul_apply, LinearMap.comp_apply, smul_eq_mul, RingHom.id_apply]
    ring

omit hκ in
lemma conjugateHermitian_apply (u v : conjugateSubspace κ P) :
    conjugateHermitian κ Ψ P u v =
      (-2 * Complex.I) * Ψ (κ (u : Y)) (v : Y) := rfl

theorem conjugateHermitian_symm
    (hreal : ∀ x y, star (Ψ x y) = Ψ (κ x) (κ y))
    (hskew : ∀ x y, Ψ x y = -Ψ y x)
    (u v : conjugateSubspace κ P) :
    conjugateHermitian κ Ψ P v u = star (conjugateHermitian κ Ψ P u v) := by
  simp only [conjugateHermitian_apply, star_mul, hreal]
  rw [hκ (u : Y)]
  rw [hskew (u : Y) (κ (v : Y))]
  simp only [star_neg, star_ofNat, Complex.star_def, Complex.conj_I]
  ring

theorem conjugateHermitian_positive (r : ℕ)
    (hP : Geometry.ComplexBall.PrescribedSignsB.PositivePeriod r (fun x y => Ψ x y) κ P)
    (u : conjugateSubspace κ P) (hu : u ≠ 0) :
    0 < (conjugateHermitian κ Ψ P u u).re := by
  have hne : κ (u : Y) ≠ 0 := by
    intro hz
    apply hu
    apply Subtype.ext
    exact κ.injective (hz.trans κ.map_zero.symm)
  have hp := (hP.2.2.2.1 (κ (u : Y)) u.property hne).2
  rw [hκ] at hp
  have he : (-2 * Complex.I) * Ψ (κ (u : Y)) (u : Y) =
      2 * (Ψ (κ (u : Y)) (u : Y) / Complex.I) := by
    rw [div_eq_mul_inv, Complex.inv_I]
    ring
  rw [conjugateHermitian_apply, he]
  simpa using mul_pos (show (0 : ℝ) < 2 by norm_num) hp

lemma real_decomposition (hc : IsCompl P (conjugateSubspace κ P))
    (x : Y) (hx : κ x = x) :
    let q := (conjugateSubspace κ P).projectionOnto P hc.symm x
    x = κ (q : Y) + (q : Y) := by
  let p := P.projectionOnto (conjugateSubspace κ P) hc x
  let q := (conjugateSubspace κ P).projectionOnto P hc.symm x
  have hsum : (p : Y) + q = x := Submodule.projection_add_projection_eq_self hc x
  have hsumc : κ (q : Y) + κ (p : Y) = x := by
    have h := congrArg κ hsum
    rw [map_add, hx] at h
    simpa only [add_comm] using h
  have hp : (p : Y) = κ (q : Y) := by
    have hd : (p : Y) - κ (q : Y) ∈ P := P.sub_mem p.property q.property
    have hd' : (p : Y) - κ (q : Y) ∈ conjugateSubspace κ P := by
      have he : (p : Y) - κ (q : Y) = κ (p : Y) - q := by
        apply sub_eq_sub_iff_add_eq_add.mpr
        simpa only [add_comm] using hsum.trans hsumc.symm
      rw [he]
      exact (conjugateSubspace κ P).sub_mem
        (conjugate_mem κ hκ P p p.property) q.property
    exact sub_eq_zero.mp (Submodule.disjoint_def.mp hc.disjoint _ hd hd')
  dsimp only
  rw [← hp]
  exact hsum.symm

theorem conjugateHermitian_riemann
    (hc : IsCompl P (conjugateSubspace κ P))
    (hreal : ∀ x y, star (Ψ x y) = Ψ (κ x) (κ y))
    (hiso : ∀ x ∈ P, ∀ y ∈ P, Ψ x y = 0)
    (x y : Y) (hx : κ x = x) (hy : κ y = y) :
    let π := (conjugateSubspace κ P).projectionOnto P hc.symm
    (conjugateHermitian κ Ψ P (π x) (π y)).im = -(Ψ x y).re := by
  let π := (conjugateSubspace κ P).projectionOnto P hc.symm
  let u := π x
  let v := π y
  have he : Ψ x y = Ψ (κ (u : Y)) (v : Y) + star (Ψ (κ (u : Y)) (v : Y)) := by
    have hx' : x = κ (u : Y) + (u : Y) := real_decomposition κ hκ P hc x hx
    have hy' : y = κ (v : Y) + (v : Y) := real_decomposition κ hκ P hc y hy
    have hisouv : Ψ (κ (u : Y)) (κ (v : Y)) = 0 :=
      hiso _ u.property _ v.property
    have huv : Ψ (u : Y) (v : Y) = 0 := by
      have h := hreal (κ (u : Y)) (κ (v : Y))
      rw [hκ (u : Y), hκ (v : Y), hisouv, star_zero] at h
      exact h.symm
    have hc : star (Ψ (κ (u : Y)) (v : Y)) = Ψ (u : Y) (κ (v : Y)) := by
      rw [hreal, hκ (u : Y)]
    rw [hx', hy']
    simp only [map_add, LinearMap.add_apply]
    rw [hisouv, huv, hc]
    ring
  change (conjugateHermitian κ Ψ P u v).im = _
  rw [he, conjugateHermitian_apply]
  simp [Complex.add_re, Complex.mul_im, Complex.mul_re]
  ring

/-- A positive period supplies a quotient of the prescribed dimension and
an actual positive Hermitian form on its tangent space. -/
theorem exists_positive_quotient [FiniteDimensional ℂ Y]
    (r : ℕ) (hP : Geometry.ComplexBall.PrescribedSignsB.PositivePeriod r (fun x y => Ψ x y) κ P)
    (hreal : ∀ x y, star (Ψ x y) = Ψ (κ x) (κ y))
    (hskew : ∀ x y, Ψ x y = -Ψ y x) :
    let T := Fin r → ℂ
    ∃ (π : Y →ₗ[ℂ] T) (H : T →ₗ⋆[ℂ] T →ₗ[ℂ] ℂ),
      π.ker = P ∧ Function.Surjective π ∧
      (∀ u v, H v u = star (H u v)) ∧
      (∀ u, u ≠ 0 → 0 < (H u u).re) ∧
      (∀ x y, κ x = x → κ y = y → (H (π x) (π y)).im = -(Ψ x y).re) := by
  let Q := conjugateSubspace κ P
  have hc : IsCompl P Q := positivePeriod_isCompl κ hκ Ψ P r hP
  have hd : Module.finrank ℂ Q = r :=
    (P.quotientEquivOfIsCompl Q hc).finrank_eq.symm.trans hP.2.1
  let e : Q ≃ₗ[ℂ] (Fin r → ℂ) := (Module.finBasisOfFinrankEq ℂ Q hd).equivFun
  let π := e.toLinearMap.comp (Q.projectionOnto P hc.symm)
  let H : (Fin r → ℂ) →ₗ⋆[ℂ] (Fin r → ℂ) →ₗ[ℂ] ℂ :=
    { toFun := fun u => (conjugateHermitian κ Ψ P (e.symm u)).comp e.symm.toLinearMap
      map_add' := fun u v => by ext w; simp
      map_smul' := fun a u => by ext v; simp }
  have he (x : Y) : e.symm (π x) = Q.projectionOnto P hc.symm x := e.symm_apply_apply _
  refine ⟨π, H, ?_, ?_, ?_, ?_, ?_⟩
  · simp only [π, LinearMap.ker_comp, LinearEquiv.ker, Submodule.comap_bot,
      Submodule.ker_projectionOnto]
  · exact e.surjective.comp (Submodule.projectionOnto_surjective hc.symm)
  · intro u v
    exact conjugateHermitian_symm κ hκ Ψ P hreal hskew (e.symm u) (e.symm v)
  · intro u hu
    apply conjugateHermitian_positive κ hκ Ψ P r hP (e.symm u)
    intro hz
    exact hu (e.symm.injective (hz.trans e.symm.map_zero.symm))
  · intro x y hx hy
    change (conjugateHermitian κ Ψ P (e.symm (π x)) (e.symm (π y))).im = _
    rw [he, he]
    exact conjugateHermitian_riemann κ hκ Ψ P hc hreal hP.2.2.1 x y hx hy

end

end OAI.NumberTheory.ArithmeticGroups.Period.CongruenceLevel
