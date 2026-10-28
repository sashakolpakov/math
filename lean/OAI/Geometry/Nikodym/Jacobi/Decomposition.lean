import OAI.Geometry.Nikodym.Jacobi.ODE

noncomputable section
namespace OAI.Geometry.Nikodym

open Set
open scoped RealInnerProductSpace

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- Full radial/transverse Jacobi formula in a parallel orthonormal frame.
Unlike the perpendicular formula, no orthogonality of the initial variation
is assumed. The input is the actual constant-curvature Jacobi ODE. -/
theorem constant_curvature_jacobi_decomposition
    {S : Set ℝ} (hS : Convex ℝ S) (h0 : 0 ∈ S)
    (κ : ℝ) {e w : E} (he : ‖e‖ = 1) {J V : ℝ → E}
    (hJ : ∀ t ∈ S, HasDerivAt J (V t) t)
    (hV : ∀ t ∈ S, HasDerivAt V ((-κ) • (J t - ⟪e,J t⟫ • e)) t)
    (hJ0 : J 0 = 0) (hV0 : V 0 = w) {t : ℝ} (ht : t ∈ S) :
    J t = (t * ⟪e,w⟫) • e + curvatureSin κ t • (w - ⟪e,w⟫ • e) ∧
    V t = ⟪e,w⟫ • e + curvatureCos κ t • (w - ⟪e,w⟫ • e) := by
  have hee : ⟪e,e⟫ = (1:ℝ) := by simp [he]
  let a : ℝ → ℝ := fun s => ⟪e,J s⟫
  let b : ℝ → ℝ := fun s => ⟪e,V s⟫
  have ha (s : ℝ) (hs : s ∈ S) : HasDerivAt a (b s) s := by
    simpa only [a,b,inner_zero_left,zero_add,add_zero] using! (hasDerivAt_const s e).inner ℝ (hJ s hs)
  have hb (s : ℝ) (hs : s ∈ S) : HasDerivAt b 0 s := by
    simpa only [b,inner_zero_left,zero_add,inner_smul_right,inner_sub_right,hee,
      mul_one,sub_self,mul_zero] using (hasDerivAt_const s e).inner ℝ (hV s hs)
  have hab := constant_curvature_jacobi_solution hS h0 (0:ℝ) ha
    (fun s hs => by simpa using hb s hs)
    (show a 0 = 0 by simp [a,hJ0]) (show b 0 = ⟪e,w⟫ by simp [b,hV0]) ht
  have hat : a t = t * ⟪e,w⟫ := by simpa only [curvatureSin_flat,smul_eq_mul] using hab.1
  have hbt : b t = ⟪e,w⟫ := by simpa only [curvatureCos_flat,one_smul] using hab.2
  let Q : ℝ → E := fun s => J s - a s • e
  let W : ℝ → E := fun s => V s - b s • e
  have hQ (s : ℝ) (hs : s ∈ S) : HasDerivAt Q (W s) s :=
    (hJ s hs).sub ((ha s hs).smul_const e)
  have hW (s : ℝ) (hs : s ∈ S) : HasDerivAt W ((-κ) • Q s) s := by
    simpa only [W,Q,a,zero_smul,sub_zero] using! (hV s hs).sub ((hb s hs).smul_const e)
  have hQ0 : Q 0 = 0 := by simp [Q,a,hJ0]
  have hW0 : W 0 = w - ⟪e,w⟫ • e := by simp [W,b,hV0]
  have hQW := constant_curvature_jacobi_solution hS h0 κ hQ hW hQ0 hW0 ht
  constructor
  · calc
      J t = a t • e + Q t := by dsimp [Q]; module
      _ = _ := by rw [hat,hQW.1]
  · calc
      V t = b t • e + W t := by dsimp [W]; module
      _ = _ := by rw [hbt,hQW.2]

end OAI.Geometry.Nikodym
