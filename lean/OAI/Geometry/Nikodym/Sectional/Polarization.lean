import Mathlib

noncomputable section
namespace OAI.Geometry.Nikodym

/-- The scalar sectional quadratic forms determine an algebraic curvature
tensor. Only additivity, the curvature skew symmetries and Bianchi are used. -/
theorem curvature_tensor_zero_of_sectional_zero
    {E : Type*} [AddCommGroup E] (T : E → E → E → E → ℝ)
    (ha : ∀ a b c d e, T (a+b) c d e = T a c d e + T b c d e)
    (hb : ∀ a b c d e, T a (b+c) d e = T a b d e + T a c d e)
    (hc : ∀ a b c d e, T a b (c+d) e = T a b c e + T a b d e)
    (hd : ∀ a b c d e, T a b c (d+e) = T a b c d + T a b c e)
    (hfirst : ∀ a b c d, T a b c d = -T b a c d)
    (hlast : ∀ a b c d, T a b c d = -T a b d c)
    (hbianchi : ∀ a b c d, T a b c d + T b c a d + T c a b d = 0)
    (hsection : ∀ a b, T a b b a = 0) : ∀ a b c d, T a b c d = 0 := by
  have hz (a b c : E) : T a b c c = 0 := by
    have hh := hlast a b c c
    linarith
  have hsym (a b c : E) : T a b b c = T c b b a := by
    have h := hbianchi a b c b
    have h1 := hlast a b c b
    have h2 := hfirst b c a b
    have h3 := hlast c b a b
    rw [hz c a b] at h
    linarith
  have hj (a b c : E) : T a b b c = 0 := by
    have h := hsection (a+c) b
    rw [ha,hd,hd,hsection a b,hsection c b] at h
    have hs := hsym a b c
    linarith
  have hmiddle (a b c d : E) : T a b c d = -T a c b d := by
    have h := hj a (b+c) d
    rw [hb,hc,hc,hj a b d,hj a c d] at h
    linarith
  intro a b c d
  have h := hbianchi a b c d
  have h1 := hmiddle b c a d
  have h2 := hfirst b a c d
  have h3 := hfirst c a b d
  have h4 := hmiddle a c b d
  linarith

end OAI.Geometry.Nikodym
