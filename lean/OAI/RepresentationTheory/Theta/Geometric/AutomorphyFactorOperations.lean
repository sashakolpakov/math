import OAI.RepresentationTheory.Theta.Geometric.AutomorphicFamilies

/-! # Automorphy Factor Operations -/

namespace OAI.RepresentationTheory.Theta.Geometric

noncomputable section

/-! Pulling back and multiplying actual automorphy factors and their
theta sections, for the forthcoming cubical product comparison. -/

open scoped ContDiff

section

variable {Φ Ψ : Torus.Data.CM.ProjectivePeriodData}

def Torus.Data.CM.ProjectivePeriodData.latticeMapOfLinear (f : Ψ.space →L[ℂ] Φ.space)
    (hf : ∀ l : Ψ.periodIntegerLattice, f l.val ∈ Φ.periodIntegerLattice) :
    Ψ.periodIntegerLattice →+ Φ.periodIntegerLattice where
  toFun l := ⟨f l.val, hf l⟩
  map_zero' := Subtype.ext f.map_zero
  map_add' l m := Subtype.ext (f.map_add l.val m.val)

def Torus.Data.CM.ProjectivePeriodData.AutomorphyFactor.comap (J : Φ.AutomorphyFactor) (f : Ψ.space →L[ℂ] Φ.space)
    (hf : ∀ l : Ψ.periodIntegerLattice, f l.val ∈ Φ.periodIntegerLattice) : Ψ.AutomorphyFactor where
  value l z := J.value (Torus.Data.CM.ProjectivePeriodData.latticeMapOfLinear f hf l) (f z)
  zero z := by rw [map_zero, J.zero]
  add l m z := by rw [map_add, J.add]; congr 2; exact (f.map_add z m.val).symm
  continuous l := (J.continuous _).comp f.continuous

def Torus.Data.CM.ProjectivePeriodData.AutomorphyFactor.mul (J K : Φ.AutomorphyFactor) : Φ.AutomorphyFactor where
  value l z := J.value l z * K.value l z
  zero z := by rw [J.zero, K.zero, one_mul]
  add l m z := by rw [J.add, K.add]; ring
  continuous l := (J.continuous l).mul (K.continuous l)

end

variable {Φ Ψ : Torus.Data.CM.ProjectivePeriodData} {J K : Φ.AutomorphyFactor} {n : ℕ}

def AutomorphicFamilies.CM.Torus.AutomorphicTheta.Section.castDegree (s : AutomorphicFamilies.CM.Torus.AutomorphicTheta.Section J n) {m : ℕ} (h : n = m) : AutomorphicFamilies.CM.Torus.AutomorphicTheta.Section J m := h ▸ s

@[simp] theorem AutomorphicFamilies.CM.Torus.AutomorphicTheta.Section.castDegree_apply (s : AutomorphicFamilies.CM.Torus.AutomorphicTheta.Section J n) {m : ℕ} (h : n = m) (z : Φ.space) :
    s.castDegree h z = s z := by
  cases h
  rfl

theorem AutomorphicFamilies.CM.Torus.AutomorphicTheta.Section.castDegree_coe (s : AutomorphicFamilies.CM.Torus.AutomorphicTheta.Section J n) {m : ℕ} (h : n = m) :
    (s.castDegree h : Φ.space → ℂ) = s := funext (AutomorphicFamilies.CM.Torus.AutomorphicTheta.Section.castDegree_apply s h)

def AutomorphicFamilies.CM.Torus.AutomorphicTheta.Section.castFactor (s : AutomorphicFamilies.CM.Torus.AutomorphicTheta.Section J n) (h : J = K) : AutomorphicFamilies.CM.Torus.AutomorphicTheta.Section K n := h ▸ s

@[simp] theorem AutomorphicFamilies.CM.Torus.AutomorphicTheta.Section.castFactor_apply (s : AutomorphicFamilies.CM.Torus.AutomorphicTheta.Section J n) (h : J = K) (z : Φ.space) :
    s.castFactor h z = s z := by
  cases h
  rfl

def AutomorphicFamilies.CM.Torus.AutomorphicTheta.Section.comap (s : AutomorphicFamilies.CM.Torus.AutomorphicTheta.Section J n) (f : Ψ.space →L[ℂ] Φ.space)
    (hf : ∀ l : Ψ.periodIntegerLattice, f l.val ∈ Φ.periodIntegerLattice) :
    AutomorphicFamilies.CM.Torus.AutomorphicTheta.Section (J.comap f hf) n where
  toFun z := s (f z)
  regular := s.regular.comp f.contDiff
  translates l z := by rw [map_add]; exact s.translates (Torus.Data.CM.ProjectivePeriodData.latticeMapOfLinear f hf l) (f z)

@[simp] theorem AutomorphicFamilies.CM.Torus.AutomorphicTheta.Section.comap_apply (s : AutomorphicFamilies.CM.Torus.AutomorphicTheta.Section J n) (f : Ψ.space →L[ℂ] Φ.space)
    (hf : ∀ l : Ψ.periodIntegerLattice, f l.val ∈ Φ.periodIntegerLattice) (z : Ψ.space) :
    s.comap f hf z = s (f z) := rfl

def AutomorphicFamilies.CM.Torus.AutomorphicTheta.Section.factorMul (s : AutomorphicFamilies.CM.Torus.AutomorphicTheta.Section J n) (t : AutomorphicFamilies.CM.Torus.AutomorphicTheta.Section K n) : AutomorphicFamilies.CM.Torus.AutomorphicTheta.Section (J.mul K) n where
  toFun z := s z * t z
  regular := s.regular.mul t.regular
  translates l z := by rw [s.translates, t.translates]; change _ = (_ * _) ^ n * _; rw [mul_pow]; ring

@[simp] theorem AutomorphicFamilies.CM.Torus.AutomorphicTheta.Section.factorMul_apply (s : AutomorphicFamilies.CM.Torus.AutomorphicTheta.Section J n) (t : AutomorphicFamilies.CM.Torus.AutomorphicTheta.Section K n) (z : Φ.space) :
    s.factorMul t z = s z * t z := rfl

theorem AutomorphicFamilies.CM.Torus.AutomorphicTheta.Section.factorMul_cast_coe (s : AutomorphicFamilies.CM.Torus.AutomorphicTheta.Section J n) {m : ℕ} (t : AutomorphicFamilies.CM.Torus.AutomorphicTheta.Section K m) (h : m = n) :
    (s.factorMul (t.castDegree h) : Φ.space → ℂ) = (s : Φ.space → ℂ) * t := by
  funext z
  exact congrArg (s z * ·) (AutomorphicFamilies.CM.Torus.AutomorphicTheta.Section.castDegree_apply t h z)

end

end OAI.RepresentationTheory.Theta.Geometric
