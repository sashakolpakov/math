import OAI.AlgebraicGeometry.HilbertScheme.Presentations.Module.Fractions

/-! # Degree Pieces -/

namespace OAI.AlgebraicGeometry.HilbertScheme.Presentations.Localized.DegreePieces.GradedModules

noncomputable section

/-!
Homogeneous degree pieces in the localization at a homogeneous element.
Membership is represented by an actual homogeneous numerator and a power
of the chosen denominator.
-/

universe u v w

variable {R : Type u} [CommRing R] {A : Type v} [CommRing A] [Algebra R A]
variable {M : Type w} [AddCommGroup M] [Module R M] [Module A M] [IsScalarTower R A M]
variable (𝒜 : ℤ → Submodule R A) [GradedAlgebra 𝒜]
variable (ℳ : ℤ → Submodule R M) [SetLike.GradedSMul 𝒜 ℳ]

def localizedDegreeStage (a : A) (e d : ℤ) (k : ℕ) : Submodule R (Presentations.Module.Fractions.GradedModules.AwayModule a M) :=
  (ℳ (d + (k : ℤ) * e)).map (Presentations.Module.Fractions.GradedModules.moduleFractionMap (R := R) a k)

def localizedDegreePiece (a : A) (e d : ℤ) : Submodule R (Presentations.Module.Fractions.GradedModules.AwayModule a M) :=
  ⨆ k : ℕ, localizedDegreeStage ℳ a e d k

theorem localizedDegreeStage_le_add (a : A) (e : ℤ) (ha : a ∈ 𝒜 e) (d : ℤ) (k l : ℕ) :
    localizedDegreeStage ℳ a e d k ≤ localizedDegreeStage ℳ a e d (k + l) := by
  rintro x ⟨m, hm, rfl⟩
  refine ⟨a ^ l • m, ?_, Presentations.Module.Fractions.GradedModules.moduleFractionMap_raise (R := R) a k l m⟩
  have hp : a ^ l ∈ 𝒜 ((l : ℤ) * e) := by simpa only [nsmul_eq_mul] using SetLike.pow_mem_graded l ha
  have h := SetLike.GradedSMul.smul_mem hp hm
  have he : (l : ℤ) * e + (d + (k : ℤ) * e) = d + ((k + l : ℕ) : ℤ) * e := by
    push_cast
    ring
  exact he ▸ h

theorem localizedDegreeStage_directed (a : A) (e : ℤ) (ha : a ∈ 𝒜 e) (d : ℤ) :
    Directed (· ≤ ·) (localizedDegreeStage ℳ a e d) := by
  intro k l
  refine ⟨k + l, localizedDegreeStage_le_add 𝒜 ℳ a e ha d k l, ?_⟩
  simpa only [Nat.add_comm l k] using localizedDegreeStage_le_add 𝒜 ℳ a e ha d l k

theorem mem_localizedDegreePiece_iff (a : A) (e : ℤ) (ha : a ∈ 𝒜 e) (d : ℤ)
    (x : Presentations.Module.Fractions.GradedModules.AwayModule a M) :
    x ∈ localizedDegreePiece ℳ a e d ↔
      ∃ (k : ℕ) (m : M), m ∈ ℳ (d + (k : ℤ) * e) ∧ Presentations.Module.Fractions.GradedModules.moduleFractionMap (R := R) a k m = x := by
  rw [localizedDegreePiece, Submodule.mem_iSup_of_directed _
    (localizedDegreeStage_directed 𝒜 ℳ a e ha d)]
  rfl

theorem moduleFractionMap_mem_degree (a : A) (e d : ℤ) (k : ℕ) (m : M)
    (hm : m ∈ ℳ (d + (k : ℤ) * e)) :
    Presentations.Module.Fractions.GradedModules.moduleFractionMap (R := R) a k m ∈ localizedDegreePiece ℳ a e d :=
  (le_iSup (localizedDegreeStage ℳ a e d) k) ⟨m, hm, rfl⟩

theorem localizedDegreePiece_zero_numerator (a : A) (e : ℤ) (ha : a ∈ 𝒜 e) (d : ℤ)
    (x : Presentations.Module.Fractions.GradedModules.AwayModule a M) (hx : x ∈ localizedDegreePiece ℳ a e d) :
    ∃ (k : ℕ) (m : M), m ∈ ℳ (d + (k : ℤ) * e) ∧
      Presentations.Module.Fractions.GradedModules.moduleFractionMap (R := R) a k m = x ∧ (x = 0 ↔ ∃ l : ℕ, a ^ l • m = 0) := by
  obtain ⟨k, m, hm, hmx⟩ := (mem_localizedDegreePiece_iff 𝒜 ℳ a e ha d x).mp hx
  exact ⟨k, m, hm, hmx, hmx ▸ Presentations.Module.Fractions.GradedModules.moduleFractionMap_eq_zero (R := R) a k m⟩

end

end OAI.AlgebraicGeometry.HilbertScheme.Presentations.Localized.DegreePieces.GradedModules
