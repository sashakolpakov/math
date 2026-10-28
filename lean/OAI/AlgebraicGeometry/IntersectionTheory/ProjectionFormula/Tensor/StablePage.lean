import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.BrutalFiltration
import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Tensor.SpectralIsomorphisms
import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.BrutalTensorSpectralSequence

/-! # Stable Page -/

namespace OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Tensor.StablePage

noncomputable section

/-! For a bounded tail filtration, sufficiently late native spectral
pages identify with the graded pieces defined by its fixed endpoints. -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.CategoryTheory.ComposableArrows

abbrev arrow {a b : ℤ} (h : a ≤ b) : (a : EInt) ⟶ (b : EInt) :=
  homOfLE (WithBotTop.coe_le_coe.mpr h)

variable (R : Type) [CommRing R] (A K : CochainComplex (ModuleCat.{0} R) ℤ)

def term (d : ℕ) (q n : ℤ) (hqa : -1 ≤ q) (hqb : q + 1 ≤ (d : ℤ)) : ModuleCat.{0} R :=
  (Tensor.SpectralObject.abelian R K (BrutalFiltration.filtration R A)).E
    (arrow hqa) (arrow (show q ≤ q + 1 by omega)) (arrow hqb) (n - 1) n (n + 1)

def iso (d : ℕ) (hl : ∀ i, i < -(d : ℤ) → IsZero (A.X i))
    (hu : ∀ i, 0 < i → IsZero (A.X i)) (r : ℤ) (hr : (d : ℤ) + 3 ≤ r)
    (p q : ℤ) (hqa : -1 ≤ q) (hqb : q + 1 ≤ (d : ℤ)) :
    ((BrutalTensorSpectralSequence.spectralSequence R A K).page r (by omega)).X (p, q) ≅
      term R A K d q (p + q) hqa hqb := by
  let D := BrutalFiltration.filtration R A
  let X := Tensor.SpectralObject.abelian R K D
  let f₁ : ((q - r + 2 : ℤ) : EInt) ⟶ (q : EInt) := arrow (by omega)
  let f₂ : (q : EInt) ⟶ ((q + 1 : ℤ) : EInt) := arrow (by omega)
  let f₃ : ((q + 1 : ℤ) : EInt) ⟶ ((q + r - 1 : ℤ) : EInt) := arrow (by omega)
  let g₁ : ((-1 : ℤ) : EInt) ⟶ (q : EInt) := arrow hqa
  let g₃ : ((q + 1 : ℤ) : EInt) ⟶ ((d : ℤ) : EInt) := arrow hqb
  let α : mk₃ f₁ f₂ f₃ ⟶ mk₃ g₁ f₂ f₃ :=
    homMk₃ (arrow (show q - r + 2 ≤ -1 by omega)) (𝟙 _) (𝟙 _) (𝟙 _)
  let β : mk₃ g₁ f₂ g₃ ⟶ mk₃ g₁ f₂ f₃ :=
    homMk₃ (𝟙 _) (𝟙 _) (𝟙 _) (arrow (show (d : ℤ) ≤ q + r - 1 by omega))
  have hα : ∀ t, IsIso (D.map (α.app t)) := by
    intro t
    fin_cases t
    · exact BrutalFiltration.Bounds.inclusion_isIso_below R A 0 (q - r + 2) (-1)
        (by omega) hu (by omega)
    · change IsIso (D.map (𝟙 _)); infer_instance
    · change IsIso (D.map (𝟙 _)); infer_instance
    · change IsIso (D.map (𝟙 _)); infer_instance
  have hβ : ∀ t, IsIso (D.map (β.app t)) := by
    intro t
    fin_cases t
    · change IsIso (D.map (𝟙 _)); infer_instance
    · change IsIso (D.map (𝟙 _)); infer_instance
    · change IsIso (D.map (𝟙 _)); infer_instance
    · exact BrutalFiltration.Bounds.inclusion_isIso_above R A (-(d : ℤ)) (d : ℤ) (q + r - 1)
        (by omega) hl (by omega)
  let : IsIso (X.map f₁ f₂ f₃ g₁ f₂ f₃ α ((p + q) - 1) (p + q) ((p + q) + 1)) :=
    SpectralIsomorphisms.E_map_isIso R K D _ _ _ _ _ _ α hα (p + q)
  let : IsIso (X.map g₁ f₂ g₃ g₁ f₂ f₃ β ((p + q) - 1) (p + q) ((p + q) + 1)) :=
    SpectralIsomorphisms.E_map_isIso R K D _ _ _ _ _ _ β hβ (p + q)
  exact X.spectralSequencePageXIso Abelian.SpectralObject.coreE₂Cohomological r (by omega) (p, q)
      (((q - r + 2 : ℤ) : EInt)) (q : EInt) ((q + 1 : ℤ) : EInt) ((q + r - 1 : ℤ) : EInt)
      rfl rfl rfl rfl ((p + q) - 1) (p + q) ((p + q) + 1) rfl ≪≫
    asIso (X.map f₁ f₂ f₃ g₁ f₂ f₃ α ((p + q) - 1) (p + q) ((p + q) + 1) (sub_add_cancel _ _) rfl) ≪≫
    (asIso (X.map g₁ f₂ g₃ g₁ f₂ f₃ β ((p + q) - 1) (p + q) ((p + q) + 1) (sub_add_cancel _ _) rfl)).symm

end

end OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Tensor.StablePage
