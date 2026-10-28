import OAI.NumberTheory.PadicHodge.IntegralComparison.Principal.SupportedOpenScalar
import OAI.NumberTheory.PadicHodge.IntegralComparison.PrincipalPoint.Fraction
import OAI.NumberTheory.PadicHodge.IntegralComparison.Principal.AmbientProducts
import OAI.NumberTheory.PadicHodge.IntegralComparison.Principal.TerminalScalars
import OAI.NumberTheory.PadicHodge.IntegralComparison.RelativeCech.RefinementQuasiIso
import OAI.NumberTheory.PadicHodge.IntegralComparison.SectionIdealPuncturedCover
import Mathlib.CategoryTheory.Limits.Preserves.Lattice

/-! # Support Conditions -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.PrincipalSource.SupportConditions

noncomputable section

/-! The actual ambient principal parameters supply the wide and selected
support covers on the source scheme. Every term remains an affine open,
and both diagrams lie inside the original affine source neighborhood. -/
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry _root_.TopologicalSpace Opposite
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open OAI.NumberTheory.PadicHodge.IntegralComparison.Principal.SectionPresheaf OAI.NumberTheory.PadicHodge.IntegralComparison.PrincipalSource.OpenReindex
variable {Y Z : Scheme.{0}} (π : Y ⟶ Z) (U : Z.Opens) (hU : IsAffineOpen U)
  (V : Y.Opens) (hV : V ≤ π ⁻¹ᵁ U)

theorem wide_top : (OpenReindex.wideOpens π U hU).obj (⊤_ (Principal.SectionPresheaf.Index U)) = π ⁻¹ᵁ U := by
  change π ⁻¹ᵁ Principal.SectionPresheaf.openSubset U (⊤_ (Principal.SectionPresheaf.Index U)) = _
  rw [Principal.TerminalScalars.open_eq U hU]

include hV in
theorem local_top : (OpenReindex.geometricOpens π U hU V).obj (⊤_ (Principal.SectionPresheaf.Index U)) = V := by
  change V ⊓ (OpenReindex.wideOpens π U hU).obj (⊤_ (Principal.SectionPresheaf.Index U)) = V
  rw [wide_top, inf_eq_left.mpr hV]

theorem wide_bounded (r : Principal.SectionPresheaf.Index U) : (OpenReindex.wideOpens π U hU).obj r ≤ π ⁻¹ᵁ U :=
  π.preimage_mono (Z.basicOpen_le r.val)

theorem local_bounded (r : Principal.SectionPresheaf.Index U) : (OpenReindex.geometricOpens π U hU V).obj r ≤ π ⁻¹ᵁ U :=
  inf_le_right.trans (wide_bounded π U hU r)

variable {g : ℕ} (t : Fin g → Γ(Z,U))

local instance preimage_preserves : PreservesFiniteLimits (Opens.map π.base) := by
  change PreservesFiniteLimits (OrderHom.ofClass π.base.frameHom).toFunctor
  infer_instance

local instance intersection_preserves_shape (n : ℕ) :
    PreservesLimitsOfShape (Discrete (Fin (n+1))) (RelativeCech.Intersections.intersect V) := by
  let : ∀ a : Fin (n+1) → Y.Opens,
      PreservesLimit (Discrete.functor a) (RelativeCech.Intersections.intersect V) :=
    fun a => RelativeCech.RefinementQuasiIso.intersection_preserves_product V a
  exact preservesLimitsOfShape_of_discrete _

instance wide_preserves : ∀ (n : ℕ) (a : Fin (n+1) → ULift (Fin g)),
    PreservesLimit (Discrete.functor (PrincipalPoint.Fraction.family U t ∘ a)) (OpenReindex.wideOpens π U hU) :=
  fun _ _ => by
    dsimp only [OpenReindex.wideOpens]
    infer_instance

instance local_preserves : ∀ (n : ℕ) (a : Fin (n+1) → ULift (Fin g)),
    PreservesLimit (Discrete.functor (PrincipalPoint.Fraction.family U t ∘ a))
      (OpenReindex.geometricOpens π U hU V) :=
  fun _ _ => by
    dsimp only [OpenReindex.geometricOpens]
    infer_instance

variable [Y.IsSeparated] [IsAffineHom π] (hVa : IsAffineOpen V)
  (O₁ O₂ : Y.Opens) (hout : O₁ ≤ O₂) (hinter : V ⊓ O₁ = V ⊓ O₂)
  (hselected : V ⊔ O₂ = ⊤) (hwide : (π ⁻¹ᵁ U) ⊔ O₁ = ⊤)
  (hcover : (π ⁻¹ᵁ U) ⊓ O₁ = ⨆ j, π ⁻¹ᵁ Z.basicOpen (t j))

include hV hVa hout hinter hselected hwide hcover in
theorem conditions : Principal.InjectiveIntegerRows.SingleSupportedCandidate.Conditions
    (OpenReindex.wideOpens π U hU) (OpenReindex.geometricOpens π U hU V)
    (PrincipalPoint.Fraction.family U t) O₁ O₂ where
  outside_le := hout
  intersection_eq := by rw [local_top π U hU V hV]; exact hinter
  local_global := by rw [local_top π U hU V hV]; exact hselected
  wide_global := by rw [wide_top]; exact hwide
  wide_punctured := fun j =>
    (le_iSup (fun k => π ⁻¹ᵁ Z.basicOpen (t k)) j.down).trans
      (hcover.ge.trans inf_le_right)
  local_punctured := fun j => inf_le_right.trans
    ((le_iSup (fun k => π ⁻¹ᵁ Z.basicOpen (t k)) j.down).trans
      (hcover.ge.trans inf_le_right))
  wide_cover := by
    rw [wide_top]
    intro y hy
    rw [hcover] at hy
    obtain ⟨j, hj⟩ := Opens.mem_iSup.mp hy
    exact Opens.mem_iSup.mpr ⟨ULift.up j, hj⟩
  local_cover := by
    rw [local_top π U hU V hV]
    intro y hy
    have hy' : y ∈ (π ⁻¹ᵁ U) ⊓ O₁ := ⟨hV hy.1, hy.2⟩
    rw [hcover] at hy'
    obtain ⟨j, hj⟩ := Opens.mem_iSup.mp hy'
    exact Opens.mem_iSup.mpr ⟨ULift.up j, hy.1, hj⟩
  wide_affine := fun r => (hU.basicOpen r.val).preimage π
  local_affine := fun r => hVa.inf ((hU.basicOpen r.val).preimage π)

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.PrincipalSource.SupportConditions
