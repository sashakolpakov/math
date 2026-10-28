import OAI.NumberTheory.PadicHodge.IntegralComparison.PrincipalSource.SupportConditions
import OAI.NumberTheory.PadicHodge.IntegralComparison.PrincipalSource.Intrinsic

/-! # Intrinsic Support -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.PrincipalSource.IntrinsicSupport.Intrinsic

noncomputable section

/-! The transported native principal diagram has the same punctured
cover and support complement as the geometric source diagram. -/
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry _root_.TopologicalSpace
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open OAI.NumberTheory.PadicHodge.IntegralComparison.PrincipalSource.OpenReindex

variable {Y Z : Scheme.{0}} (π : Y ⟶ Z) (U : Z.Opens) (hU : IsAffineOpen U)
  (V : Y.Opens) (hV : IsAffineOpen V) (hVU : V ≤ π ⁻¹ᵁ U)
  {m : ℕ} (t : Fin m → Γ(Z,U))

abbrev native := Principal.AdditiveSections.opens V hV
abbrev geometric := OpenReindex.geometricOpens π U hU V
abbrev family := (OpenReindex.reindex π U V hVU).obj ∘ PrincipalPoint.Fraction.family U t

theorem object (j : ULift (Fin m)) :
    (native V hV).obj (family π U V hVU t j) =
      (geometric π U hU V).obj (PrincipalPoint.Fraction.family U t j) := by
  exact congrArg (fun F => F.obj (PrincipalPoint.Fraction.family U t j))
    (OpenReindex.opens_eq π U hU V hV hVU)

include hVU in
theorem terminal :
    (native V hV).obj (⊤_ (Principal.SectionPresheaf.Index V)) =
      (geometric π U hU V).obj (⊤_ (Principal.SectionPresheaf.Index U)) := by
  exact (AugmentedCech.AmbientReindex.terminal_eq
    (OpenReindex.reindex π U V hVU) (native V hV)).symm.trans
      (congrArg (fun F => F.obj (⊤_ (Principal.SectionPresheaf.Index U)))
        (OpenReindex.opens_eq π U hU V hV hVU))

variable (O : Y.Opens)
  (hpunct : ∀ j, (geometric π U hU V).obj (PrincipalPoint.Fraction.family U t j) ≤ O)
  (hcover : (geometric π U hU V).obj (⊤_ (Principal.SectionPresheaf.Index U)) ⊓ O ≤
    ⨆ j, (geometric π U hU V).obj (PrincipalPoint.Fraction.family U t j))
  (hglobal : (geometric π U hU V).obj (⊤_ (Principal.SectionPresheaf.Index U)) ⊔ O = ⊤)

include hpunct in
theorem punctured (j : ULift (Fin m)) : (native V hV).obj (family π U V hVU t j) ≤ O := by
  rw [object π U hU V hV hVU t]
  exact hpunct j

include hcover in
theorem cover : (native V hV).obj (⊤_ (Principal.SectionPresheaf.Index V)) ⊓ O ≤
    ⨆ j, (native V hV).obj (family π U V hVU t j) := by
  simpa only [terminal π U hU V hV hVU, object π U hU V hV hVU t] using hcover

include hglobal hVU in
theorem global : (native V hV).obj (⊤_ (Principal.SectionPresheaf.Index V)) ⊔ O = ⊤ := by
  rw [terminal π U hU V hV hVU]
  exact hglobal

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.PrincipalSource.IntrinsicSupport.Intrinsic
