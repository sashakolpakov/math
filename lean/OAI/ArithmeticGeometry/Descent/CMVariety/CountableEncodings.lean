import Mathlib.Data.Set.Countable
import Mathlib.Logic.Function.Basic

/-! # Countable Encodings -/

namespace OAI.ArithmeticGeometry.Descent.CMVariety.CountableEncodings.Abelian

/-! A countable code space gives a countable image whenever equal codes
force equal outputs; the source itself may be uncountable. -/

theorem countable_range_of_countable_encoding {I C X : Type*} [Countable C]
    (code : I → C) (f : I → X)
    (h : ∀ i j, code i = code j → f i = f j) : (Set.range f).Countable := by
  classical
  rcases isEmpty_or_nonempty I with hI | hI
  · exact Set.countable_empty.mono (by rintro _ ⟨i, _⟩; exact isEmptyElim i)
  · let i₀ : I := Classical.choice hI
    let out := Function.extend code f (fun _ => f i₀)
    have hf : f.FactorsThrough code := fun {i j} hij => h i j hij
    apply (Set.countable_range out).mono
    rintro _ ⟨i, rfl⟩
    exact ⟨code i, hf.extend_apply (fun _ => f i₀) i⟩

end OAI.ArithmeticGeometry.Descent.CMVariety.CountableEncodings.Abelian
