import OAI.RepresentationTheory.Weil.Local.PrincipalSquareClasses
import OAI.RepresentationTheory.Weil.Local.QuadraticNormAt
import OAI.RepresentationTheory.Weil.Local.SquareIndexTools

/-! # Norm Square Kernels -/

namespace OAI.RepresentationTheory.Weil.Local.NormSquareKernels.Construction

noncomputable section

/-! Both compact one-dimensional groups have exactly two elements killed by squaring. -/

theorem normUnit_square_kernel_card
    {k : Type*} [NormedField k] [CharZero k] :
    Nat.card (powMonoidHom 2 : PrincipalSquareClasses.Construction.normUnitSubgroup k →* PrincipalSquareClasses.Construction.normUnitSubgroup k).ker = 2 := by
  let ε : PrincipalSquareClasses.Construction.normUnitSubgroup k := ⟨(-1 : kˣ), by change ‖(-1 : k)‖ = 1; simp⟩
  apply SquareIndexTools.Construction.square_kernel_card_two ε
  · intro he
    have hh : (-1 : k) = 1 := congrArg (fun u : PrincipalSquareClasses.Construction.normUnitSubgroup k => u.val.val) he
    norm_num at hh
  · intro x
    constructor
    · intro hx
      have hs : x.val.val ^ 2 = 1 := congrArg (fun u : PrincipalSquareClasses.Construction.normUnitSubgroup k => u.val.val) hx
      rcases sq_eq_one_iff.mp hs with hs | hs
      · left; apply Subtype.ext; exact Units.ext hs
      · right; apply Subtype.ext; exact Units.ext hs
    · rintro (rfl | rfl)
      · exact one_pow 2
      · apply Subtype.ext
        apply Units.ext
        change (-1 : k) ^ 2 = 1
        ring

theorem normOne_square_kernel_card
    {k : Type*} [Field k] [CharZero k] :
    Nat.card (powMonoidHom 2 : QuadraticNormAt.Construction.QuadraticNormOne k →* QuadraticNormAt.Construction.QuadraticNormOne k).ker = 2 := by
  apply SquareIndexTools.Construction.square_kernel_card_two QuadraticNormAt.Construction.QuadraticNormOne.minusOne
  · intro he
    have hh : (-1 : k) = 1 := congrArg (fun p : QuadraticNormAt.Construction.QuadraticNormOne k => p.val.1) he
    norm_num at hh
  · exact QuadraticNormAt.Construction.QuadraticNormOne.sq_eq_one_iff

end

end OAI.RepresentationTheory.Weil.Local.NormSquareKernels.Construction
