import OAI.RepresentationTheory.Theta.Adelic.SplitAtPlace
import OAI.RepresentationTheory.Theta.Adelic.AllNonsplitAtPlace

/-! # All Places Local Splitting -/

namespace OAI.RepresentationTheory.Theta.Adelic.AllPlacesLocalSplitting

noncomputable section

/-! Construction of an exactly normalized continuous unitary-pair
splitting at every completion, with no local splitting as an input. -/

variable (F : Type) [Field F] [NumberField F] (d : F) (hd : d ≠ 0)
variable {n m : ℕ} (C : Weil.AdelicSplitting.Characters.Construction.GlobalCharacters F d n m) (v : Weil.AdelicSplitting.ArchimedeanAdeles.Construction.Places F)

theorem normalized_splitting_at_every_place (hnm : 0 < n * m)
    (H : (Matrix (Fin n) (Fin n) (Weil.AdelicSplitting.ArchimedeanAdeles.Construction.localQuadratic F d v))ˣ)
    (K : (Matrix (Fin m) (Fin m) (Weil.AdelicSplitting.ArchimedeanAdeles.Construction.localQuadratic F d v))ˣ)
    (hH : H.val.conjTranspose = H.val) (hK : K.val.conjTranspose = -K.val)
    (P : Weil.AdelicSplitting.TensorSpace.Construction.SymplecticFrame (Weil.AdelicSplitting.ArchimedeanAdeles.Construction.rationalScalar F v d) n m H.val K.val) :
    ∃ s : (Weil.AdelicSplitting.UnitaryBase.Construction.Unitary H.val × Weil.AdelicSplitting.UnitaryBase.Construction.Unitary K.val) →ₜ* Weil.AdelicSplitting.Vacuum.Construction.CoverAt F (n * m) C.ψ v,
      (∀ g, Weil.AdelicSplitting.Vacuum.Construction.projectionAt F (n * m) C.ψ v (s g) = Weil.AdelicSplitting.TensorSpace.Construction.dualPairSymplectic H.val K.val P g) ∧
      Weil.AdelicSplitting.CorrectedNormalization.Construction.CorrectedLocalNormalization F d hd n m C v H K P s := by
  by_cases hsq : IsSquare (Weil.AdelicSplitting.ArchimedeanAdeles.Construction.rationalScalar F v d)
  · exact SplitAtPlace.split_at_place F d hd C v hnm hsq H K hH hK P
  · exact AllNonsplitAtPlace.all_nonsplit_at_place F d hd C v hsq H K hH hK P

end

end OAI.RepresentationTheory.Theta.Adelic.AllPlacesLocalSplitting
