import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.RegularPair.Closed
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.StructureCechPullbackData

/-! # Pair Pullback -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.RegularPair.PairPullback

noncomputable section

/-! The original scheme section maps pull back regular pair cocycles
on the literal inverse-image cover, retaining the triple equation. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace

variable {X Y : Scheme.{0}} (f : X ⟶ Y)

theorem regularSectionPullback_restrict {U V : Y.Opens} (h : V ≤ U) (s : Γ(Y, U)) :
    f.app V (Y.presheaf.map (homOfLE h).op s) =
      X.presheaf.map (homOfLE (show f ⁻¹ᵁ V ≤ f ⁻¹ᵁ U from fun _ hx => h hx)).op (f.app U s) :=
  ConcreteCategory.congr_hom (f.naturality (homOfLE h).op) s

variable {I : Type} (U : I → Y.Opens) (v : ∀ i j : I, Γ(Y, U i ⊓ U j))

def regularPairPullback (i j : I) : Γ(X, (f ⁻¹ᵁ U i) ⊓ (f ⁻¹ᵁ U j)) :=
  f.app (U i ⊓ U j) (v i j)

theorem regularPairPullback_cocycle (hv : Closed.RegularPairCocycle Y U v) :
    Closed.RegularPairCocycle X (fun i => f ⁻¹ᵁ U i) (regularPairPullback f U v) := by
  intro i j l
  let W := (U i ⊓ U j) ⊓ U l
  have h₁ : W ≤ U i ⊓ U j := inf_le_left
  have h₂ : W ≤ U j ⊓ U l := le_inf (inf_le_left.trans inf_le_right) inf_le_right
  have h₃ : W ≤ U i ⊓ U l := le_inf (inf_le_left.trans inf_le_left) inf_le_right
  have h := congrArg (f.app W) (hv i j l)
  rw [map_add] at h
  exact (congrArg₂ (· + ·) (regularSectionPullback_restrict f h₁ (v i j)).symm
    (regularSectionPullback_restrict f h₂ (v j l)).symm).trans
      (h.trans (regularSectionPullback_restrict f h₃ (v i l)))

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.RegularPair.PairPullback
