import OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.CMPointsAt

/-! # Higher Projector On Block -/

namespace OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.HigherProjectorOnBlock.Construction

noncomputable section

/-! A higher-level integral coefficient projector acts identically on
the same lower torsion block. This uses the original compatible residue characters. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj

variable {E K : Type} [Field E] [NumberField E] [Algebra ℚ E]
  [Field K] [NumberField K] {κ : K →+* ℂ} {q : ℕ} [Fact q.Prime]
  (j : PELModuli.CMPoints.Arithmetic.QadicChoice K κ q) (iota : E →+* K) (hsplit : j.HasSplitCoordinates iota)

theorem higherProjector_residue_self (m n : ℕ) (hmn : m ≤ n) (τ : Gal(E/ℚ)) :
    j.residueCharacter iota τ m (j.projector iota hsplit n τ) = 1 := by
  classical
  have hp : j.residueCharacter iota τ n (j.projector iota hsplit n τ) = 1 :=
    (congrFun (j.projector_coordinates iota hsplit n τ) τ).trans (Pi.single_eq_same _ _)
  have hc := congrArg (fun f : NumberField.RingOfIntegers E →+* ZMod (q ^ m) =>
    f (j.projector iota hsplit n τ)) (j.residueCharacter_compatible iota τ m n hmn)
  simpa only [RingHom.comp_apply, hp, map_one] using hc.symm

variable {S : Scheme} {g : ℕ} (A : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme g S)
  (ρ : AbelianModuli.ReferenceFamily.ActionData.IntegralAction (NumberField.RingOfIntegers E) A)

theorem levelOneBlock_fixed_by_higherProjector (n : ℕ) (τ : Gal(E/ℚ))
    (T : Over S) (a : T ⟶ (PELModuli.CMPoints.BlocksProjectors.splitBlockGroupScheme j iota hsplit A ρ 1 τ).X) :
    (a ≫ CMPointsAt.Construction.l45BlockInclusion j iota hsplit A ρ 1 τ) ≫
      ρ.map (j.projector iota hsplit (n + 1) τ) = a ≫ CMPointsAt.Construction.l45BlockInclusion j iota hsplit A ρ 1 τ := by
  have h := CMPointsAt.Construction.l45BlockInclusion_scalar j iota hsplit A ρ 1 τ
    (j.projector iota hsplit (n + 1) τ) T a
  change _ = (a ≫ CMPointsAt.Construction.l45BlockInclusion j iota hsplit A ρ 1 τ) ^
    (j.residueCharacter iota τ 1 (j.projector iota hsplit (n + 1) τ)).val at h
  rw [higherProjector_residue_self j iota hsplit 1 (n + 1) (Nat.le_add_left 1 n) τ] at h
  have ho : (1 : ZMod (q ^ 1)).val = 1 := by
    let : Fact (1 < q ^ 1) := ⟨by simpa only [pow_one] using (Fact.out : q.Prime).one_lt⟩
    exact ZMod.val_one (q ^ 1)
  simpa only [ho, pow_one] using h

end

end OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.HigherProjectorOnBlock.Construction
