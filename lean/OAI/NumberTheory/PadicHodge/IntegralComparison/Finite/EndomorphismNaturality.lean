import OAI.NumberTheory.PadicHodge.IntegralComparison.Finite.PullbackCharacter
import OAI.NumberTheory.PadicHodge.IntegralComparison.Endomorphism.CoverSquares

/-! # Endomorphism Naturality -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Finite.EndomorphismNaturality

noncomputable section

/-! The actual finite-coefficient H¹ pairing with torsion points is natural
for every algebraic group endomorphism. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry Opposite
open MonoidalCategory CartesianMonoidalCategory MonObj

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

open OAI.NumberTheory.PadicHodge.IntegralComparison.MultiplicationCoverCharacter OAI.NumberTheory.PadicHodge.IntegralComparison.Endomorphism.CoverSquares

universe u
variable (ℓ n : ℕ) [Fact ℓ.Prime]
  {k : Type u} [Field k] [IsAlgClosed k]
  (A : Over (Spec (.of k))) [GrpObj A] [IsCommMonObj A]
  [Smooth A.hom] [IsProper A.hom] [GeometricallyIntegral A.hom]
  (hℓ : (ℓ : k) ≠ 0) (e : AlgebraicGeometry.FormalGeometry.Completion.Endomorphisms.Construction.AlgebraicEnd A)

local notation "N" => ℓ ^ n
local notation "U" => OAI.NumberTheory.PadicHodge.IntegralComparison.MultiplicationCoverCharacter.cover ℓ n A hℓ
local notation "D" => OAI.NumberTheory.PadicHodge.IntegralComparison.MultiplicationCoverCharacter.overlap ℓ n A hℓ
local notation "m" => ((𝟙 A : A ⟶ A) ^ N)
local notation "E" => e.toMul.hom.hom

theorem overlap_pullback (x : (AlgebraicGeometry.FormalGeometry.Completion.Finite.CoefficientSheaf.Construction.finiteEllAdicCoefficient ℓ n A.left).H 1) :
    MultiplicationCoverCharacter.character ℓ n A hℓ (AlgebraicGeometry.FormalGeometry.Completion.Finite.CoefficientPullback.Construction.finiteEllAdicPullback ℓ n (E).left 1 x) =
      (AlgebraicGeometry.FormalGeometry.Completion.Finite.CoefficientPullback.Construction.proEtFiniteCoefficientPullback ℓ n (E).left).hom.app (op D)
        (ProEtalePullbackSections.sectionMap (E).left (AlgebraicGeometry.FormalGeometry.Completion.Finite.CoefficientSheaf.Construction.finiteEllAdicCoefficient ℓ n A.left)
          (Endomorphism.CoverSquares.overlapMap ℓ n A hℓ e) (MultiplicationCoverCharacter.character ℓ n A hℓ x)) := by
  let : IsIntegral A.left := GeometricallyIntegral.isIntegral_of_subsingleton A.hom
  let : PreconnectedSpace (U).left := inferInstanceAs (PreconnectedSpace A.left)
  exact PullbackCharacter.character_pullback ℓ n (E).left
    U D (MultiplicationCoverCharacter.first ℓ n A hℓ) (MultiplicationCoverCharacter.second ℓ n A hℓ) U D (MultiplicationCoverCharacter.first ℓ n A hℓ) (MultiplicationCoverCharacter.second ℓ n A hℓ)
    (FiniteCoefficient.GroupLaw.multiplication_pow_pullback_zero ℓ n A)
    (FiniteCoefficient.GroupLaw.multiplication_pow_pullback_zero ℓ n A)
    (Endomorphism.CoverSquares.coverMap ℓ n A hℓ e) (Endomorphism.CoverSquares.overlapMap ℓ n A hℓ e)
    (Endomorphism.CoverSquares.overlapMap_first ℓ n A hℓ e) (Endomorphism.CoverSquares.overlapMap_second ℓ n A hℓ e) x

theorem pairing (x : (AlgebraicGeometry.FormalGeometry.Completion.Finite.CoefficientSheaf.Construction.finiteEllAdicCoefficient ℓ n A.left).H 1)
    (t : AlgebraicGeometry.FormalGeometry.Completion.TorsionPointAction.Construction.geometricTorsionPoints A N) :
    TorsionPointCharacter.character ℓ n A hℓ
        (AlgebraicGeometry.FormalGeometry.Completion.Finite.CoefficientPullback.Construction.finiteEllAdicPullback ℓ n (E).left 1 x) (Additive.ofMul t) =
      TorsionPointCharacter.character ℓ n A hℓ x
        (Additive.ofMul (AlgebraicGeometry.FormalGeometry.Completion.TorsionPointAction.Construction.algebraicEndTorsionPointMap A N e t)) := by
  let p := TorsionPointCharacter.pair ℓ n A hℓ (𝟙 A) (Category.id_comp m) t
  let t' := AlgebraicGeometry.FormalGeometry.Completion.TorsionPointAction.Construction.algebraicEndTorsionPointMap A N e t
  let p' := TorsionPointCharacter.pair ℓ n A hℓ (𝟙 A) (Category.id_comp m) t'
  let z := Endomorphism.CoverSquares.origin A (IsLocalRing.closedPoint k)
  have he := congrArg (fun s : (AlgebraicGeometry.FormalGeometry.Completion.Finite.CoefficientSheaf.Construction.finiteEllAdicCoefficient ℓ n A.left).obj.obj (op D) =>
    ULift.down (α := C((D).left, ZMod N)) s (p.left z))
    (overlap_pullback ℓ n A hℓ e x)
  rw [ProEtalePullbackSections.finite_coefficient] at he
  have hs := congrArg (fun g : (D).left ⟶ (D).left => g (p.left z))
    (ProEtaleCoverSquares.map_fst (E).left (Endomorphism.CoverSquares.overlapSchemeMap ℓ n A hℓ e)
      (Endomorphism.CoverSquares.overlapSchemeMap_comm ℓ n A hℓ e))
  change (pullback.fst (D).hom (E).left) ((Endomorphism.CoverSquares.overlapMap ℓ n A hℓ e).left (p.left z)) =
    Endomorphism.CoverSquares.overlapSchemeMap ℓ n A hℓ e (p.left z) at hs
  rw [hs] at he
  have hp := congrArg (fun g : Spec (.of k) ⟶ (D).left => g (IsLocalRing.closedPoint k))
    (Endomorphism.CoverSquares.origin_pair_map ℓ n A hℓ e t)
  change Endomorphism.CoverSquares.overlapSchemeMap ℓ n A hℓ e (p.left z) = p'.left z at hp
  rw [hp] at he
  have hl := TorsionPointCharacter.pair_value ℓ n A hℓ
    (AlgebraicGeometry.FormalGeometry.Completion.Finite.CoefficientPullback.Construction.finiteEllAdicPullback ℓ n (E).left 1 x) (𝟙 A) (Category.id_comp m) t z
  have hr := TorsionPointCharacter.pair_value ℓ n A hℓ x
    (𝟙 A) (Category.id_comp m) t' z
  exact hl.symm.trans (he.trans hr)

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Finite.EndomorphismNaturality
