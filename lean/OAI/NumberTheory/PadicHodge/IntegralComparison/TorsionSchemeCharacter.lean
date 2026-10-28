import OAI.NumberTheory.PadicHodge.IntegralComparison.MultiplicationCoverCharacter
import OAI.AlgebraicGeometry.FormalGeometry.Completion.Geometric.IntegralConnected

/-! # Torsion Scheme Character -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.TorsionSchemeCharacter

noncomputable section

/-! Actual finite-coefficient H¹ injects additively into continuous
functions on the scheme-theoretic torsion kernel. Geometric connectedness
removes the abelian-variety coordinate from the overlap character. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
open MonoidalCategory CartesianMonoidalCategory MonObj

open OAI.AlgebraicGeometry.FormalGeometry.Completion.Geometric.IntegralConnected.Construction OAI.NumberTheory.PadicHodge.IntegralComparison.MultiplicationCoverCharacter

universe u
variable (ℓ n : ℕ) [Fact ℓ.Prime]
  {k : Type u} [Field k] [IsAlgClosed k]
  (A : Over (Spec (.of k))) [GrpObj A] [IsCommMonObj A]
  [Smooth A.hom] [IsProper A.hom] [GeometricallyIntegral A.hom]
  (hℓ : (ℓ : k) ≠ 0)

local notation "T" => OAI.AlgebraicGeometry.AbelianScheme.TorsionQuotient.SubgroupFunctor.torsionScheme A (ℓ ^ n)

def identitySection : T ⟶ A ⊗ T := lift (toUnit T ≫ η[A]) (𝟙 T)

omit [Fact (Nat.Prime ℓ)] [IsAlgClosed k] [IsCommMonObj A] [Smooth A.hom] [IsProper A.hom] [GeometricallyIntegral A.hom] in
@[reassoc (attr := simp)] theorem section_snd : identitySection ℓ n A ≫ snd A T = 𝟙 T :=
  lift_snd _ _

def character : (AlgebraicGeometry.FormalGeometry.Completion.Finite.CoefficientSheaf.Construction.finiteEllAdicCoefficient ℓ n A.left).H 1 →+ C((T).left, ZMod (ℓ ^ n)) where
  toFun x := (MultiplicationCoverCharacter.productCharacter ℓ n A hℓ x).comp
    ⟨(identitySection ℓ n A).left, (identitySection ℓ n A).left.continuous⟩
  map_zero' := by rw [map_zero]; rfl
  map_add' x y := by rw [map_add]; rfl

theorem productCharacter_value (x : (AlgebraicGeometry.FormalGeometry.Completion.Finite.CoefficientSheaf.Construction.finiteEllAdicCoefficient ℓ n A.left).H 1)
    (z : (A ⊗ T).left) :
    MultiplicationCoverCharacter.productCharacter ℓ n A hℓ x z = character ℓ n A hℓ x ((snd A T).left z) := by
  let f := (snd A T).left
  let : GeometricallyConnected f := inferInstanceAs
    (GeometricallyConnected (pullback.snd A.hom (T).hom))
  let c := MultiplicationCoverCharacter.productCharacter ℓ n A hℓ x
  have hs : f ((identitySection ℓ n A).left (f z)) = f z := by
    have he := congrArg Over.Hom.left (section_snd ℓ n A)
    exact congrArg (fun g : (T).left ⟶ (T).left => g (f z)) he
  exact ((f.isConnected_preimage_singleton (f z)).isPreconnected.image c
    c.continuous.continuousOn).subsingleton ⟨z, rfl, rfl⟩
      ⟨(identitySection ℓ n A).left (f z), hs, rfl⟩

theorem character_injective : Function.Injective (character ℓ n A hℓ) := by
  intro x y hxy
  apply MultiplicationCoverCharacter.productCharacter_injective ℓ n A hℓ
  apply ContinuousMap.ext
  intro z
  rw [productCharacter_value, productCharacter_value]
  exact congrArg (fun c : C((T).left, ZMod (ℓ ^ n)) => c ((snd A T).left z)) hxy

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.TorsionSchemeCharacter
