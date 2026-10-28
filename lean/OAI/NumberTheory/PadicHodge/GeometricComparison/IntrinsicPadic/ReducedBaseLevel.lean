import OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.ReducedBaseCoefficientLevel
import OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.ReducedDeRhamLevelMap

/-! # Reduced Base Level -/

namespace OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.ReducedBaseLevel.IntrinsicPadicReducedBaseLevel

noncomputable section

/-! The actual Witt/p-adic integral de Rham quotient diagram isomorphism
respects the canonical level transitions. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry Opposite

private theorem square {C : Type*} [Category* C] {A B D E F G : C}
    (a : A ⟶ B) (b : B ⟶ D) (u : D ⟶ E) (s : A ⟶ F) (a' : F ⟶ G)
    (t : B ⟶ G) (b' : G ⟶ E) (h₁ : a ≫ t = s ≫ a') (h₂ : b ≫ u = t ≫ b') :
    (a ≫ b) ≫ u = s ≫ (a' ≫ b') := by
  rw [Category.assoc, h₂, ← Category.assoc, h₁, Category.assoc]

variable (p : ℕ) [Fact p.Prime] (X : Over (Spec (CommRingCat.of ℤ_[p])))
  (n m : ℕ) (hnm : n ≤ m)

local notation "W" => WittVector p (ZMod p)
local notation "IW" => fun q : ℕ => (Ideal.span {(p : WittVector p (ZMod p))}) ^ (q + 1)
local notation "IZ" => fun q : ℕ => (Ideal.span {(p : ℤ_[p])}) ^ (q + 1)
local notation "G" => ModuleCat.restrictScalars (RingEquiv.toRingHom (WittVector.equiv p))
local notation "AZ" => CategoryTheory.Functor.op (OAI.NumberTheory.PadicHodge.GeometricComparison.Affine.OpenProducts.AffineOpenProducts.inclusion X.left) ⋙
  AlgebraicGeometry.Crystalline.Cohomology.AlgebraicForms.AlgebraicDeRham.sectionAlgebras ℤ_[p] X

def targetTransition : IntegralReducedBaseIso.IntrinsicPadicIntegralReducedBaseIso.target p X m ⟶
    IntegralReducedBaseIso.IntrinsicPadicIntegralReducedBaseIso.target p X n :=
  Functor.whiskerRight
    (Functor.whiskerLeft (AZ ⋙ IntegralComparison.OrdinaryDeRhamFunctor.Ordinary.functor ℤ_[p])
      ((IntegralComparison.Module.IdealQuotientTransition.transformation ℤ_[p] (IZ m) (IZ n)
        (Ideal.pow_le_pow_right (Nat.add_le_add_right hnm 1))).mapHomologicalComplex (.up ℕ)))
    ((G).mapHomologicalComplex (.up ℕ))

theorem base_component (U : X.left.affineOpensᵒᵖ) :
    ((IntegralComparison.Module.IdealQuotient.functor W (IW m)).mapHomologicalComplex (.up ℕ)).map
      ((IntegralBaseIso.IntrinsicPadicIntegralBaseIso.iso p X).hom.app U) ≫
        IntegralComparison.Module.IdealQuotientTransition.complexMap W (IW m) (IW n)
          (Ideal.pow_le_pow_right (Nat.add_le_add_right hnm 1)) ((IntegralBaseIso.IntrinsicPadicIntegralBaseIso.target p X).obj U) =
    (ReducedDeRhamLevelMap.IntrinsicPadicReducedDeRhamLevelMap.sourceTransition p X n m hnm).app U ≫
      ((IntegralComparison.Module.IdealQuotient.functor W (IW n)).mapHomologicalComplex (.up ℕ)).map
        ((IntegralBaseIso.IntrinsicPadicIntegralBaseIso.iso p X).hom.app U) :=
  ((IntegralComparison.Module.IdealQuotientTransition.transformation W (IW m) (IW n)
    (Ideal.pow_le_pow_right (Nat.add_le_add_right hnm 1))).mapHomologicalComplex (.up ℕ)).naturality
      ((IntegralBaseIso.IntrinsicPadicIntegralBaseIso.iso p X).hom.app U)

theorem natural : (IntegralReducedBaseIso.IntrinsicPadicIntegralReducedBaseIso.iso p X m).hom ≫ targetTransition p X n m hnm =
    ReducedDeRhamLevelMap.IntrinsicPadicReducedDeRhamLevelMap.sourceTransition p X n m hnm ≫
      (IntegralReducedBaseIso.IntrinsicPadicIntegralReducedBaseIso.iso p X n).hom := by
  apply NatTrans.ext
  funext U
  exact square _ _ _ _ _ _ _ (base_component p X n m hnm U)
    (ReducedBaseCoefficientLevel.IntrinsicPadicReducedBaseComplexLevel.natural p n m hnm ((AZ ⋙ IntegralComparison.OrdinaryDeRhamFunctor.Ordinary.functor ℤ_[p]).obj U))

end

end OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.ReducedBaseLevel.IntrinsicPadicReducedBaseLevel
