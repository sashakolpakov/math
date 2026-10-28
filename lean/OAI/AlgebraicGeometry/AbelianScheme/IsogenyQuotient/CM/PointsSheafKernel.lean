import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Torsion.SheafActions
import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.CM.PointsPerfectKernel

/-! # Points Sheaf Kernel -/

namespace OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.CM.PointsSheafKernel.Construction

noncomputable section

/-!
Use the actual CartierDuality torsion pairing directly in the CMPoints quotient-kernel
construction. The native scheme pairing and its action adjoints are
constructed through the canonical torsion-sheaf comparison.
-/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj

universe u v

def integralTorsionSheafAction {O : Type v} [CommRing O] {S : Scheme.{u}} {d : ℕ}
    (A : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme d S) (σ : AbelianModuli.ReferenceFamily.ActionData.IntegralAction O A) (n : ℕ) (a : O) :
    CartierDuality.TorsionSheaves.Construction.Schemes.torsionFppfAb (CartierDuality.CommutativeSheavesAb.Construction.Schemes.representedFppfAb S (Grp.mk A.scheme)) n ⟶
      CartierDuality.TorsionSheaves.Construction.Schemes.torsionFppfAb (CartierDuality.CommutativeSheavesAb.Construction.Schemes.representedFppfAb S (Grp.mk A.scheme)) n :=
  CartierDuality.SheafTorsionMaps.Construction.Schemes.torsionSheafMap (CartierDuality.RepresentedMorphisms.Construction.Schemes.representedFppfAbMap
    (@Grp.homMk (Over S) _ _ (Grp.mk A.scheme) (Grp.mk A.scheme) (σ.map a) (σ.preservesGroup a))) n

theorem integralTorsionSheafPairing_adjoint {O : Type v} [CommRing O] {S : Scheme.{u}} {d : ℕ}
    (A : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme d S) (σ : AbelianModuli.ReferenceFamily.ActionData.IntegralAction O A) (n : ℕ)
    (e : CartierDuality.SheafEvaluation.Construction.Schemes.BilinearPairing (CartierDuality.TorsionSheaves.Construction.Schemes.torsionFppfAb (CartierDuality.CommutativeSheavesAb.Construction.Schemes.representedFppfAb S (Grp.mk A.scheme)) n)
      (CartierDuality.TorsionSheaves.Construction.Schemes.torsionFppfAb (CartierDuality.CommutativeSheavesAb.Construction.Schemes.representedFppfAb S (Grp.mk A.scheme)) n))
    (a c : O) (h : CartierDuality.SheafBlocks.Construction.Schemes.ProjectorsAdjoint e (integralTorsionSheafAction A σ n a)
      (integralTorsionSheafAction A σ n c))
    (T : Over S) (x y : T ⟶ Torsion.Groups.Construction.nativeTorsionScheme A.scheme n) :
    (Torsion.SheafPairing.Construction.torsionSheafPairingToNative (Grp.mk A.scheme) (Grp.mk A.scheme) n e).pairValue
      (x ≫ Torsion.Groups.Construction.nativeTorsionMap n (σ.map a)) y =
    (Torsion.SheafPairing.Construction.torsionSheafPairingToNative (Grp.mk A.scheme) (Grp.mk A.scheme) n e).pairValue
      x (y ≫ Torsion.Groups.Construction.nativeTorsionMap n (σ.map c)) :=
  Torsion.SheafActions.Construction.torsionSheafPairingToNative_adjoint (Grp.mk A.scheme) (Grp.mk A.scheme) n e
    (@Grp.homMk (Over S) _ _ (Grp.mk A.scheme) (Grp.mk A.scheme) (σ.map a) (σ.preservesGroup a))
    (@Grp.homMk (Over S) _ _ (Grp.mk A.scheme) (Grp.mk A.scheme) (σ.map c) (σ.preservesGroup c)) h T x y

theorem l45_torsion_sheaf_kernel_self_annihilating
    {E K : Type} [Field E] [NumberField E] [Algebra ℚ E]
    [NumberField.IsCMField E] [Field K] [NumberField K]
    {κ : K →+* ℂ} {q : ℕ} [Fact q.Prime]
    (j : PELModuli.CMPoints.Arithmetic.QadicChoice K κ q) (iota : E →+* K) (hsplit : j.HasSplitCoordinates iota)
    {k : Type} [Field k] [CharZero k] {S : Scheme} (base : S ⟶ Spec (.of k))
    {d : ℕ} (A : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme d S)
    (σ : AbelianModuli.ReferenceFamily.ActionData.IntegralAction (NumberField.RingOfIntegers E) A)
    (h s : ℕ) (labels : ChoiceKernel.Construction.KernelIndex s ≃ Gal(E/ℚ))
    (hlabels : ∀ i, labels (Sum.swap i) = PELModuli.CMPoints.Arithmetic.rationalConjugation E * labels i)
    {P : Over S} (M : Fin s → Type) [∀ i, AddCommGroup (M i)]
    [∀ i, Module (ZMod (q ^ h)) (M i)] [∀ i, Finite (M i)]
    (U : ∀ i, SubgroupFunctor.Construction.SupportedChoice A.scheme (q ^ h) (M i)
      (PointsIntrinsicFamily.Construction.l45ChosenProjectors j iota hsplit A σ h s labels i) P)
    (e : CartierDuality.SheafEvaluation.Construction.Schemes.BilinearPairing (CartierDuality.TorsionSheaves.Construction.Schemes.torsionFppfAb (CartierDuality.CommutativeSheavesAb.Construction.Schemes.representedFppfAb S (Grp.mk A.scheme)) (q ^ h))
      (CartierDuality.TorsionSheaves.Construction.Schemes.torsionFppfAb (CartierDuality.CommutativeSheavesAb.Construction.Schemes.representedFppfAb S (Grp.mk A.scheme)) (q ^ h)))
    (he : e.IsPerfect)
    (halt : ∀ (T : Over S)
      (x : (CartierDuality.TorsionSheaves.Construction.Schemes.torsionFppfAb (CartierDuality.CommutativeSheavesAb.Construction.Schemes.representedFppfAb S (Grp.mk A.scheme)) (q ^ h)).obj.obj (.op T)),
      CartierDuality.SheafEvaluation.Construction.Schemes.sheafCharacterValue (CartierDuality.TorsionSheaves.Construction.Schemes.torsionFppfAb (CartierDuality.CommutativeSheavesAb.Construction.Schemes.representedFppfAb S (Grp.mk A.scheme)) (q ^ h)) T
        (e.rightAdjoint.hom.app (.op T) x) x = 1)
    (hOE : ∀ a : NumberField.RingOfIntegers E,
      CartierDuality.SheafBlocks.Construction.Schemes.ProjectorsAdjoint e (integralTorsionSheafAction A σ (q ^ h) a)
        (integralTorsionSheafAction A σ (q ^ h) (NumberField.IsCMField.ringOfIntegersComplexConj E a))) :
    let b := Torsion.SheafPairing.Construction.torsionSheafPairingToNative (Grp.mk A.scheme) (Grp.mk A.scheme) (q ^ h) e
    let H := SubgroupTransport.Construction.relativeSubgroupPullback (Torsion.Groups.Construction.nativeTorsionInclusion A.scheme (q ^ h))
      (ChoiceKernel.Construction.choiceFullKernel (q ^ h) s M (PointsIntrinsicFamily.Construction.l45ChosenProjectors j iota hsplit A σ h s labels)
        (PointsIntrinsicFamily.Construction.l45OppositeProjectors j iota hsplit A σ h s labels)
        (PointsPerfectKernel.Construction.l45SourceBlockPairing j iota hsplit A σ h s labels b) U)
    b.relativeAnnihilator H = H := by
  apply PointsPerfectKernel.Construction.l45_choice_kernel_self_annihilating_from_perfect_source j iota hsplit A σ h s labels
    (Torsion.SheafPairing.Construction.torsionSheafPairingToNative (Grp.mk A.scheme) (Grp.mk A.scheme) (q ^ h) e) base hlabels M U
    (Torsion.SheafPairing.Construction.torsionSheafPairingToNative_isPerfect _ _ _ e he)
    (Torsion.SheafActions.Construction.torsionSheafPairingToNative_alternating _ _ e halt)
  intro a T x y
  exact integralTorsionSheafPairing_adjoint A σ (q ^ h) e a
    (NumberField.IsCMField.ringOfIntegersComplexConj E a) (hOE a) T x y

end

end OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.CM.PointsSheafKernel.Construction
