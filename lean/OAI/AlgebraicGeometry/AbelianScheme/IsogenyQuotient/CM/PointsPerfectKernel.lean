import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Relative.PerfectChoiceKernel
import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.CM.PointsChoiceIsotropy
import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.ProjectorAdjoints

/-! # Points Perfect Kernel -/

namespace OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.CM.PointsPerfectKernel.Construction

noncomputable section

/-!
The actual CMPoints projectors discharge completeness and orthogonality.
The integral-action adjoint equation gives the conjugate projector
adjoints, so the exact quotient kernel is self-annihilating for a perfect
alternating source pairing without per-block duality assumptions.
-/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj BigOperators

variable {E K : Type} [Field E] [NumberField E] [Algebra ℚ E]
  [NumberField.IsCMField E] [Field K] [NumberField K]
  {κ : K →+* ℂ} {q : ℕ} [Fact q.Prime]
  (j : PELModuli.CMPoints.Arithmetic.QadicChoice K κ q) (iota : E →+* K) (hsplit : j.HasSplitCoordinates iota)
  {S : Scheme} {d : ℕ} (A : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme d S)
  (σ : AbelianModuli.ReferenceFamily.ActionData.IntegralAction (NumberField.RingOfIntegers E) A)
  (h s : ℕ) (labels : ChoiceKernel.Construction.KernelIndex s ≃ Gal(E/ℚ))
  (b : Annihilator.Construction.SchemeBicharacter (A := Torsion.Groups.Construction.nativeTorsionScheme A.scheme (q ^ h))
    (B := Torsion.Groups.Construction.nativeTorsionScheme A.scheme (q ^ h)) (W := (CartierDuality.CharacterSheaf.Construction.Schemes.multiplicativeGroupOver S).X))

def l45SourceBlockPairing (i : Fin s) :
    Annihilator.Construction.SchemeBicharacter
      (A := OppositeKernel.Construction.torsionBlock (q ^ h) (PointsIntrinsicFamily.Construction.l45ChosenProjectors j iota hsplit A σ h s labels i))
      (B := OppositeKernel.Construction.torsionBlock (q ^ h) (PointsIntrinsicFamily.Construction.l45OppositeProjectors j iota hsplit A σ h s labels i))
      (W := (CartierDuality.CharacterSheaf.Construction.Schemes.multiplicativeGroupOver S).X) :=
  b.restrict
    (BlockGroups.Construction.fixedPointInclusion (Torsion.Groups.Construction.nativeTorsionMap (q ^ h) (PointsIntrinsicFamily.Construction.l45ChosenProjectors j iota hsplit A σ h s labels i)))
    (BlockGroups.Construction.fixedPointInclusion (Torsion.Groups.Construction.nativeTorsionMap (q ^ h) (PointsIntrinsicFamily.Construction.l45OppositeProjectors j iota hsplit A σ h s labels i)))

theorem l45_choice_projectors_adjoint
    (hlabels : ∀ i, labels (Sum.swap i) = PELModuli.CMPoints.Arithmetic.rationalConjugation E * labels i)
    (hOE : ∀ (a : NumberField.RingOfIntegers E) (X : Over S)
      (x y : X ⟶ Torsion.Groups.Construction.nativeTorsionScheme A.scheme (q ^ h)),
      b.pairValue (x ≫ Torsion.Groups.Construction.nativeTorsionMap (q ^ h) (σ.map a)) y =
        b.pairValue x (y ≫ Torsion.Groups.Construction.nativeTorsionMap (q ^ h)
          (σ.map (NumberField.IsCMField.ringOfIntegersComplexConj E a))))
    (i : ChoiceKernel.Construction.KernelIndex s) (X : Over S) (x y : X ⟶ Torsion.Groups.Construction.nativeTorsionScheme A.scheme (q ^ h)) :
    b.pairValue (x ≫ ChoiceIsotropy.Construction.choiceTorsionProjector (q ^ h) s
      (PointsIntrinsicFamily.Construction.l45ChosenProjectors j iota hsplit A σ h s labels)
      (PointsIntrinsicFamily.Construction.l45OppositeProjectors j iota hsplit A σ h s labels) i) y =
    b.pairValue x (y ≫ ChoiceIsotropy.Construction.choiceTorsionProjector (q ^ h) s
      (PointsIntrinsicFamily.Construction.l45ChosenProjectors j iota hsplit A σ h s labels)
      (PointsIntrinsicFamily.Construction.l45OppositeProjectors j iota hsplit A σ h s labels) (Sum.swap i)) := by
  have hp (k : ChoiceKernel.Construction.KernelIndex s) : ChoiceIsotropy.Construction.choiceTorsionProjector (q ^ h) s
      (PointsIntrinsicFamily.Construction.l45ChosenProjectors j iota hsplit A σ h s labels)
      (PointsIntrinsicFamily.Construction.l45OppositeProjectors j iota hsplit A σ h s labels) k =
      Torsion.Groups.Construction.nativeTorsionMap (q ^ h) (σ.map (j.projector iota hsplit h (labels k))) := by
    cases k <;> rfl
  rw [hp, hp, hlabels]
  exact ProjectorAdjoints.Construction.l45_projectors_adjoint_of_integral_action j iota hsplit A σ h b hOE (labels i) X x y

theorem l45_choice_kernel_self_annihilating_from_perfect_source
    {P : Over S}
    {k : Type} [Field k] [CharZero k] (base : S ⟶ Spec (.of k))
    (hlabels : ∀ i, labels (Sum.swap i) = PELModuli.CMPoints.Arithmetic.rationalConjugation E * labels i)
    (M : Fin s → Type) [∀ i, AddCommGroup (M i)]
    [∀ i, Module (ZMod (q ^ h)) (M i)] [∀ i, Finite (M i)]
    (U : ∀ i, SubgroupFunctor.Construction.SupportedChoice A.scheme (q ^ h) (M i)
      (PointsIntrinsicFamily.Construction.l45ChosenProjectors j iota hsplit A σ h s labels i) P)
    (hb : b.toSheafPairing.IsPerfect)
    (halt : ∀ (X : Over S) (x : X ⟶ Torsion.Groups.Construction.nativeTorsionScheme A.scheme (q ^ h)), b.pairValue x x = 1)
    (hOE : ∀ (a : NumberField.RingOfIntegers E) (X : Over S)
      (x y : X ⟶ Torsion.Groups.Construction.nativeTorsionScheme A.scheme (q ^ h)),
      b.pairValue (x ≫ Torsion.Groups.Construction.nativeTorsionMap (q ^ h) (σ.map a)) y =
        b.pairValue x (y ≫ Torsion.Groups.Construction.nativeTorsionMap (q ^ h)
          (σ.map (NumberField.IsCMField.ringOfIntegersComplexConj E a)))) :
    let H := SubgroupTransport.Construction.relativeSubgroupPullback (Torsion.Groups.Construction.nativeTorsionInclusion A.scheme (q ^ h))
      (ChoiceKernel.Construction.choiceFullKernel (q ^ h) s M (PointsIntrinsicFamily.Construction.l45ChosenProjectors j iota hsplit A σ h s labels)
        (PointsIntrinsicFamily.Construction.l45OppositeProjectors j iota hsplit A σ h s labels)
        (l45SourceBlockPairing j iota hsplit A σ h s labels b) U)
    b.relativeAnnihilator H = H :=
  Relative.PerfectChoiceKernel.Construction.relativeChoiceFullKernel_self_annihilating_from_perfect_source base A (q ^ h) s
    (pow_pos (Fact.out : q.Prime).pos h) M
    (PointsIntrinsicFamily.Construction.l45ChosenProjectors j iota hsplit A σ h s labels)
    (PointsIntrinsicFamily.Construction.l45OppositeProjectors j iota hsplit A σ h s labels) U
    (PointsChoiceIsotropy.Construction.l45_choice_torsion_orthogonal j iota hsplit A σ h s labels)
    (PointsChoiceIsotropy.Construction.l45_choice_torsion_complete j iota hsplit A σ h s labels) b hb halt
    (l45_choice_projectors_adjoint j iota hsplit A σ h s labels b hlabels hOE)

end

end OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.CM.PointsPerfectKernel.Construction
