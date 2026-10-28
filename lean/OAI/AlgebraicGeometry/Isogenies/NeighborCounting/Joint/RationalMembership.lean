import OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Joint.CoordinateMembership
import OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Evaluated.ActiveChoiceImage
import OAI.AlgebraicGeometry.Isogenies.NeighborCounting.EtaleMembershipDescent

/-! # Rational Membership -/

namespace OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Joint.RationalMembership

noncomputable section

/-! Descend the original coordinate-membership calculation from the
specified geometric extension to the actual common evaluation field. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj

open OAI.AlgebraicGeometry.Isogenies.NeighborCounting.HeckeExponents OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Intrinsic.HeckeEvaluation
open OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Intrinsic.ChoiceFunctor OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Reference.ParameterSubspaces OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Intrinsic.ActiveSubspaces
open OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Joint.CoordinateSubspaces OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Joint.CoordinateMembership OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Evaluated.ActiveChoiceImage.Prime

variable {E K : Type} [Field E] [NumberField E] [Algebra ℚ E]
  [Field K] [NumberField K] {κ : K →+* ℂ} {q : ℕ} [Fact q.Prime]
  (j : PELModuli.CMPoints.Arithmetic.QadicChoice K κ q) (iota : E →+* K) (hsplit : j.HasSplitCoordinates iota)
  {L : Type} [Field L] [CharZero L] {g s : ℕ} (A : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme g (Spec (.of L)))
  (ρ : AbelianModuli.ReferenceFamily.ActionData.IntegralAction (NumberField.RingOfIntegers E) A)
  (c : Fin s → Bool) (p : Fin 3 → Fin (s + 1) → (A.scheme ⟶ A.scheme))
  [∀ i v, IsMonHom (p i v)] (hTorsionQuotient : AbelianScheme.IsogenyQuotient.Unit.Construction.TorsionQuotientInput)
  (d : IntrinsicEvaluation.Lifts.JointFiniteEvaluationField L (Intrinsic.HeckeEvaluation.neighborEvaluationSchemes A q 0 (Fin.cases false c) p hTorsionQuotient))
  (i : Fin 3) (k : Type) [Field k] [IsAlgClosed k] (φ : d.carrier →+* k)
  (τ : Gal(E/ℚ)) (hp : p i 0 = ρ.map (j.projector iota hsplit (HeckeExponents.neighborLevel i) τ))
  (coordinates : ∀ v : Fin s,
    Additive ((d.family (some i)).extendedParameterBase k φ ⟶
      AbelianScheme.IsogenyQuotient.OppositeKernel.Construction.torsionBlock (q ^ HeckeExponents.neighborLevel i) (p i v.succ)) ≃+ (Fin 3 → ZMod (q ^ HeckeExponents.neighborLevel i)))

local instance : NeZero q := ⟨(Fact.out : q.Prime).ne_zero⟩

local instance neighborModule (v : Fin (s + 1)) :
    Module (ZMod (q ^ HeckeExponents.neighborLevel i))
      (AbelianScheme.IsogenyQuotient.ElementaryModules.Construction.RankThreeElementaryModule.{0} q (HeckeExponents.neighborExponents 0 (Fin.cases false c) i v)) :=
  AbelianScheme.IsogenyQuotient.ElementaryModules.Construction.rankThreeElementaryModule_structure q (HeckeExponents.neighborLevel i)
    (HeckeExponents.neighborExponents 0 (Fin.cases false c) i v)
    (HeckeExponents.neighborExponents_bound 0 (Fin.cases false c) i v)

variable
  (linearCoordinates : Additive (Over.mk (Spec.map (CommRingCat.ofHom (algebraMap L d.carrier))) ⟶
    AbelianScheme.IsogenyQuotient.OppositeKernel.Construction.torsionBlock q (ρ.map (j.projector iota hsplit 1 τ))) ≃ₗ[ZMod q] ((Fin 2 → ZMod q) × ZMod q))
  (a : ULift (Fin (d.count (some i))))
  (z : Additive (Over.mk (Spec.map (CommRingCat.ofHom (algebraMap L d.carrier))) ⟶
    AbelianScheme.IsogenyQuotient.OppositeKernel.Construction.torsionBlock q (ρ.map (j.projector iota hsplit 1 τ))))

theorem jointCoordinateSubspaceEquiv_rational_membership :
    linearCoordinates z ∈
      (CoordinateSubspaces.jointCoordinateSubspaceEquiv j iota hsplit A ρ c p hTorsionQuotient d i k φ τ hp coordinates linearCoordinates a).val ↔
    z.toMul ∈ (Evaluated.ActiveChoiceImage.Prime.evaluatedPrimeActiveSubgroup j iota hsplit A ρ c p hTorsionQuotient d i τ a).points
      (Over.mk (Spec.map (CommRingCat.ofHom (algebraMap L d.carrier)))) (𝟙 _) := by
  have hg := AbelianScheme.IsogenyQuotient.OppositeKernel.Construction.torsionBlock_finite_etale q (ρ.map (j.projector iota hsplit 1 τ))
    (AbelianScheme.IsogenyQuotient.Kernel.Assembly.Construction.torsion_finite_etale_from_TorsionQuotient (A := A.scheme) (𝟙 (Spec (.of L))) q
      (Fact.out : q.Prime).pos hTorsionQuotient)
  let : IsFinite (AbelianScheme.IsogenyQuotient.OppositeKernel.Construction.torsionBlock q (ρ.map (j.projector iota hsplit 1 τ))).hom := hg.1
  let : Etale (AbelianScheme.IsogenyQuotient.OppositeKernel.Construction.torsionBlock q (ρ.map (j.projector iota hsplit 1 τ))).hom := hg.2
  have : Nonempty ((d.family (some i)).extendedParameterBase k φ).left :=
    inferInstanceAs (Nonempty (Spec (.of k)))
  have : Subsingleton (Over.mk
      (Spec.map (CommRingCat.ofHom (algebraMap L (d.family (some i)).carrier)))).left :=
    inferInstanceAs (Subsingleton (Spec (.of d.carrier)))
  have : Surjective ((d.family (some i)).parameterExtensionMap k φ).left :=
    ⟨Function.surjective_to_subsingleton _⟩
  have h₁ := CoordinateMembership.jointCoordinateSubspaceEquiv_membership j iota hsplit A ρ c p hTorsionQuotient d i k φ τ hp
    coordinates linearCoordinates a z
  have h₂ := EtaleMembershipDescent.membership_iff_surjective
    (Evaluated.ActiveChoiceImage.Prime.evaluatedPrimeActiveSubgroupModel j iota hsplit A ρ c p hTorsionQuotient d i τ hp a)
    ((d.family (some i)).parameterExtensionMap k φ) (𝟙 _) z.toMul
  change z.toMul ≫ AbelianScheme.IsogenyQuotient.OppositeKernel.Construction.torsionBlockInclusion q (ρ.map (j.projector iota hsplit 1 τ)) ∈
      (Evaluated.ActiveChoiceImage.Prime.evaluatedPrimeActiveChoice A c p hTorsionQuotient d i a).val.subgroup.points _ (𝟙 _) ↔
    (((d.family (some i)).parameterExtensionMap k φ) ≫ z.toMul) ≫
        AbelianScheme.IsogenyQuotient.OppositeKernel.Construction.torsionBlockInclusion q (ρ.map (j.projector iota hsplit 1 τ)) ∈
      (Evaluated.ActiveChoiceImage.Prime.evaluatedPrimeActiveChoice A c p hTorsionQuotient d i a).val.subgroup.points _
        (((d.family (some i)).parameterExtensionMap k φ) ≫ 𝟙 _) at h₂
  erw [Category.comp_id, Category.assoc] at h₂
  exact h₁.trans h₂.symm

end

end OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Joint.RationalMembership
