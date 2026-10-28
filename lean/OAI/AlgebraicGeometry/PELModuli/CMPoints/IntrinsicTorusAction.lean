import OAI.AlgebraicGeometry.PELModuli.CMPoints.IntrinsicLattice

/-! # Intrinsic Torus Action -/

namespace OAI.AlgebraicGeometry.PELModuli.CMPoints.IntrinsicTorusAction

noncomputable section

/-! The actual exponential quotient comparison respects the original
algebraic integral action, including its transport through the native
projective presentation. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.AbelianUniformizationEq.Constructions.AbelianUniformization
open scoped _root_.CategoryTheory.MonObj

open OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Intrinsic.Maps.IntrinsicAlgebraicMaps

variable {E : Type} [Field E] [NumberField E] [Algebra ℚ E]
  {g : ℕ} (A : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme g Foundations.Scheme.ProjectiveSpace.complexBase)
  (P : Foundations.Scheme.SmoothProjective.ProjectivePresentation A.scheme.left A.scheme.hom)
  (ρ : AbelianModuli.ReferenceFamily.ActionData.IntegralAction (NumberField.RingOfIntegers E) A)

def nativeTorusPointsEquiv : let := IntrinsicLattice.nativeAmbientModule A P ρ
    (HodgeConjecture.DegreeTwo.Transport.Constructions.AbelianModel (AbelianModuli.ReferenceFamily.Abelian.IntrinsicAdapter.AbelianIntrinsicAdapter.native A P) ⧸ IntrinsicLattice.nativeIntegerLattice A P ρ) ≃+
      Additive (A.Points (AbelianModuli.ReferenceFamily.ConstantSectionsOn.ConstantSections.baseTest Foundations.Scheme.ProjectiveSpace.complexBase)) := by
  let := IntrinsicLattice.nativeAmbientModule A P ρ
  exact (AbelianModuli.ReferenceFamily.Intrinsic.Maps.IntrinsicAlgebraicMaps.periodAddEquiv (AbelianModuli.ReferenceFamily.Abelian.IntrinsicAdapter.AbelianIntrinsicAdapter.native A P)).trans (AbelianModuli.ReferenceFamily.Abelian.IntrinsicAdapter.AbelianIntrinsicAdapter.nativePointEquiv A P).toAdditive

omit [NumberField E] [Algebra ℚ E] in
theorem nativePeriod_action (a : NumberField.RingOfIntegers E) :
    let := IntrinsicLattice.nativeAmbientModule A P ρ
    ∀ x : HodgeConjecture.DegreeTwo.Transport.Constructions.AbelianModel (AbelianModuli.ReferenceFamily.Abelian.IntrinsicAdapter.AbelianIntrinsicAdapter.native A P) ⧸ IntrinsicLattice.nativeIntegerLattice A P ρ,
      (AbelianModuli.ReferenceFamily.Intrinsic.Maps.IntrinsicAlgebraicMaps.periodAddEquiv (AbelianModuli.ReferenceFamily.Abelian.IntrinsicAdapter.AbelianIntrinsicAdapter.native A P) (a • x)).toMul =
        (AbelianModuli.ReferenceFamily.Intrinsic.Maps.IntrinsicAlgebraicMaps.periodAddEquiv (AbelianModuli.ReferenceFamily.Abelian.IntrinsicAdapter.AbelianIntrinsicAdapter.native A P) x).toMul ≫ AbelianModuli.ReferenceFamily.Intrinsic.IntegralAction.IntrinsicIntegralAction.nativeMap A P ρ a := by
  dsimp only
  let := IntrinsicLattice.nativeAmbientModule A P ρ
  intro x
  obtain ⟨v, rfl⟩ := (IntrinsicLattice.nativeIntegerLattice A P ρ).mkQ_surjective x
  have h := congrArg (AbelianModuli.ReferenceFamily.Intrinsic.Maps.IntrinsicAlgebraicMaps.periodAddEquiv (AbelianModuli.ReferenceFamily.Abelian.IntrinsicAdapter.AbelianIntrinsicAdapter.native A P)) (AbelianModuli.ReferenceFamily.Intrinsic.Maps.IntrinsicLinearMaps.linearLift_lifts (AbelianModuli.ReferenceFamily.Intrinsic.IntegralAction.IntrinsicIntegralAction.nativeMap A P ρ a) v)
  change (AbelianModuli.ReferenceFamily.Intrinsic.Maps.IntrinsicAlgebraicMaps.periodAddEquiv (AbelianModuli.ReferenceFamily.Abelian.IntrinsicAdapter.AbelianIntrinsicAdapter.native A P)) ((AbelianModuli.ReferenceFamily.Intrinsic.Maps.IntrinsicAlgebraicMaps.periodAddEquiv (AbelianModuli.ReferenceFamily.Abelian.IntrinsicAdapter.AbelianIntrinsicAdapter.native A P)).symm
      (Additive.ofMul ((AbelianModuli.ReferenceFamily.Intrinsic.Maps.IntrinsicAlgebraicMaps.periodAddEquiv (AbelianModuli.ReferenceFamily.Abelian.IntrinsicAdapter.AbelianIntrinsicAdapter.native A P) (QuotientAddGroup.mk v)).toMul ≫ AbelianModuli.ReferenceFamily.Intrinsic.IntegralAction.IntrinsicIntegralAction.nativeMap A P ρ a))) =
    AbelianModuli.ReferenceFamily.Intrinsic.Maps.IntrinsicAlgebraicMaps.periodAddEquiv (AbelianModuli.ReferenceFamily.Abelian.IntrinsicAdapter.AbelianIntrinsicAdapter.native A P) (QuotientAddGroup.mk (AbelianModuli.ReferenceFamily.Intrinsic.IntegralAction.IntrinsicIntegralAction.linearAction A P ρ a v)) at h
  rw [(AbelianModuli.ReferenceFamily.Intrinsic.Maps.IntrinsicAlgebraicMaps.periodAddEquiv (AbelianModuli.ReferenceFamily.Abelian.IntrinsicAdapter.AbelianIntrinsicAdapter.native A P)).apply_symm_apply] at h
  exact congrArg Additive.toMul h.symm

omit [NumberField E] [Algebra ℚ E] in
theorem nativeTorusPointsEquiv_action (a : NumberField.RingOfIntegers E) :
    let := IntrinsicLattice.nativeAmbientModule A P ρ
    ∀ x : HodgeConjecture.DegreeTwo.Transport.Constructions.AbelianModel (AbelianModuli.ReferenceFamily.Abelian.IntrinsicAdapter.AbelianIntrinsicAdapter.native A P) ⧸ IntrinsicLattice.nativeIntegerLattice A P ρ,
      (nativeTorusPointsEquiv A P ρ (a • x)).toMul =
        (nativeTorusPointsEquiv A P ρ x).toMul ≫ ρ.map a := by
  dsimp only
  let := IntrinsicLattice.nativeAmbientModule A P ρ
  intro x
  change (AbelianModuli.ReferenceFamily.Intrinsic.Maps.IntrinsicAlgebraicMaps.periodAddEquiv (AbelianModuli.ReferenceFamily.Abelian.IntrinsicAdapter.AbelianIntrinsicAdapter.native A P) (a • x)).toMul ≫ (AbelianModuli.ReferenceFamily.Abelian.IntrinsicAdapter.AbelianIntrinsicAdapter.nativeOverIso A P).hom =
    ((AbelianModuli.ReferenceFamily.Intrinsic.Maps.IntrinsicAlgebraicMaps.periodAddEquiv (AbelianModuli.ReferenceFamily.Abelian.IntrinsicAdapter.AbelianIntrinsicAdapter.native A P) x).toMul ≫ (AbelianModuli.ReferenceFamily.Abelian.IntrinsicAdapter.AbelianIntrinsicAdapter.nativeOverIso A P).hom) ≫ ρ.map a
  rw [nativePeriod_action A P ρ a x]
  simp only [AbelianModuli.ReferenceFamily.Intrinsic.IntegralAction.IntrinsicIntegralAction.nativeMap, Category.assoc, Iso.inv_hom_id, Category.comp_id]

def nativeModuleTorsionEquiv (N : ℕ) : let := IntrinsicLattice.nativeAmbientModule A P ρ
    LatticeDivision.moduleTorsion (IntrinsicLattice.nativeIntegerLattice A P ρ) N ≃+
      Additive (A.torsionPoints N (AbelianModuli.ReferenceFamily.ConstantSectionsOn.ConstantSections.baseTest Foundations.Scheme.ProjectiveSpace.complexBase)) := by
  let := IntrinsicLattice.nativeAmbientModule A P ρ
  let e : LatticeDivision.moduleTorsion (IntrinsicLattice.nativeIntegerLattice A P ρ) N ≃+
      AbelianModuli.ReferenceFamily.TorsionCongruence.TorusTorsion.killedBy
        (HodgeConjecture.DegreeTwo.Transport.Constructions.AbelianModel (AbelianModuli.ReferenceFamily.Abelian.IntrinsicAdapter.AbelianIntrinsicAdapter.native A P) ⧸ (IntrinsicLattice.nativeIntegerLattice A P ρ).toAddSubgroup) N :=
    { toFun := fun x => ⟨x.val, x.property⟩
      invFun := fun x => ⟨x.val, x.property⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl
      map_add' := fun _ _ => rfl }
  exact e.trans ((AbelianModuli.ReferenceFamily.TorsionCongruence.TorusTorsion.killedByEquiv (nativeTorusPointsEquiv A P ρ) N).trans
    (AbelianModuli.ReferenceFamily.Abelian.IntrinsicAdapter.AbelianIntrinsicAdapter.torsionAddEquiv A N).symm)

omit [NumberField E] [Algebra ℚ E] in
theorem nativeModuleTorsionEquiv_action (N : ℕ) (a : NumberField.RingOfIntegers E) :
    let := IntrinsicLattice.nativeAmbientModule A P ρ
    ∀ x : LatticeDivision.moduleTorsion (IntrinsicLattice.nativeIntegerLattice A P ρ) N,
      (nativeModuleTorsionEquiv A P ρ N (a • x)).toMul.val =
        (nativeModuleTorsionEquiv A P ρ N x).toMul.val ≫ ρ.map a := by
  dsimp only
  let := IntrinsicLattice.nativeAmbientModule A P ρ
  intro x
  exact nativeTorusPointsEquiv_action A P ρ a x.val

def nativeTorsionFixedEquiv (N : ℕ) (a : NumberField.RingOfIntegers E) :
    let := IntrinsicLattice.nativeAmbientModule A P ρ
    {x : LatticeDivision.moduleTorsion (IntrinsicLattice.nativeIntegerLattice A P ρ) N // a • x = x} ≃
      {x : A.torsionPoints N (AbelianModuli.ReferenceFamily.ConstantSectionsOn.ConstantSections.baseTest Foundations.Scheme.ProjectiveSpace.complexBase) // x.val ≫ ρ.map a = x.val} := by
  let := IntrinsicLattice.nativeAmbientModule A P ρ
  let e := (nativeModuleTorsionEquiv A P ρ N).toEquiv.trans Additive.toMul
  apply e.subtypeEquiv
  intro x
  change a • x = x ↔
    (nativeModuleTorsionEquiv A P ρ N x).toMul.val ≫ ρ.map a =
      (nativeModuleTorsionEquiv A P ρ N x).toMul.val
  rw [← nativeModuleTorsionEquiv_action A P ρ N a x]
  constructor
  · intro h
    exact congrArg (fun y => (nativeModuleTorsionEquiv A P ρ N y).toMul.val) h
  · intro h
    exact e.injective (Subtype.ext h)

end

end OAI.AlgebraicGeometry.PELModuli.CMPoints.IntrinsicTorusAction
