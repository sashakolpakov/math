import OAI.AlgebraicGeometry.FormalGeometry.Completion.PolarizationKernel.Has

/-! # Over Representation -/

namespace OAI.AlgebraicGeometry.FormalGeometry.Completion.PolarizationKernel.OverRepresentation

noncomputable section

/-! The global kernel scheme represents the same actual kernel
subfunctor in the category of schemes over the ground field. -/

set_option backward.isDefEq.respectTransparency false

open _root_.AlgebraicGeometry _root_.CategoryTheory Opposite
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory
open scoped _root_.CategoryTheory.MonObj

namespace Construction

universe u
variable {K : Type u} [Field K] [IsAlgClosed K]
  (A : Over (Spec (CommRingCat.of K))) [GrpObj A] [IsCommMonObj A]
  [IsProper A.hom] [Smooth A.hom] [GeometricallyIntegral A.hom]
  (L : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle A.left)

def polarizationKernelOver : Over (Spec (CommRingCat.of K)) := FamilyLiftFactorization.Construction.compositeFamily A (Has.Construction.polarizationKernel A L)

def polarizationKernelInclusion : polarizationKernelOver A L ⟶ A := FamilyLiftFactorization.Construction.compositeFamilyMap A (Has.Construction.polarizationKernel A L)

instance polarizationKernelInclusion_mono : Mono (polarizationKernelInclusion A L) :=
  inferInstanceAs (Mono (FamilyLiftFactorization.Construction.compositeFamilyMap A (Has.Construction.polarizationKernel A L)))

theorem polarizationKernelOver_factorization (T : Over (Spec (CommRingCat.of K))) (a : T ⟶ A) :
    (a ≫ 𝟙 A) ∈ (Functor.Construction.polarizationKernelSubfunctor A L).obj (op T) ↔
      ∃ z : T ⟶ polarizationKernelOver A L, z ≫ polarizationKernelInclusion A L = a := by
  rw [Category.comp_id]
  change Polarization.PicardMap.Construction.polarizationRelativeSection A L a = AbelianModuli.HilbertConstruction.Picard.PicardSheaf.trivialPicardClass A T ↔ _
  rw [← Has.Construction.polarizationKernel_hasLift_iff A L a]
  constructor
  · rintro ⟨p⟩
    let z := FamilyLiftFactorization.Construction.familyLiftFactorizationEquiv A (Has.Construction.polarizationKernel A L) a p
    exact ⟨z.val, z.property⟩
  · rintro ⟨z, hz⟩
    exact ⟨(FamilyLiftFactorization.Construction.familyLiftFactorizationEquiv A (Has.Construction.polarizationKernel A L) a).symm ⟨z, hz⟩⟩

def polarizationKernelPointMap :
    yoneda.obj (polarizationKernelOver A L) ⟶ (Functor.Construction.polarizationKernelSubfunctor A L).toFunctor :=
  SubfunctorChart.Construction.subfunctorChartMap (Functor.Construction.polarizationKernelSubfunctor A L) (𝟙 A) (polarizationKernelInclusion A L)
    (polarizationKernelOver_factorization A L)

instance polarizationKernelPointMap_isIso : IsIso (polarizationKernelPointMap A L) :=
  (SubfunctorChart.Construction.subfunctorChart_isPullback (Functor.Construction.polarizationKernelSubfunctor A L) (𝟙 A) (polarizationKernelInclusion A L)
    (polarizationKernelOver_factorization A L)).isIso_snd_of_isIso

def polarizationKernelPointIso :
    yoneda.obj (polarizationKernelOver A L) ≅ (Functor.Construction.polarizationKernelSubfunctor A L).toFunctor :=
  asIso (polarizationKernelPointMap A L)

end Construction

end

end OAI.AlgebraicGeometry.FormalGeometry.Completion.PolarizationKernel.OverRepresentation
