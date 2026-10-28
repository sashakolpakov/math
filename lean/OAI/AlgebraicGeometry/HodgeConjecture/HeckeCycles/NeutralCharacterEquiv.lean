import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.SplitKernelProjection
import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.NeutralCharacters

/-! # Neutral Character Equiv -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.NeutralCharacterEquiv.CM

noncomputable section

/-! Characters of a finite q-primary group in characteristic q are
exactly the characters of its connected factor. The inverse extends a
character using the constructed group-scheme projection. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj
open OAI.AlgebraicGeometry.Picard.PoincareBundle.Kernel.Scheme

open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Finite.GroupRetraction.CM OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Finite.GroupDecomposition.CM OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.NeutralCharacters.CM

universe u
variable {k : Type u} [Field k] [IsAlgClosed k]
  (A : Grp (Over (Spec (.of k)))) [IsFinite A.X.hom] [IsCommMonObj A.X]

def pointSection : AbelianScheme.FrobeniusKernel.EtaleSubgroups.Construction.etaleGroupScheme (Spec (.of k))
    (Over.mk (𝟙 (Spec (.of k))) ⟶ A.X) ⟶ A :=
  ConstantGroupMap.CM.groupMap (Spec (.of k)) (Over.mk (𝟙 (Spec (.of k))) ⟶ A.X)
    A (MonoidHom.id _)

omit [IsCommMonObj A.X] in
theorem section_split : (pointSection A).hom.hom ≫ Finite.GroupRetraction.CM.componentMap A = 𝟙 (Finite.GroupDecomposition.CM.pointGroup A).X :=
  congrArg (fun f : Finite.GroupDecomposition.CM.pointGroup A ⟶ Finite.GroupDecomposition.CM.pointGroup A => f.hom.hom) (Finite.GroupRetraction.CM.inclusion_retraction A)

def projection : A ⟶ Finite.GroupDecomposition.CM.neutralPart A :=
  SplitKernelProjection.CM.groupProjection (Finite.GroupRetraction.CM.componentMap A) (pointSection A).hom.hom (section_split A)

theorem inclusion_projection : NeutralCharacters.CM.inclusion A ≫ projection A = 𝟙 (Finite.GroupDecomposition.CM.neutralPart A) := by
  apply Grp.hom_ext
  exact SplitKernelProjection.CM.inclusion_projection (Finite.GroupRetraction.CM.componentMap A)
    (pointSection A).hom.hom (section_split A)

theorem restriction_surjective : Function.Surjective (NeutralCharacters.CM.restrict A) := by
  intro χ
  refine ⟨projection A ≫ χ, ?_⟩
  change NeutralCharacters.CM.inclusion A ≫ (projection A ≫ χ) = χ
  exact (Category.assoc _ _ _).symm.trans
    ((congrArg (· ≫ χ) (inclusion_projection A)).trans (Category.id_comp χ))

def characterEquiv (q : ℕ) [Fact q.Prime] [CharP k q] (n : ℕ)
    (hkill : ∀ p : Over.mk (𝟙 (Spec (.of k))) ⟶ A.X, p ^ (q ^ n) = 1) :
    (A ⟶ AbelianScheme.CartierDuality.CharacterSheaf.Construction.Schemes.multiplicativeGroupOver (Spec (.of k))) ≃*
      (Finite.GroupDecomposition.CM.neutralPart A ⟶ AbelianScheme.CartierDuality.CharacterSheaf.Construction.Schemes.multiplicativeGroupOver (Spec (.of k))) :=
  MulEquiv.ofBijective (NeutralCharacters.CM.restrictionHom A)
    ⟨NeutralCharacters.CM.restrict_injective A q n hkill, restriction_surjective A⟩

end

end OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.NeutralCharacterEquiv.CM
