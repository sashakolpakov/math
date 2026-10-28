import OAI.AlgebraicGeometry.AbelianScheme.TateComparison.SplitBlockSchemes
import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Geometric.TateChoices

/-! # Geometric Block Subgroups -/

namespace OAI.AlgebraicGeometry.AbelianScheme.TateComparison

noncomputable section

/-! Actual supported geometric subgroup choices classify typed subgroups
of the actual split Tate torsion blocks. The comparison retains their
inclusion into the original abelian scheme and uses the supplied local
characters directly. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj

variable {E K : Type} [Field E] [NumberField E] [NumberField.IsCMField E]
  [Field K] [NumberField K] {s q : ℕ} [Fact q.Prime]
  (D : Data.SphericalPELAlbaneseData E K s q) (hg : D.IsGoodCompletelySplitPrime)
  {S : Scheme} (T : Over S)
  (F : PEL.PELFamilyData (NumberField.RingOfIntegers E) (3 * s) D.level S) (n : ℕ)

def Data.SphericalPELAlbaneseData.torsionBlockPointsEquiv (v : Fin s × Bool) :
    D.torsionBlock hg T F n v ≃+ Additive ((Subgroups.splitBlock F (D.localCharacter v) n).atTest T) where
  toFun x := Additive.ofMul ⟨x.val.val.toMul, (D.torsionBlock_mem_iff hg T F n v x.val).mp x.property⟩
  invFun y := by
    let z : Add.Tate.torsion q (Additive (T ⟶ F.abelian.scheme)) n :=
      ⟨Additive.ofMul y.toMul.val, by
        apply Additive.toMul.injective
        rw [toMul_nsmul]
        exact y.toMul.property.1⟩
    exact ⟨z, (D.torsionBlock_mem_iff hg T F n v z).mpr y.toMul.property⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl

def Data.SphericalPELAlbaneseData.torsionBlockSchemePointsEquiv (v : Fin s × Bool) :
    D.torsionBlock hg T F n v ≃+ Additive (T ⟶ D.integralTorsionBlockScheme hg F n v) :=
  (D.torsionBlockPointsEquiv hg T F n v).trans
    (D.integralTorsionBlockPointsEquiv hg F n T v).symm.toAdditive

theorem Data.SphericalPELAlbaneseData.torsionBlockSchemePointsEquiv_inclusion (v : Fin s × Bool) (x : D.torsionBlock hg T F n v) :
    (D.torsionBlockSchemePointsEquiv hg T F n v x).toMul ≫
      D.integralTorsionBlockInclusion hg F n v = x.val.val.toMul :=
  congrArg Subtype.val ((D.integralTorsionBlockPointsEquiv hg F n T v).apply_symm_apply
    (D.torsionBlockPointsEquiv hg T F n v x).toMul)

variable (base : S ⟶ Spec (.of K))
  (k : Type) [Field k] [IsAlgClosed k] (b : Spec (.of k) ⟶ S)
  (M : Type) [AddCommGroup M] [Module (ZMod (q ^ n)) M] [Finite M]

def Data.SphericalPELAlbaneseData.geometricSplitBlockChoices (v : Fin s × Bool) :
    IsogenyQuotient.SubgroupFunctor.Construction.SupportedChoice F.abelian.scheme (q ^ n) M
      (D.integralProjectorMap hg F n v) (Over.mk b) ≃
      {J : AddSubgroup (D.torsionBlock hg (Over.mk b) F n v) // Nonempty (J ≃+ M)} := by
  have hgeometry := D.integralTorsionBlock_finite_etale hg F n base v
  have : IsFinite (D.integralTorsionBlockScheme hg F n v).hom := hgeometry.1
  have : Etale (D.integralTorsionBlockScheme hg F n v).hom := hgeometry.2
  exact IsogenyQuotient.Geometric.TateChoices.Construction.geometricSupportedAdditiveChoiceEquiv (q ^ n) M k b
    (D.integralProjectorMap hg F n v) (D.torsionBlockSchemePointsEquiv hg (Over.mk b) F n v)

theorem Data.SphericalPELAlbaneseData.geometricSplitBlockChoices_membership (v : Fin s × Bool)
    (H : IsogenyQuotient.SubgroupFunctor.Construction.SupportedChoice F.abelian.scheme (q ^ n) M
      (D.integralProjectorMap hg F n v) (Over.mk b))
    (x : D.torsionBlock hg (Over.mk b) F n v) :
    x ∈ (D.geometricSplitBlockChoices hg F n base k b M v H).val ↔
      x.val.val.toMul ∈ H.val.subgroup.points (Over.mk b) (𝟙 _) := by
  have hgeometry := D.integralTorsionBlock_finite_etale hg F n base v
  have : IsFinite (D.integralTorsionBlockScheme hg F n v).hom := hgeometry.1
  have : Etale (D.integralTorsionBlockScheme hg F n v).hom := hgeometry.2
  unfold Data.SphericalPELAlbaneseData.geometricSplitBlockChoices
  rw [IsogenyQuotient.Geometric.TateChoices.Construction.geometricSupportedAdditiveChoiceEquiv_membership,
    ← Data.SphericalPELAlbaneseData.integralTorsionBlockInclusion, Data.SphericalPELAlbaneseData.torsionBlockSchemePointsEquiv_inclusion]

end

end OAI.AlgebraicGeometry.AbelianScheme.TateComparison
