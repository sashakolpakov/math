import OAI.AlgebraicGeometry.AbelianScheme.TateComparison.IntegralTorsionProjectors
import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.OppositeKernel
import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Unit
import OAI.AlgebraicGeometry.AbelianScheme.TorsionQuotient.Etale

/-! # Split Block Schemes -/

namespace OAI.AlgebraicGeometry.AbelianScheme.TateComparison

noncomputable section

/-! The original split eigenblock functors are represented by actual
finite etale subgroup schemes. Their fixed-point endomorphisms come from
the integral residue representatives of the supplied completion. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj

variable {E K : Type} [Field E] [NumberField E] [NumberField.IsCMField E]
  [Field K] [NumberField K] {s q : ℕ} [Fact q.Prime]
  (D : Data.SphericalPELAlbaneseData E K s q) (hg : D.IsGoodCompletelySplitPrime)
  {S : Scheme}
  (F : PEL.PELFamilyData (NumberField.RingOfIntegers E) (3 * s) D.level S) (n : ℕ)

def Data.SphericalPELAlbaneseData.integralProjectorMap (v : Fin s × Bool) : F.abelian.scheme ⟶ F.abelian.scheme :=
  End.endSchemeMap F.abelian.scheme (F.action (D.integralResidueProjector n hg v))

instance Data.SphericalPELAlbaneseData.integralProjectorMap_isMonHom (v : Fin s × Bool) :
    IsMonHom (D.integralProjectorMap hg F n v) := by
  unfold Data.SphericalPELAlbaneseData.integralProjectorMap
  infer_instance

theorem Data.SphericalPELAlbaneseData.torsionBlock_mem_iff_integral_fixed (T : Over S) (v : Fin s × Bool)
    (x : Add.Tate.torsion q (Additive (T ⟶ F.abelian.scheme)) n) :
    x ∈ D.torsionBlock hg T F n v ↔
      TorsionAction.torsionIntegralAction T q n F (D.integralResidueProjector n hg v) x = x := by
  rw [D.integralResidueProjector_action hg T F n]
  exact ⟨fun hx => ProductActionDecomposition.ProductAction.projector_on_block _ v ⟨x, hx⟩, fun hx => ⟨x, hx⟩⟩

theorem Data.SphericalPELAlbaneseData.splitBlock_mem_iff_integral_fixed (T : Over S) (v : Fin s × Bool)
    (x : T ⟶ F.abelian.scheme) :
    x ∈ (Subgroups.splitBlock F (D.localCharacter v) n).atTest T ↔
      x ^ (q ^ n) = 1 ∧ x ≫ D.integralProjectorMap hg F n v = x := by
  have hfixed (hx : x ^ (q ^ n) = 1) :
      x ∈ (Subgroups.splitBlock F (D.localCharacter v) n).atTest T ↔
        x ≫ D.integralProjectorMap hg F n v = x := by
    let z : Add.Tate.torsion q (Additive (T ⟶ F.abelian.scheme)) n :=
      ⟨Additive.ofMul x, by apply Additive.toMul.injective; exact hx⟩
    change z.val.toMul ∈ (Subgroups.splitBlock F (D.localCharacter v) n).atTest T ↔ _
    rw [← D.torsionBlock_mem_iff hg T F n v z,
      D.torsionBlock_mem_iff_integral_fixed hg F n T v z]
    constructor
    · intro hz
      have he := congrArg (fun a : Add.Tate.torsion q (Additive (T ⟶ F.abelian.scheme)) n => a.val.toMul) hz
      rw [TorsionBlockSubgroups.torsionIntegralAction_point] at he
      exact he
    · intro hx'
      apply Subtype.ext
      apply Additive.toMul.injective
      rw [TorsionBlockSubgroups.torsionIntegralAction_point]
      exact hx'
  exact ⟨fun hx => ⟨hx.1, (hfixed hx.1).mp hx⟩, fun hx => (hfixed hx.1).mpr hx.2⟩

abbrev Data.SphericalPELAlbaneseData.integralTorsionBlockScheme (v : Fin s × Bool) : Over S :=
  IsogenyQuotient.OppositeKernel.Construction.torsionBlock (q ^ n) (D.integralProjectorMap hg F n v)

def Data.SphericalPELAlbaneseData.integralTorsionBlockInclusion (v : Fin s × Bool) :
    D.integralTorsionBlockScheme hg F n v ⟶ F.abelian.scheme :=
  IsogenyQuotient.OppositeKernel.Construction.torsionBlockInclusion (q ^ n) (D.integralProjectorMap hg F n v)

instance Data.SphericalPELAlbaneseData.integralTorsionBlockInclusion_isMonHom (v : Fin s × Bool) :
    IsMonHom (D.integralTorsionBlockInclusion hg F n v) := by
  unfold Data.SphericalPELAlbaneseData.integralTorsionBlockInclusion
  infer_instance

def Data.SphericalPELAlbaneseData.integralTorsionBlockPointsEquiv (T : Over S) (v : Fin s × Bool) :
    (T ⟶ D.integralTorsionBlockScheme hg F n v) ≃*
      (Subgroups.splitBlock F (D.localCharacter v) n).atTest T where
  toFun f := ⟨f ≫ D.integralTorsionBlockInclusion hg F n v, by
    apply (D.splitBlock_mem_iff_integral_fixed hg F n T v _).mpr
    constructor
    · rw [← MonObj.comp_pow, Data.SphericalPELAlbaneseData.integralTorsionBlockInclusion,
        IsogenyQuotient.OppositeKernel.Construction.torsionBlockInclusion_killed, MonObj.comp_one]
    · rw [Data.SphericalPELAlbaneseData.integralTorsionBlockInclusion, Category.assoc, IsogenyQuotient.OppositeKernel.Construction.torsionBlockInclusion_supported]⟩
  invFun x := IsogenyQuotient.OppositeKernel.Construction.torsionBlockLift (q ^ n) (D.integralProjectorMap hg F n v) x.val
    ((D.splitBlock_mem_iff_integral_fixed hg F n T v x.val).mp x.property).1
    ((D.splitBlock_mem_iff_integral_fixed hg F n T v x.val).mp x.property).2
  left_inv f := by
    apply (cancel_mono (IsogenyQuotient.OppositeKernel.Construction.torsionBlockInclusion (q ^ n) (D.integralProjectorMap hg F n v))).mp
    exact IsogenyQuotient.OppositeKernel.Construction.torsionBlockLift_inclusion _ _ _ _ _
  right_inv x := Subtype.ext (IsogenyQuotient.OppositeKernel.Construction.torsionBlockLift_inclusion _ _ _ _ _)
  map_mul' f g := Subtype.ext (MonObj.mul_comp f g _)

theorem Data.SphericalPELAlbaneseData.integralTorsionBlock_finite_etale (base : S ⟶ Spec (.of K)) (v : Fin s × Bool) :
    IsFinite (D.integralTorsionBlockScheme hg F n v).hom ∧
      Etale (D.integralTorsionBlockScheme hg F n v).hom :=
  IsogenyQuotient.OppositeKernel.Construction.torsionBlock_finite_etale (q ^ n) (D.integralProjectorMap hg F n v)
    (TorsionQuotient.Etale.TorsionEtale.torsion_finite_etale F.abelian.scheme (q ^ n)
      (IsogenyQuotient.Unit.Construction.positive_integer_unit_on_characteristic_zero_base base (q ^ n)
        (pow_pos (Fact.out : q.Prime).pos n)))

include hg in
theorem Data.SphericalPELAlbaneseData.splitBlock_hasFiniteEtaleModel (base : S ⟶ Spec (.of K)) (v : Fin s × Bool) :
    (Subgroups.splitBlock F (D.localCharacter v) n).HasFiniteEtaleModel := by
  have hf := D.integralTorsionBlock_finite_etale hg F n base v
  refine ⟨CommGrp.mk (D.integralTorsionBlockScheme hg F n v),
    IsogenyQuotient.OppositeKernel.Construction.torsionBlockInclusion (q ^ n) (D.integralProjectorMap hg F n v),
    inferInstance, inferInstance, hf.1, hf.2, ?_⟩
  intro T x
  constructor
  · intro hx
    exact ⟨(D.integralTorsionBlockPointsEquiv hg F n T v).symm ⟨x, hx⟩,
      congrArg Subtype.val ((D.integralTorsionBlockPointsEquiv hg F n T v).apply_symm_apply ⟨x, hx⟩)⟩
  · rintro ⟨y, rfl⟩
    exact ((D.integralTorsionBlockPointsEquiv hg F n T v) y).property

end

end OAI.AlgebraicGeometry.AbelianScheme.TateComparison
