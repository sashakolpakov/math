import OAI.AlgebraicGeometry.PELModuli.IntegralModel.Finite.PartitionActions
import OAI.AlgebraicGeometry.PELModuli.IntegralModel.Finite.PartitionBaseMaps
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Finite.ConstantScheme
import OAI.ArithmeticGeometry.Models.SpreadingOut.ProperCoproducts

/-! # Parameter Sum -/

namespace OAI.AlgebraicGeometry.PELModuli.IntegralModel.Finite.ParameterSum

noncomputable section

/-! Finite disjoint sums of actual action parameter schemes retain
their reducedness, finite type, quasi-compactness, and separatedness. -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

namespace FiniteBasePartition
variable {S : Scheme.{0}} {I : Type} (Z : I → Over S)

def sumParameter : Over S := Over.mk (Sigma.desc (fun i => (Z i).hom))

def sumParameterInclusion (i : I) : Z i ⟶ sumParameter Z :=
  Over.homMk (Sigma.ι (fun i => (Z i).left) i) (Sigma.ι_comp_desc (fun i => (Z i).hom) i)

def sumParameterIsColimit :
    IsColimit (Cofan.mk (sumParameter Z).left (fun i => (sumParameterInclusion Z i).left)) :=
  coproductIsCoproduct (fun i => (Z i).left)

theorem sumParameter_component (z : (sumParameter Z).left) :
    ∃ i, ∃ x : (Z i).left, (sumParameterInclusion Z i).left x = z := by
  obtain ⟨⟨i, x⟩, h⟩ := (sigmaMk (fun i => (Z i).left)).surjective z
  exact ⟨i, x, (sigmaMk_mk (fun i => (Z i).left) i x).symm.trans h⟩

instance sumParameter_reduced [∀ i, IsReduced (Z i).left] : IsReduced (sumParameter Z).left := by
  apply (IsReduced.iff_of_openCover _ (sigmaOpenCover (fun i => (Z i).left))).mpr
  intro i
  exact inferInstanceAs (IsReduced (Z i).left)

theorem sigmaMap_property (P : MorphismProperty Scheme.{0}) [IsZariskiLocalAtTarget P]
    {X Y : I → Scheme.{0}} (f : ∀ i, X i ⟶ Y i) (hf : ∀ i, P (f i)) :
    P (Limits.Sigma.map f) := by
  apply IsZariskiLocalAtTarget.of_openCover (P := P) (sigmaOpenCover Y)
  intro i
  change P (pullback.snd (Limits.Sigma.map f) (Sigma.ι Y i))
  rw [← MorphismProperty.cancel_left_of_respectsIso (P := P)
    (ArithmeticGeometry.Models.SpreadingOut.ProperCoproducts.Construction.sigma_map_component_pullback f i).flip.isoPullback.hom]
  convert hf i using 1
  exact (ArithmeticGeometry.Models.SpreadingOut.ProperCoproducts.Construction.sigma_map_component_pullback f i).flip.isoPullback_hom_snd

theorem sumParameter_factor : (sumParameter Z).hom =
    Limits.Sigma.map (fun i => (Z i).hom) ≫ (AbelianModuli.HilbertConstruction.ConstantScheme.Iff.constantScheme S I).hom := by
  apply Sigma.hom_ext
  intro i
  simp only [sumParameter, Over.mk_hom, Sigma.ι_comp_desc, Sigma.ι_map_assoc, AbelianModuli.HilbertConstruction.ConstantScheme.Iff.constantScheme_ι_hom,
    Category.comp_id]

variable [Finite I]

instance sumParameter_locallyOfFiniteType [∀ i, LocallyOfFiniteType (Z i).hom] :
    LocallyOfFiniteType (sumParameter Z).hom := by
  have : LocallyOfFiniteType (Limits.Sigma.map (fun i => (Z i).hom)) :=
    sigmaMap_property (@LocallyOfFiniteType) _ (fun _ => inferInstance)
  rw [sumParameter_factor]
  infer_instance

instance sumParameter_quasiCompact [∀ i, QuasiCompact (Z i).hom] : QuasiCompact (sumParameter Z).hom := by
  have : QuasiCompact (Limits.Sigma.map (fun i => (Z i).hom)) :=
    sigmaMap_property (@QuasiCompact) _ (fun _ => inferInstance)
  rw [sumParameter_factor]
  infer_instance

instance sumParameter_separated [∀ i, IsSeparated (Z i).hom] : IsSeparated (sumParameter Z).hom := by
  have : IsSeparated (Limits.Sigma.map (fun i => (Z i).hom)) :=
    sigmaMap_property (@IsSeparated) _ (fun _ => inferInstance)
  rw [sumParameter_factor]
  infer_instance

end FiniteBasePartition

end

end OAI.AlgebraicGeometry.PELModuli.IntegralModel.Finite.ParameterSum
