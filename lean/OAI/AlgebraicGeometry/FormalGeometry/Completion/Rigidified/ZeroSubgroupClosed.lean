import OAI.AlgebraicGeometry.FormalGeometry.Completion.Rigidified.ZeroSchemeFiniteType
import OAI.AlgebraicGeometry.FormalGeometry.Completion.GroupSubobject
import OAI.AlgebraicGeometry.FormalGeometry.Completion.GroupMonomorphismClosed

/-! # Zero Subgroup Closed -/

namespace OAI.AlgebraicGeometry.FormalGeometry.Completion.Rigidified

noncomputable section

/-! If the actual zero condition is closed under the group operations
on all test schemes, its represented finite-type locus is a closed
subgroup scheme, including its nonreduced structure. -/

set_option backward.isDefEq.respectTransparency false

open _root_.AlgebraicGeometry _root_.CategoryTheory
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory
open scoped _root_.CategoryTheory.MonObj

universe u
variable {K : Type u} [Field K] {A B : Over (Spec (.of K))} [GrpObj A] [GrpObj B]
  (D : ProductLine.Construction.RigidifiedProductLine A B)

structure ProductLine.Construction.RigidifiedProductLine.ZeroIsSubgroup : Prop where
  one (T : Over (Spec (.of K))) : D.relativeValue (1 : T ⟶ B) = AbelianModuli.HilbertConstruction.Picard.PicardSheaf.trivialPicardClass A T
  mul {T : Over (Spec (.of K))} (a b : T ⟶ B)
    (ha : D.relativeValue a = AbelianModuli.HilbertConstruction.Picard.PicardSheaf.trivialPicardClass A T) (hb : D.relativeValue b = AbelianModuli.HilbertConstruction.Picard.PicardSheaf.trivialPicardClass A T) :
    D.relativeValue (a * b) = AbelianModuli.HilbertConstruction.Picard.PicardSheaf.trivialPicardClass A T
  inv {T : Over (Spec (.of K))} (a : T ⟶ B)
    (ha : D.relativeValue a = AbelianModuli.HilbertConstruction.Picard.PicardSheaf.trivialPicardClass A T) :
    D.relativeValue a⁻¹ = AbelianModuli.HilbertConstruction.Picard.PicardSheaf.trivialPicardClass A T

variable [IsAlgClosed K] [IsCommMonObj A] [IsProper A.hom] [Smooth A.hom]
  [GeometricallyIntegral A.hom] [IsLocallyNoetherian B.left]

omit [GrpObj B] in
theorem ProductLine.Construction.RigidifiedProductLine.zeroInclusion_relative_zero : D.relativeValue D.zeroInclusion = AbelianModuli.HilbertConstruction.Picard.PicardSheaf.trivialPicardClass A D.zeroSchemeOver := by
  apply (D.zeroScheme_hasLift_iff D.zeroInclusion).mp
  exact ⟨𝟙 D.zeroScheme⟩

omit [GrpObj B] in
theorem ProductLine.Construction.RigidifiedProductLine.zeroInclusion_comp_relative_zero {T : Over (Spec (.of K))} (a : T ⟶ D.zeroSchemeOver) :
    D.relativeValue (a ≫ D.zeroInclusion) = AbelianModuli.HilbertConstruction.Picard.PicardSheaf.trivialPicardClass A T := by
  rw [← D.relativeValue_natural, D.zeroInclusion_relative_zero, AbelianModuli.HilbertConstruction.Picard.PicardSheaf.trivialPicardClass_naturality]

structure ProductLine.Construction.RigidifiedProductLine.ZeroGroupData where
  group : GrpObj D.zeroSchemeOver
  monHom : letI := group; IsMonHom D.zeroInclusion

def ProductLine.Construction.RigidifiedProductLine.zeroGroupData (H : D.ZeroIsSubgroup) : D.ZeroGroupData := by
  apply Classical.choice
  let Z := D.zeroSchemeOver
  let i := D.zeroInclusion
  have h1 : D.relativeValue (MonObj.one : 𝟙_ (Over (Spec (.of K))) ⟶ B) =
      AbelianModuli.HilbertConstruction.Picard.PicardSheaf.trivialPicardClass A (𝟙_ (Over (Spec (.of K)))) := by
    rw [MonObj.one_eq_one]
    exact H.one _
  obtain ⟨e, he⟩ := (D.zeroInclusion_factorization _ MonObj.one).mp h1
  have hm0 := H.mul (fst Z Z ≫ i) (snd Z Z ≫ i)
    (D.zeroInclusion_comp_relative_zero (fst Z Z)) (D.zeroInclusion_comp_relative_zero (snd Z Z))
  obtain ⟨m, hm⟩ := (D.zeroInclusion_factorization _ ((fst Z Z ≫ i) * (snd Z Z ≫ i))).mp hm0
  have hm' : m ≫ i = (i ⊗ₘ i) ≫ MonObj.mul := by
    simpa only [Hom.mul_def, lift_fst_comp_snd_comp] using hm
  obtain ⟨r, hr⟩ := (D.zeroInclusion_factorization _ i⁻¹).mp
    (H.inv i D.zeroInclusion_relative_zero)
  have hr' : r ≫ i = i ≫ GrpObj.inv := hr
  exact ⟨⟨GroupSubobject.Construction.grpObjOfMono i e m r he hm' hr', GroupSubobject.Construction.grpObjOfMono_isMonHom i e m r he hm' hr'⟩⟩

theorem ProductLine.Construction.RigidifiedProductLine.zeroScheme_closed [LocallyOfFiniteType B.hom] (H : D.ZeroIsSubgroup) :
    IsClosedImmersion D.zeroScheme.hom := by
  let G := D.zeroGroupData H
  let := G.group
  have : IsMonHom D.zeroInclusion := G.monHom
  exact GroupMonomorphismClosed.Construction.groupMonomorphism_isClosedImmersion D.zeroInclusion

end

end OAI.AlgebraicGeometry.FormalGeometry.Completion.Rigidified
