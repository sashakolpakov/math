import OAI.AlgebraicGeometry.Picard.ThetaConstruction.RelativeFiniteType
import OAI.AlgebraicGeometry.FormalGeometry.Completion.GroupSubobject

/-! # Relative Zero Group -/

namespace OAI.AlgebraicGeometry.Picard.ThetaConstruction.RelativeZeroGroup.Geometric.RelativeRigidifiedCharts

noncomputable section

/-! If the actual zero condition is closed under the group operations
on all test schemes, its represented finite-type locus is a
group scheme, including its nonreduced structure. Closedness is a separate obligation. -/

open _root_.AlgebraicGeometry _root_.CategoryTheory
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory
open scoped _root_.CategoryTheory.MonObj

open OAI.AlgebraicGeometry.FormalGeometry.Completion.GroupSubobject.Construction

variable {S : Scheme} {A B : Over S} [GrpObj A] [GrpObj B]
  (D : AbelianScheme.IsogenyQuotient.Relative.RigidifiedLine.Construction.RelativeRigidifiedProductLine A B)

structure ZeroIsSubgroup : Prop where
  one (T : Over S) : D.relativeValue (1 : T ⟶ B) = AbelianModuli.HilbertConstruction.Picard.PicardSheaf.trivialPicardClass A T
  mul {T : Over S} (a b : T ⟶ B)
    (ha : D.relativeValue a = AbelianModuli.HilbertConstruction.Picard.PicardSheaf.trivialPicardClass A T) (hb : D.relativeValue b = AbelianModuli.HilbertConstruction.Picard.PicardSheaf.trivialPicardClass A T) :
    D.relativeValue (a * b) = AbelianModuli.HilbertConstruction.Picard.PicardSheaf.trivialPicardClass A T
  inv {T : Over S} (a : T ⟶ B)
    (ha : D.relativeValue a = AbelianModuli.HilbertConstruction.Picard.PicardSheaf.trivialPicardClass A T) :
    D.relativeValue a⁻¹ = AbelianModuli.HilbertConstruction.Picard.PicardSheaf.trivialPicardClass A T

variable [IsProper A.hom] [Smooth A.hom]
  [GeometricallyConnected A.hom] [IsLocallyNoetherian B.left] (P : AbelianModuli.HilbertConstruction.Projective.ProjectivePresentations.ProjectivePresentation A)

omit [GrpObj B] in
theorem zeroInclusion_relative_zero : D.relativeValue (RelativeZeroScheme.Geometric.RelativeRigidifiedCharts.zeroInclusion D P) = AbelianModuli.HilbertConstruction.Picard.PicardSheaf.trivialPicardClass A (RelativeZeroScheme.Geometric.RelativeRigidifiedCharts.zeroSchemeOver D P) := by
  apply (RelativeZeroScheme.Geometric.RelativeRigidifiedCharts.zeroScheme_hasLift_iff D P (RelativeZeroScheme.Geometric.RelativeRigidifiedCharts.zeroInclusion D P)).mp
  exact ⟨𝟙 (RelativeZeroScheme.Geometric.RelativeRigidifiedCharts.zeroScheme D P)⟩

omit [GrpObj B] in
theorem zeroInclusion_comp_relative_zero {T : Over S} (a : T ⟶ (RelativeZeroScheme.Geometric.RelativeRigidifiedCharts.zeroSchemeOver D P)) :
    D.relativeValue (a ≫ (RelativeZeroScheme.Geometric.RelativeRigidifiedCharts.zeroInclusion D P)) = AbelianModuli.HilbertConstruction.Picard.PicardSheaf.trivialPicardClass A T := by
  rw [← D.relativeValue_natural, zeroInclusion_relative_zero D P, AbelianModuli.HilbertConstruction.Picard.PicardSheaf.trivialPicardClass_naturality]

structure ZeroGroupData where
  group : GrpObj (RelativeZeroScheme.Geometric.RelativeRigidifiedCharts.zeroSchemeOver D P)
  monHom : letI := group; IsMonHom (RelativeZeroScheme.Geometric.RelativeRigidifiedCharts.zeroInclusion D P)

def zeroGroupData (H : ZeroIsSubgroup D) : ZeroGroupData D P := by
  apply Classical.choice
  let Z := (RelativeZeroScheme.Geometric.RelativeRigidifiedCharts.zeroSchemeOver D P)
  let i := (RelativeZeroScheme.Geometric.RelativeRigidifiedCharts.zeroInclusion D P)
  have h1 : D.relativeValue (MonObj.one : 𝟙_ (Over S) ⟶ B) =
      AbelianModuli.HilbertConstruction.Picard.PicardSheaf.trivialPicardClass A (𝟙_ (Over S)) := by
    rw [MonObj.one_eq_one]
    exact H.one _
  obtain ⟨e, he⟩ := (RelativeZeroScheme.Geometric.RelativeRigidifiedCharts.zeroInclusion_factorization D P _ MonObj.one).mp h1
  have hm0 := H.mul (fst Z Z ≫ i) (snd Z Z ≫ i)
    (zeroInclusion_comp_relative_zero D P (fst Z Z)) (zeroInclusion_comp_relative_zero D P (snd Z Z))
  obtain ⟨m, hm⟩ := (RelativeZeroScheme.Geometric.RelativeRigidifiedCharts.zeroInclusion_factorization D P _ ((fst Z Z ≫ i) * (snd Z Z ≫ i))).mp hm0
  have hm' : m ≫ i = (i ⊗ₘ i) ≫ MonObj.mul := by
    simpa only [Hom.mul_def, lift_fst_comp_snd_comp] using hm
  obtain ⟨r, hr⟩ := (RelativeZeroScheme.Geometric.RelativeRigidifiedCharts.zeroInclusion_factorization D P _ i⁻¹).mp
    (H.inv i (zeroInclusion_relative_zero D P))
  have hr' : r ≫ i = i ≫ GrpObj.inv := hr
  exact ⟨⟨FormalGeometry.Completion.GroupSubobject.Construction.grpObjOfMono i e m r he hm' hr', FormalGeometry.Completion.GroupSubobject.Construction.grpObjOfMono_isMonHom i e m r he hm' hr'⟩⟩

end

end OAI.AlgebraicGeometry.Picard.ThetaConstruction.RelativeZeroGroup.Geometric.RelativeRigidifiedCharts
