import OAI.AlgebraicGeometry.AbelianScheme.TateComparison.ComplexHeckeBaseChange
import OAI.AlgebraicGeometry.AbelianScheme.TateComparison.TransportDifferences
import OAI.AlgebraicGeometry.AbelianScheme.TateComparison.GeometricPointEndExt

/-! # Complex Hecke Point Independence -/

namespace OAI.AlgebraicGeometry.AbelianScheme.TateComparison

noncomputable section

/-! The complex Hecke endomorphism gives the same geometric point action
for every compatible map from the test field to the complex base. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj

variable {E K : Type} [Field E] [NumberField E] [NumberField.IsCMField E]
  [Field K] [NumberField K] {s q : ℕ} [Fact q.Prime]
  (D : Data.SphericalPELAlbaneseData E K s q) (hg : D.HasIntegralModelGeometry)

local instance Data.SphericalPELAlbaneseData.ComplexHeckePointIndependence_local1 : GrpObj D.albaneseGroup.X := D.albaneseGroup.grp
local instance Data.SphericalPELAlbaneseData.ComplexHeckePointIndependence_local2 : IsCommMonObj D.albaneseGroup.X := D.albaneseGroup.comm
local instance Data.SphericalPELAlbaneseData.ComplexHeckePointIndependence_local3 : GrpObj D.complexAlbanese.X := D.complexAlbanese.grp
local instance Data.SphericalPELAlbaneseData.ComplexHeckePointIndependence_local4 : IsCommMonObj D.complexAlbanese.X := D.complexAlbanese.comm

def Data.SphericalPELAlbaneseData.complexHeckePointEnd (t : Local.IntegralType s) {T : Scheme}
    (b : T ⟶ Spec (.of K)) (c : T ⟶ Foundations.Scheme.ProjectiveSpace.complexBase) (hc : c ≫ D.complexGenericPoint = b) :
    Additive (Over.mk b ⟶ D.albaneseGroup.X) →+ Additive (Over.mk b ⟶ D.albaneseGroup.X) :=
  FieldPointTransport.pointBaseChangeEnd D.complexGenericPoint c b hc D.albaneseGroup.X
    (End.endSchemeMap D.complexAlbanese.X (D.complexHeckeEnd hg t))

theorem Data.SphericalPELAlbaneseData.complexHeckePointEnd_differences (t : Local.IntegralType s) {T : Scheme}
    (b : T ⟶ Spec (.of K)) (c : T ⟶ Foundations.Scheme.ProjectiveSpace.complexBase) (hc : c ≫ D.complexGenericPoint = b)
    (j : Fin D.componentCount) (x y : Over.mk b ⟶ D.componentGeneric j) :
    D.complexHeckePointEnd hg t b c hc (D.aPoint hg j x - D.aPoint hg j y) =
      Additive.ofMul ((x ≫ D.componentInclusion j ≫ D.albaneseTrace hg t) /
        (y ≫ D.componentInclusion j ≫ D.albaneseTrace hg t)) := by
  change FieldPointTransport.pointBaseChangeEnd D.complexGenericPoint c b hc D.albaneseGroup.X
    (End.endSchemeMap D.complexAlbanese.X (D.complexHeckeEnd hg t))
      (Additive.ofMul (((x ≫ D.componentInclusion j) ≫ D.albaneseMap hg) /
        ((y ≫ D.componentInclusion j) ≫ D.albaneseMap hg))) = _
  simpa only [Category.assoc] using
    TransportDifferences.pointBaseChangeEnd_differences D.complexGenericPoint c b hc
      D.albaneseGroup.X (D.componentGeneric j)
      (End.endSchemeMap D.complexAlbanese.X (D.complexHeckeEnd hg t))
      (D.componentInclusion j ≫ D.albaneseMap hg)
      (D.componentInclusion j ≫ D.albaneseTrace hg t)
      (D.complexHeckeEnd_baseChange_differences hg t j) x y

theorem Data.SphericalPELAlbaneseData.complexHeckePointEnd_independent (t : Local.IntegralType s)
    {Ω : Type} [Field Ω] [IsAlgClosed Ω]
    (b : Spec (.of Ω) ⟶ Spec (.of K)) (c d : Spec (.of Ω) ⟶ Foundations.Scheme.ProjectiveSpace.complexBase)
    (hc : c ≫ D.complexGenericPoint = b) (hd : d ≫ D.complexGenericPoint = b) :
    D.complexHeckePointEnd hg t b c hc = D.complexHeckePointEnd hg t b d hd := by
  apply D.geometricPointEnd_ext hg b
  intro j x y
  rw [D.complexHeckePointEnd_differences hg, D.complexHeckePointEnd_differences hg]

end

end OAI.AlgebraicGeometry.AbelianScheme.TateComparison
